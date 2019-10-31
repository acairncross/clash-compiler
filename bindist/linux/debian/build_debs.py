#!/usr/bin/env python3
import os
import shutil
import subprocess
import sys
import tempfile
import glob
import json
import getpass

import prepare_deps

HACKDIR = "/homedoesnotexistatbuildtime/"

OLD_STYLE_CABAL = [
    "time-compat",
    "type-equality",
    "binary-orphans"
]

HERE = os.path.abspath(os.path.dirname(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "../../.."))
CACHE_DIR = os.path.expanduser(os.path.join(HERE, "deb_cache"))


def install_debs(target_dir, package):
    debs = list(glob.glob(os.path.join(target_dir, "*.deb")))
    subprocess.run(["sudo", "dpkg", "-i"] + debs, check=True)
    return debs


def build_deb(tmpdir, package, src_dir, force=False):
    print(json.dumps(package, indent=2))
    target_dir = os.path.join(CACHE_DIR, os.path.basename(src_dir))

    if force:
        shutil.rmtree(target_dir, ignore_errors=True)
    elif os.path.exists(target_dir):
        return False, install_debs(target_dir, package)

    tmp_target = os.path.join(tmpdir, os.path.basename(src_dir))
    shutil.copytree(src_dir, tmp_target)
    os.chdir(tmp_target)

    cabal_debian_cmd = [
        "cabal-debian",
        "--native",
        "--disable-tests",
        "--dep-map", "pthread:libpthread-stubs0-dev"
    ]

    # clash-prelude work-around
    if package["pkg-name"] in {"clash-prelude", "clash-lib", "clash-ghc"}:
        # TODO: Ask Leon
        cabal_debian_cmd.append("--disable-haddock")

    # Workaround for wrong version bounds in concurrent-supply
    if package["pkg-name"] == "concurrent-supply":
      repl = "s/hashable >= 1.1 && < 1.3,/hashable,/g"
      subprocess.run(["sed", "-i", repl, "concurrent-supply.cabal"], check=True)
      
    # Build debian/
    subprocess.run(cabal_debian_cmd, check=True)

    if package["pkg-name"] in OLD_STYLE_CABAL:
        user = getpass.getuser()
        subprocess.run("sudo mkdir -p {}".format(HACKDIR).split(), check=True)
        subprocess.run("sudo chown {}:{} {}".format(user, user, HACKDIR).split(), check=True)

    try:
        subprocess.run("dpkg-buildpackage", check=True)
    finally:
        subprocess.run("sudo rm -rf {}".format(HACKDIR).split(), check=True)

    shutil.rmtree(tmp_target)
    shutil.move(tmpdir, target_dir)
    os.mkdir(tmpdir)
    return True, install_debs(target_dir, package)

def build_deps():
    # If we built a package, all packages following it need to be rebuilt.
    force_build = False
    for package, src_dir in prepare_deps.prepare_all_deps():
        with tempfile.TemporaryDirectory() as tmpdir:
            (force_build_1, debs) = build_deb(tmpdir, package, src_dir, force_build)
            force_build |= force_build_1
            yield from debs

def main():
    """
    Generate Debian packages for clash-ghc and its dependencies. List files
    separated by spaces in '$cwd/debs'. 
    """
    with open("debs", "w") as debsf:
        for dep in build_deps():
            debsf.write(dep)
            debsf.write(" ")
        
if __name__ == '__main__':
    main()
