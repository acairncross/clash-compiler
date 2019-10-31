FROM ubuntu:eoan

ARG PARALLEL=-j8

ENV DEBIAN_FRONTEND noninteractive
ENV PATH /opt/ghc/bin:/opt/cabal/bin:$PATH

ARG DEPS_GHC="ghc ghc-doc ghc-prof cabal-debian cabal-install happy"
ARG DEPS_BUILD="build-essential dpkg-dev haskell-devscripts debhelper wget sudo"
ARG DEPS_CLASH="libtinfo-dev libpthread-stubs0-dev"

RUN apt update && apt install $DEPS_GHC $DEPS_BUILD $DEPS_CLASH -y
RUN mkdir -p /ghc-and-deps && cd /ghc-and-deps && apt-get download $(apt-cache depends --recurse --no-recommends --no-suggests --no-conflicts --no-breaks --no-replaces --no-enhances ghc ghc-doc ghc-prof cabal-install happy | grep "^\w" | grep -v libc6)
