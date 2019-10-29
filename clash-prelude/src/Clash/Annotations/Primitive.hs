{-|
Copyright  :  (C) 2017-2019, Myrtle Software, QBayLogic
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

Instruct the clash compiler to look for primitive HDL templates in the
indicated directory. For distribution of new packages with primitive HDL
templates.
-}

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveLift            #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module Clash.Annotations.Primitive
  ( dontTranslate
  , hasBlackBox
  , warnNonSynthesizable
  , warnAlways
  , Primitive(..)
  , PrimitiveGuard(..)
  , HDL(..)
  , extractPrim
  ) where

import           Control.DeepSeq                          (NFData)
import           Data.Binary                              (Binary)
import           Data.Data
import           Data.Hashable                            (Hashable)
import           GHC.Generics                             (Generic)
import           Language.Haskell.TH.Lift                 (Lift)


-- The commented code directly below this comment is affected by an old
-- GHC bug: https://ghc.haskell.org/trac/ghc/ticket/5463. In short, NOINLINE
-- pragmas generated by Template Haskell, get ignored. We'd still like a better
-- API than manually having to write all the guard/inline pragmas some day,
-- so I'm leaving the code in for now.

{-

guard :: TH.Exp -> TH.Name -> TH.Q [TH.Dec]
guard guardExpr fName =
  pure
    [ TH.PragmaD (TH.InlineP fName TH.NoInline TH.FunLike TH.AllPhases)
    , TH.PragmaD (TH.AnnP (TH.ValueAnnotation fName) (TH.SigE guardExpr typ))
    ]
  where
    typ = TH.AppT (TH.ConT ''PrimitiveGuard) (TH.TupleT 0)

applyUnit :: TH.Exp -> TH.Exp
applyUnit e = TH.AppE e (TH.TupE [])

-- | Mark a function as having a primitive. Clash will yield an error if it
-- needs to translate this function, but no blackbox was loaded. Usage:
--
-- @
-- $(hasBlackBox 'f)
-- @
--
-- If you don't want to use TemplateHaskell, add these annotations:
--
-- @
-- {-# NOINLINE f #-}
-- {-# ANN f (HasBlackBox ()) #-}
-- @
--
hasBlackBox :: TH.Name -> TH.Q [TH.Dec]
hasBlackBox = guard (applyUnit (TH.ConE 'HasBlackBox))

-- | Mark a function as non translatable. Clash will yield an error if
-- it needs to translate this function. Usage:
--
-- @
-- $(dontTranslate 'f)
-- @
--
-- If you don't want to use TemplateHaskell, add these annotations:
--
-- @
-- {-# NOINLINE f #-}
-- {-# ANN f DontTranslate #-}
-- @
--
dontTranslate :: TH.Name -> TH.Q [TH.Dec]
dontTranslate = guard (TH.ConE 'DontTranslate)

-- | Mark a function as non synthesizable. Clash will emit the given warning
-- if instantiated outside of a testbench context. Usage:
--
-- @
-- $(warnNonSynthesizable 'f "Tread carefully, user!")
-- @
--
-- If you don't want to use TemplateHaskell, add these annotations:
--
-- @
-- {-# NOINLINE f #-}
-- {-# ANN f (WarnNonSynthesizable "Tread carefully, user!" ()) #-}
-- @
--
warnNotSynthesizable :: TH.Name -> String -> TH.Q [TH.Dec]
warnNotSynthesizable nm warning =
  guard
    (applyUnit
      (TH.AppE
        (TH.ConE 'WarnNonSynthesizable)
        (TH.LitE (TH.StringL warning))))
    nm

-- | Emit warning when translating this value.
--
-- @
-- $(warnAlways 'f "Tread carefully, user!")
-- @
--
-- If you don't want to use TemplateHaskell, add these annotations:
--
-- @
-- {-# NOINLINE f #-}
-- {-# ANN f (WarnAlways "Tread carefully, user!" ()) #-}
-- @
--
warnAlways :: TH.Name -> String -> TH.Q [TH.Dec]
warnAlways nm warning =
  guard
    (applyUnit
      (TH.AppE
        (TH.ConE 'WarnAlways)
        (TH.LitE (TH.StringL warning))))
    nm
-}

dontTranslate :: PrimitiveGuard ()
dontTranslate = DontTranslate

hasBlackBox :: PrimitiveGuard ()
hasBlackBox = HasBlackBox ()

warnNonSynthesizable :: String -> PrimitiveGuard ()
warnNonSynthesizable s = WarnNonSynthesizable s ()

warnAlways :: String -> PrimitiveGuard ()
warnAlways s = WarnAlways s ()

data HDL
  = SystemVerilog
  | Verilog
  | VHDL
  deriving (Eq, Enum, Bounded, Show, Read, Data, Generic, NFData, Hashable, Lift)

-- | The 'Primitive' constructor instructs the clash compiler to look for primitive
-- HDL templates in the indicated directory. 'InlinePrimitive' is equivalent but
-- provides the HDL template inline. They are intended for the distribution of
-- new packages with primitive HDL templates.
--
-- === Example of 'Primitive'
--
-- You have some existing IP written in one of HDLs supported by Clash, and
-- you want to distribute some bindings so that the IP can be easily instantiated
-- from Clash.
--
-- You create a package which has a @myfancyip.cabal@ file with the following stanza:
--
-- @
-- data-files: path\/to\/MyFancyIP.json
-- cpp-options: -DCABAL
-- @
--
-- and a @MyFancyIP.hs@ module with the simulation definition and primitive.
--
-- @
-- module MyFancyIP where
--
-- import Clash.Prelude
--
-- myFancyIP :: ...
-- myFancyIP = ...
-- {\-\# NOINLINE myFancyIP \#-\}
-- @
--
-- The @NOINLINE@ pragma is needed so that GHC will never inline the definition.
--
-- Now you need to add the following imports and @ANN@ pragma:
--
-- @
-- \#ifdef CABAL
-- import           Clash.Annotations.Primitive
-- import           System.FilePath
-- import qualified Paths_myfancyip
-- import           System.IO.Unsafe
--
-- {\-\# ANN module (Primitive VHDL (unsafePerformIO Paths_myfancyip.getDataDir \<\/\> "path" \<\/\> "to")) \#-\}
-- \#endif
-- @
--
-- Add more files to the @data-files@ stanza in your @.cabal@ files and more
-- @ANN@ pragma's if you want to add more primitive templates for other HDLs
--
-- === Example of 'InlinePrimitive'
--
-- The following example shows off an inline HDL primitive template. It uses the
-- [interpolate](https://hackage.haskell.org/package/interpolate) package for
-- nicer multiline strings.
--
-- @
-- module InlinePrimitive where
--
-- import           Clash.Annotations.Primitive
-- import           Clash.Prelude
-- import           Data.String.Interpolate      (i)
-- import           Data.String.Interpolate.Util (unindent)
--
-- {\-\# ANN example (InlinePrimitive VHDL $ unindent [i|
--   [ { \"BlackBox\" :
--       { "name" : "InlinePrimitive.example"
--       , "kind": "Declaration"
--       , "template" :
--   "-- begin InlinePrimitive example:
--   ~GENSYM[example][0] : block
--   ~RESULT <= 1 + ~ARG[0];
--   end block;
--   -- end InlinePrimitive example"
--       }
--     }
--   ]
--   |]) \#-\}
-- {\-\# NOINLINE example \#-\}
-- example :: Signal System (BitVector 2) -> Signal System (BitVector 2)
-- example = fmap succ
-- @
data Primitive
  = Primitive HDL FilePath
  -- ^ Description of a primitive for a given 'HDL' in a file at 'FilePath'
  | InlinePrimitive HDL String
  -- ^ Description of a primitive for a given 'HDL' as an inline 'String'
  deriving (Show, Read, Data, Generic, NFData, Hashable)

-- | Guard primitive functions. This will help Clash generate better error
-- messages. You can annotate a function like:

-- @
-- {-# ANN f dontTranslate #-}
-- @
--
-- or
--
-- @
-- {-# ANN f hasBlackBox #-}
-- @
--
-- or
--
-- @
-- {-# ANN f (warnNonSynthesizable "Tread carefully, user!") #-}
-- @
--
-- or
--
-- @
-- {-# ANN f (warnAlways "Tread carefully, user!") #-}
-- @
data PrimitiveGuard a
  = DontTranslate
  -- ^ Marks value as not translatable. Clash will error if it finds a blackbox
  -- definition for it, or when it is forced to translate it.
  | HasBlackBox a
  -- ^ Marks a value as having a blackbox. Clash will err if it hasn't found
  -- a blackbox
  | WarnNonSynthesizable String a
  -- ^ Marks value as non-synthesizable. This will trigger a warning if
  -- instantiated in a non-testbench context. Implies @HasBlackBox@.
  | WarnAlways String a
  -- ^ Always emit warning upon instantiation. Implies @HasBlackBox@.
    deriving (Show, Read, Data, Generic, NFData, Hashable, Functor, Foldable, Traversable, Binary)

-- | Extract primitive definition from a PrimitiveGuard. Will yield Nothing
-- for guards of value 'DontTranslate'.
extractPrim
  :: PrimitiveGuard a
  -> Maybe a
extractPrim =
  \case
    HasBlackBox a            -> Just a
    WarnNonSynthesizable _ a -> Just a
    WarnAlways _ a           -> Just a
    DontTranslate            -> Nothing
