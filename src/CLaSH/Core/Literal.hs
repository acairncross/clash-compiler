{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module CLaSH.Core.Literal where

import Unbound.LocallyNameless as Unbound

import {-# SOURCE #-} CLaSH.Core.Term (Term)
import CLaSH.Core.Type                (Type,intPrimTy,addrPrimTy)

data Literal
  = IntegerLiteral Integer
  | StringLiteral  String
  deriving Show

Unbound.derive [''Literal]

instance Alpha Literal

instance Subst Type Literal
instance Subst Term Literal

literalType ::
  Literal
  -> Type
literalType (IntegerLiteral _) = intPrimTy
literalType (StringLiteral  _) = addrPrimTy
