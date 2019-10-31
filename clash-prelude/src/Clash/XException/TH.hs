{-|
Copyright  :  (C) 2019, Myrtle Software Ltd
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

module Clash.XException.TH (mkNFDataXTupleInstances) where

import           Language.Haskell.TH.Syntax
import           Clash.CPP                    (maxTupleSize)
import           Data.Either                  (isLeft)

-- Spliced in in XException, so these names should be in scope:
isXName, hasUndefinedName, deepErrorXName, rnfXName :: Name
isXName = mkName "isX"
hasUndefinedName = mkName "hasUndefined"
deepErrorXName = mkName "deepErrorX"
rnfXName = mkName "rnfX"

mkTup :: [Type] -> Type
mkTup names@(length -> n) =
  foldl AppT (TupleT n) names

-- | Creates an instance of the form:
--
--  instance (NFDataX a0, NFDataX a1) => NFDataX (a0, a1)
--
-- With /n/ number of variables.
mkNFDataXTupleInstance :: Name -> Int -> Dec
mkNFDataXTupleInstance nfdataxName n =
  InstanceD
    Nothing
    constraints
    instanceTyp
    [ ensureSpineDecl
    , hasUndefinedDecl
    , deepErrorXDecl
    , rnfXDecl
    ]
 where
  constraints = map (AppT (ConT nfdataxName)) vars
  instanceTyp = ConT nfdataxName `AppT` mkTup vars
  names = map (mkName . ('a':) . show) [0..n-1]
  vars = map VarT names

  t = mkName "t"
  s = mkName "s"

  rnfXDecl = FunD rnfXName [
    Clause
      [AsP t (TildeP (TupP (map VarP names)))]
      (NormalB (
        CondE
          (VarE 'isLeft `AppE` (VarE isXName `AppE` VarE t))
          (TupE [])
          (foldl
            (\e1 e2 -> UInfixE e1 (VarE 'seq) (VarE rnfXName `AppE` e2))
            (VarE rnfXName `AppE` VarE (head names))
            (map VarE (tail names)))
      ))
      []
    ]

  hasUndefinedDecl = FunD hasUndefinedName [
    Clause
      [AsP t (TildeP (TupP (map VarP names)))]
      (NormalB (
        CondE
          (VarE 'isLeft `AppE` (VarE isXName `AppE` VarE t))
          (ConE 'True)
          (VarE 'or `AppE` ListE
            (map ((VarE hasUndefinedName `AppE`) . VarE) names))
      ))
      []
    ]

  ensureSpineDecl = FunD (mkName "ensureSpine") [
    Clause
      [TildeP (TupP (map VarP names))]
      (NormalB (TupE (map VarE names)))
      []
    ]

  deepErrorXDecl = FunD deepErrorXName [
     Clause
       [VarP s]
       (NormalB (TupE (replicate n (VarE deepErrorXName `AppE` VarE s))))
       []
     ]


mkNFDataXTupleInstances :: Name -> Q [Dec]
mkNFDataXTupleInstances nfdataxName =
  pure (map (mkNFDataXTupleInstance nfdataxName) [2..maxTupleSize])
