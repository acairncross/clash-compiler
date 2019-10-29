{-

If you don't want to provide a Haskell implementation to a HDL function,
you can use 'makeScaffold' to create a HDL blackbox with "stub" Haskell function.
An input datatype of 'Clock's and 'BitVector's with a smart constructor taking
associated clocks and setting the bitvectors to 0, and an output datatype will be
created. Each list of 'Port's is designated to be in a different clock domain.
The datatypes will be parametrized on these clock domains.

An example, a Xilinx IBUFDS_GTE2 primitive, with added dummy signals to show expansion:

@
makeScaffold "xilinxDiffClock" "IBUFDS_GTE2"
  -- A list of parameters
  [ PBool "CLKRCV_TRST" True
  ]

  -- A list of list of ports, corresponding to domains of signals
  -- Clocks will be lifted to the top of defitions
  [ [ ClkOut "O"
    , ClkIn "I"
    , In "dummy_signal1" 8
    , ClkIn "IB"
    ]
  , [ In "dummy_signal2" 40
    , Out "dummy_out1" 1
    ]
  ]
@

Creates a synthesizable HDL blackbox representation and these Haskell values:

@
data XilinxDiffClockI dom1 dom2
  = XilinxDiffClockI
  { _I :: Clock dom1
  , _IB :: Clock dom1
  , _dummy_signal1 :: Signal dom1 (BitVector 8)
  , _dummy_signal2 :: Signal dom2 (BitVector 40)
  }
data XilinxDiffClockO dom1 dom2
  = XilinxDiffClockI
  { _O :: Clock dom1
  , _dummy_out1 :: Signal dom2 (BitVector 1)
  }

-- Smart constructor taking only the clocks
xilinxDiffClockI arg1 arg2 = XilinxDiffClockI arg1 arg2 (pure def) (pure def)

-- Haskell name tied to HDL instantiation
xilinxDiffClock# arg1 arg2 arg3 arg4
  = XilinxDiffClockO clockGen (pure def)

-- A convenience function taking the input data type and calling the blackbox
xilinxDiffClock (XilinxDiffClockI arg1 arg2 arg3 arg4)
  = xilinxDiffClock# arg1 arg2 arg3 arg4
@

-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveLift            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}

module Clash.Primitives.Scaffold
  ( makeScaffold
  , makeScaffold'
  , Port (..)
  , Parameter(..)

  , ScaffoldDesc(..)
  , ScaffoldPort(..)
  )
  where

import           Prelude

import           Language.Haskell.TH
import           GHC.Generics                   ( Generic )
import           Data.Char                      ( toUpper)
import qualified Data.Text                     as T
import           Data.List                      ( sortOn )
import           Data.Semigroup.Monad           ( getMon )
import           Control.Monad.State            ( State )

import qualified Data.String.Interpolate       as I

import           Clash.Netlist.Id               ( IdType(Basic) )
import           Clash.Netlist.Types     hiding ( PortDirection(..) )
import           Clash.Netlist.Types            ( PortDirection )
import qualified Clash.Netlist.Types           as Netlist
import           Data.Text.Prettyprint.Doc.Extra
                                                ( Doc )
import           Clash.Annotations.Primitive
import           Clash.Backend                  ( Backend
                                                , mkUniqueIdentifier
                                                , blockDecl
                                                )

import qualified Clash.Prelude                 as C
                                         hiding ( Text )
import           Clash.Prelude                  ( Lift
                                                , def
                                                )

import           Control.Lens                   ( view
                                                , _1
                                                )

type Width = Integer

data Parameter
  = PString String String
  | PInteger String Integer
  | PBool String Bool
  deriving (Lift)

data Port
  = In String Width
  | Out String Width
  | ClkIn String
  | ClkOut String

-- *

type IsClock = Bool
type HWParameter = (Expr,HWType,Expr)

data ScaffoldPort
  = ScaffoldPort
  { direction  :: PortDirection
  , width      :: Width
  , name       :: String
  , isClock    :: IsClock
  , ty         :: Type
  , domain     :: Name
  } deriving (Show, Lift)

data ScaffoldDesc
  = ScaffoldDesc
  { functionName  :: Name
  , functionName# :: Name
  , functionNameI :: Name
  , qfunctionName :: Name

  , datatypeNameI :: Name
  , datatypeNameO :: Name

  , templateName  :: Name
  , qtemplateName :: Name

  , primitive     :: String
  } deriving (Show, Lift)

toTemplateHaskellType :: IsClock -> Width -> Name -> Type
toTemplateHaskellType True _ dom  = AppT (ConT ''C.Clock) (VarT dom)
toTemplateHaskellType False w dom =
  AppT
    (AppT (ConT ''C.Signal) (VarT dom))
    (AppT (ConT ''C.BitVector) (LitT $ NumTyLit w))

toClashParameter :: Parameter -> HWParameter
toClashParameter (PString n v) =
  (Identifier (T.pack n) Nothing, String, Literal Nothing (StringLit v))
toClashParameter (PInteger n v) =
  (Identifier (T.pack n) Nothing, Integer, Literal Nothing (NumLit v))
toClashParameter (PBool n v) =
  (Identifier (T.pack n) Nothing, Bool, Literal Nothing (BoolLit v))

toClashType :: ScaffoldPort -> HWType
toClashType (ScaffoldPort _ _ _ True _ _) = Clock (T.pack "clk")
toClashType (ScaffoldPort _ w _ False _ _) = BitVector (fromInteger w)

scaffoldPort :: Name -> Port -> ScaffoldPort
scaffoldPort d (In n w) =
  ScaffoldPort Netlist.In w n False (toTemplateHaskellType False w d) d
scaffoldPort d (Out n w) =
  ScaffoldPort Netlist.Out w n False (toTemplateHaskellType False w d) d
scaffoldPort d (ClkIn n) =
  ScaffoldPort Netlist.In 1 n True (toTemplateHaskellType True 1 d) d
scaffoldPort d (ClkOut n) =
  ScaffoldPort Netlist.Out 1 n True (toTemplateHaskellType True 1 d) d

scaffoldDomain :: [Port] -> Q (Name, [ScaffoldPort])
scaffoldDomain ps = do
  d <- newName "domain"
  return $ (d, scaffoldPort d <$> ps)

instantiate
  :: ScaffoldPort
  -> Expr
  -> (Expr, PortDirection, HWType, Expr)
instantiate p@(ScaffoldPort Netlist.In _ n _ _ _) e
  = (Identifier (T.pack n) Nothing, Netlist.In, toClashType p, e)
instantiate p@(ScaffoldPort Netlist.Out _ n _ _ _) e
  = ( Identifier (T.pack n) Nothing
    , Netlist.Out, toClashType p, e)

scaffoldTemplate
  :: Backend s
  => String
  -> [Parameter]
  -> [Name]
  -> [ScaffoldPort]
  -> [ScaffoldPort]
  -> BlackBoxContext
  -> State s Doc
scaffoldTemplate primitiveName parameters domains i o bbCtx = do
  wires <- mapM (ident . T.pack . name) o
  inst  <- ident (T.pack $ primitiveName <> "_inst")
  blk   <- ident (T.pack $ primitiveName <> "_blk")

  getMon
    $  blockDecl blk
    $  [ NetDecl Nothing o' t | (o', t) <- zip wires wiresTy ]
    <> [ InstDecl
         Comp
         Nothing
         (T.pack primitiveName)
         inst
         (toClashParameter <$> parameters)
         (  zipWith instantiate i (fmap (view _1) args)
         <> zipWith instantiate o (flip Identifier Nothing <$> wires)
         )
       , result wires (bbResult bbCtx)
       ]
 where
  args    = drop (length domains) (bbInputs bbCtx)
  ident   = mkUniqueIdentifier Basic
  wiresTy = fmap toClashType o

  result ws (Identifier r Nothing, resTy@(Product _ _ _))
    = Assignment r
    (DataCon resTy (DC (resTy, 0)) $ [ Identifier w Nothing | w <- ws ])
  result ws (Identifier r Nothing, _) | [wire] <- ws
    = Assignment r (Identifier wire Nothing)
  result _ t = error $ "scaffoldTemplate: unexpected result type"
                     ++ show t

scaffoldTF
  :: [Int]
  -> String
  -> [Parameter]
  -> [Name]
  -> [ScaffoldPort]
  -> [ScaffoldPort]
  -> TemplateFunction
scaffoldTF used primitiveName parameters domains i o = TemplateFunction
  used
  (const True)
  (scaffoldTemplate primitiveName parameters domains i o)

scaffoldAnnotation :: Name -> Name -> HDL -> Q Exp
scaffoldAnnotation n ntf hdl =
  [|InlinePrimitive hdl j|]
 where
  j = [I.i| [{ "BlackBox" :
              { "name" : "#{n}"
              , "kind": "Declaration"
              , "format": "Haskell"
              , "templateFunction" : "#{ntf}"
              }
          }]
      |]

makeDatatypes
  :: ScaffoldDesc
  -> ([TyVarBndr],[Name])
  -> ([ScaffoldPort], [Name])
  -> ([ScaffoldPort], [Name])
  -> [Dec]
makeDatatypes desc (kinds,domains) (i,ni) (o,no) =
  [ build (datatypeNameI desc) (zipWith mkRec i ni) [''Generic]
  , build (datatypeNameO desc) (zipWith mkRec o no) [''Generic]

  , SigD (functionNameI desc)
    $ ForallT kinds constraints
    $ foldr (AppT . AppT ArrowT) retTy (ty <$> iclks)
  , FunD (functionNameI desc) [Clause (VarP <$> argNames) (NormalB (
      foldl AppE
        (foldl AppE (ConE (datatypeNameI desc)) (VarE <$> argNames))
        (replicate (length i - length iclks) pd)
      )) []]
  ]
 where
  b = Bang NoSourceUnpackedness NoSourceStrictness
  drv = (:[]) . DerivClause Nothing . fmap ConT
  constraints = AppT (ConT ''C.KnownDomain) . VarT <$> domains
  iclks = filter isClock i
  argNames = zipWith (const (mkName . (<>) "clkArg" . show)) iclks [0::Int ..]
  applyDomains = flip (foldl AppT) (fmap VarT domains)
  retTy = applyDomains $ ConT $ datatypeNameI desc
  pd = (VarE 'pure) `AppE` (VarE 'def)
  mkRec (ScaffoldPort _ _ _ _ t _) n = (n, b, t)
#if MIN_VERSION_template_haskell(2,11,0)
  build nd fields derive = DataD [] nd kinds Nothing [(RecC nd fields)] (drv derive)
#else
  build nd fields derive = DataD [] nd kinds [(RecC nd fields)] (drv derive)
#endif

makeTemplate
  :: ScaffoldDesc
  -> [Parameter]
  -> [Name]
  -> [ScaffoldPort]
  -> [ScaffoldPort]
  -> DecsQ
makeTemplate desc parameters domains i o = do
  blackboxAnn <- do
    annotations <-
      traverse
        (scaffoldAnnotation (qfunctionName desc) (qtemplateName desc))
        [minBound .. maxBound]
    return $ (PragmaD . AnnP (valueAnnotation $ qfunctionName desc)) <$> annotations

  blackboxExpr <-
    [| scaffoldTF
       [length domains .. length domains + length i - 1]
       (primitive desc) parameters domains i o
    |]

  return $
    [ SigD (templateName desc) (ConT ''TemplateFunction)
    , FunD (templateName desc) [Clause [] (NormalB blackboxExpr) []]
    ] <> blackboxAnn

makeWrapper
  :: ScaffoldDesc
  -> ([TyVarBndr], [Name])
  -> ([ScaffoldPort], [Name])
  -> [ScaffoldPort]
  -> [Dec]
makeWrapper desc (kinds, domains) (i,ni) o =
  [ SigD (functionName# desc)
    $ ForallT kinds constraints
    $ foldr1 (AppT . AppT ArrowT) (fmap ty i ++ [retTy])
  , FunD (functionName# desc) [Clause bangs (NormalB ret) []]
  , PragmaD (InlineP (functionName# desc) NoInline FunLike AllPhases)
  , SigD (functionName desc)
    $ ForallT kinds constraints
    $ AppT ArrowT argTy `AppT` retTy
  , FunD (functionName desc) [Clause [TupP [VarP arg]] (NormalB (
      foldl AppE (VarE (functionName# desc))
      $ fmap (flip AppE (VarE arg) . VarE) ni
      )) []]
  , PragmaD (InlineP (functionName desc) NoInline FunLike AllPhases)
  ]
 where
  arg = (mkName "_arg")
  pd = (VarE 'pure) `AppE` (VarE 'def)
  bangs = replicate (length i) (BangP WildP)
  ret = foldl AppE (ConE (datatypeNameO desc))
          $ gen . isClock <$> o
  gen True = VarE 'C.clockGen
  gen False = pd
  constraints = AppT (ConT ''C.KnownDomain) . VarT <$> domains
  applyDomains = flip (foldl AppT) (fmap VarT domains)
  retTy = applyDomains $ ConT $ datatypeNameO desc
  argTy = applyDomains $ ConT $ datatypeNameI desc

makeScaffold'
  :: (ScaffoldDesc -> ScaffoldPort -> Name)
  -> String
  -> String
  -> [Parameter]
  -> [[Port]]
  -> DecsQ
makeScaffold' portname nam@(n:ame) primitive' parameters ports' = do
  currLoc <- loc_module <$> location
  let desc = ScaffoldDesc
             { functionName  = mkName nam
             , functionName# = mkName (nam ++ "#")
             , functionNameI = mkName (nam ++ "I")
             , qfunctionName = mkName (currLoc ++ "." ++ nam)

             , datatypeNameI = mkName (toUpper n : ame ++ "I")
             , datatypeNameO = mkName (toUpper n : ame ++ "O")

             , templateName  = mkName (nam ++ "TF")
             , qtemplateName = mkName (currLoc ++ "." ++ nam ++ "TF")

             , primitive     = primitive'
             }

  (domains, ports) <- collectDomains <$> mapM scaffoldDomain ports'

  let kinds = flip KindedTV (ConT ''C.Domain) <$> domains

  let i = sortOn (not . isClock) $ filterDir (Netlist.In) ports
  let o = sortOn (not . isClock) $ filterDir (Netlist.Out) ports

  let ni = portname desc <$> i
  let no = portname desc <$> o

  mappend (mconcat
   [ makeDatatypes desc (kinds,domains) (i,ni) (o,no)
   , makeWrapper desc (kinds, domains) (i,ni) o
   ]) <$> makeTemplate desc parameters domains i o
 where
  filterDir dir = filter ((dir==) . direction)
  collectDomains = foldl (\(ns, pss) (n',ps) -> (n':ns,ps<>pss)) ([],[])
makeScaffold' _ _ _ _ _ = error "makeScaffold': Empty name given!"

defaultRecords :: ScaffoldDesc -> ScaffoldPort -> Name
defaultRecords _ port = mkName $ "_" <> name port

makeScaffold
  :: String -- ^ generated haskell function name
  -> String -- ^ hdl primitive name
  -> [Parameter]
  -> [[Port]]
  -> DecsQ
makeScaffold
  = makeScaffold' defaultRecords
