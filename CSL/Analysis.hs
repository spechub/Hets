{- |
Module      :  $Header$
Description :  Static Analysis for EnCL
Copyright   :  (c) Dominik Dietrich, Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Static Analysis for EnCL
-}


module CSL.Analysis where

import Common.ExtSign
import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.ResultT
import Common.Utils (mapAccumLM)

import CSL.AS_BASIC_CSL
import CSL.Symbol
import CSL.Fold
import CSL.Sign as Sign


import Control.Monad.State

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Maybe

-- * Basic Analysis Functions


-- | generates a named formula
withName :: Annoted CMD -> Int -> Named CMD
withName f i = (makeNamed (if label == "" then "Ax_" ++ show i
                                   else label) $ item f)
               { isAxiom = not isTheorem }
    where
      label = getRLabel f
      annos = r_annos f
      isImplies' = foldl (\ y x -> isImplies x || y) False annos
      isImplied' = foldl (\ y x -> isImplied x || y) False annos
      isTheorem = isImplies' || isImplied'


-- | takes a signature and a formula and a number. 
-- It analyzes the formula and returns a formula with diagnosis
analyzeFormula :: Sign.Sign -> (Annoted CMD) -> Int -> Result (Named CMD)
analyzeFormula _ f i =
    return $ withName f i


-- | Extracts the axioms and the signature of a basic spec
splitSpec :: BASIC_SPEC -> Sign.Sign -> Result (Sign.Sign, [Named CMD])
splitSpec (Basic_spec specitems) sig =
    do
      ((newsig, _), mNCmds) <- mapAccumLM anaBasicItem (sig, 0) specitems
      return (newsig, catMaybes mNCmds)

anaBasicItem :: (Sign.Sign, Int) -> Annoted BASIC_ITEM
             -> Result ((Sign.Sign, Int), Maybe (Named CMD))
anaBasicItem (sign, i) itm =
    case item itm of
      Op_decl (Op_item tokens _) -> return ((addTokens sign tokens, i), Nothing)
      Var_decls l -> return ((addVarDecls sign l, i), Nothing)
      EP_components l -> return ((foldl addEPComponent sign l, i), Nothing)
      Axiom_item annocmd ->
          do
            ncmd <- analyzeFormula sign annocmd i
            return ((sign, i+1), Just ncmd)

-- | adds the specified tokens to the signature
addTokens :: Sign.Sign -> [Token] -> Sign.Sign
addTokens sign tokens = let f res itm = addToSig res itm
                                        $ optypeFromArity 0
                        in foldl f sign tokens



-- | adds the specified var items to the signature
addVarDecls :: Sign.Sign -> [VAR_ITEM] -> Sign.Sign
addVarDecls  = const
{-
addVarDecls sign vitems = foldl f sign vitems where
    f res (Var_item toks dom _) = addVarItem res toks dom
-}

{- | stepwise extends an initially empty signature by the basic spec bs.
 The resulting spec contains analyzed axioms in it. The result contains:
 (1) the basic spec
 (2) the new signature + the added symbols
 (3) sentences of the spec
-}
basicCSLAnalysis :: (BASIC_SPEC, Sign, a)
                 -> Result (BASIC_SPEC, ExtSign Sign Symbol, [Named CMD])
basicCSLAnalysis (bs, sig, _) =
    do 
      (newSig, ncmds) <- splitSpec bs sig
      let newSyms = Set.map Symbol $ opIds $ sigDiff newSig sig
      return (bs, ExtSign newSig newSyms, ncmds)



-- * Alternative Basic Analysis

data AnaEnv = AnaEnv
                 { aVarDecls :: Map.Map Token Domain
                 , aEPConsts :: Map.Map Token EP_const
                 , aEPDecls :: Map.Map Token EP_item
                 , aCommands :: Map.Map Int (Named CMD)
                 , aCounter :: Int
                 }


emptyAnaEnv :: AnaEnv
emptyAnaEnv = AnaEnv
              { aVarDecls = Map.empty
              , aEPConsts = Map.empty
              , aEPDecls = Map.empty
              , aCommands = Map.empty
              , aCounter = 0
              }


{-

tTT :: CMD -> CMD
tTT c = foldCMD myrec c where
    myrec = passAllRecord { foldVar = \ _ _ -> Var $ mkSimpleId "X" }

type Analysis a = ResultT (State AnaEnv) a

-- data VAR_ITEM = Var_item [Id.Token] Domain Id.Range
anaVarDecl :: VAR_ITEM -> Analysis ()
anaVarDecl (Var_item l dom rg) = error ""

-- data EPComponent = EPDomain Id.Token EPDomain | EPDefault Id.Token APInt | EPConst Id.Token APInt
anaEPComp :: EPComponent -> Analysis ()
anaEPComp (EPDomain n dom) = addEPDomain n dom
anaEPComp (EPDefault n i) = addEPDefault n i
anaEPComp (EPConst n i) = addEPConst n i


anaAxiom :: Annoted CMD -> Analysis ()
anaAxiom = error ""

anaBasicItem' :: Annoted BASIC_ITEM -> Analysis ()
anaBasicItem' itm =
    case item itm of
      Op_decl _ -> return ()
      Var_decls l -> mapM_ anaVarDecl l
      EP_components l -> mapM_ anaEPComp l
      Axiom_item annocmd -> anaAxiom annocmd

-}

