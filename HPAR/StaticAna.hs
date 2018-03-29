{- |
Module      :  ./HPAR/StaticAna.hs
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  portable

static analysis of hybrid partial algebras
-}

module HPAR.StaticAna where

import qualified HPAR.AS_Basic_HPAR as HBasic
import HPAR.Print_AS ()
import qualified HPAR.Sign as HSign

import qualified RigidCASL.StaticAna as RAna
import qualified RigidCASL.Sign as RSign

import qualified CASL.Sign as CSign 
import CASL.MixfixParser
import qualified CASL.StaticAna as CAna
import CASL.AS_Basic_CASL
import CASL.ShowMixfix
import CASL.Overload
import CASL.Quantification

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Keywords
import Common.Lib.State
import Common.Id
import Common.Result
import Common.ExtSign
import qualified Common.Lib.MapSet as MapSet
import Control.Monad (foldM)

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List as List

import Debug.Trace

data HTheoryAna = HTheoryAna {
                   hSign :: HSign.HSign,
                   declSyms :: Set.Set CSign.Symbol,
                   hSens :: [Named HBasic.HFORMULA],
                   hVars :: Map.Map SIMPLE_ID SORT,
                   anaDiags :: [Diagnosis]
                   }
      deriving Show

basicAnalysis :: (HBasic.H_BASIC_SPEC, HSign.HSign, GlobalAnnos)
                  -> Result (HBasic.H_BASIC_SPEC, ExtSign HSign.HSign CSign.Symbol, [Named HBasic.HFORMULA])
basicAnalysis (bs, inSig, ga) = 
   let  bSig' = let bSig = HSign.baseSig inSig 
                in bSig {CSign.globAnnos = CAna.addAssocs bSig ga } 
        inSig' = inSig {HSign.baseSig = bSig'}
        hth = HTheoryAna inSig' Set.empty [] Map.empty []
        (newBs, accTh) = runState (anaBasicSpec bs) hth
        ds = reverse $ anaDiags accTh
        outSig = hSign accTh
        sents = -- map (\x -> x{sentence = nomsInSens outSig $ sentence x}) $ 
                hSens accTh
   in trace ("basic spec before analysis:\n" ++ show bs ++ "\n\nbasic spec after analysis:" ++ show newBs) $ 
      Result ds $  Just (newBs, ExtSign outSig (declSyms accTh), sents)

anaBasicSpec :: HBasic.H_BASIC_SPEC -> State HTheoryAna HBasic.H_BASIC_SPEC
anaBasicSpec bs@(HBasic.Basic_spec al) = fmap HBasic.Basic_spec $
      mapAnM (anaBasicItems bs) al

anaBasicItems :: HBasic.H_BASIC_SPEC -> HBasic.H_BASIC_ITEMS -> State HTheoryAna HBasic.H_BASIC_ITEMS
anaBasicItems bs bi = 
 case bi of
  HBasic.PAR_decl pbi -> do
    hth <- get
    let hsign = hSign hth 
    let (pbi', asig) = runState (CAna.ana_BASIC_ITEMS RAna.typeAnaF 
                                 RAna.anaRBasicItem RAna.anaRSigItem 
                                 RAna.anaMix pbi) $ HSign.baseSig hsign
        hsign' = hsign {HSign.baseSig = asig}
    put $ hth { hSign = hsign' }
    return $ HBasic.PAR_decl pbi' 
  HBasic.Nom_decl (HBasic.Nom_item noms _) -> do 
    hth <- get
    let hsign = hSign hth
    let hsign' = foldl (\s n -> HSign.addNomToSig s $ mkId [n]) hsign noms
    put $ hth {hSign = hsign'}
    return bi
  HBasic.Mod_decl (HBasic.Mod_item mods i _) -> do
    hth <- get
    let hsign = hSign hth 
    let hsign' = foldl (\s m -> HSign.addModToSig s (mkId [m]) i) hsign mods
    put $ hth { hSign = hsign' } 
    return bi
  HBasic.Axiom_items annofs -> do
    hth <- get
    -- let allIds = CAna.getAllIds (Basic_spec []) emptyMix  (RSign.caslSign $ HSign.baseSig $ hSign hth) 
    let (hth', annofs') = foldl (\(h, l) f -> let (f', h') = runState (anaHFORMULA f) h
                                              in (h', f':l)) (hth, []) annofs 
    let replfs = -- map (\x -> x {item = nomsInSens (hSign hth') $ item x} ) $ 
                 reverse annofs'
        nfs = map makeNamedSen replfs
    put $ hth' {hSens = nfs ++ hSens hth'}
    return $ HBasic.Axiom_items replfs 
  
anaHFORMULA :: Annoted HBasic.HFORMULA -> State HTheoryAna (Annoted HBasic.HFORMULA)
anaHFORMULA hf = case item hf of
 HBasic.Base_formula bsen r -> case bsen of
  Mixfix_formula (Mixfix_token i) -> trace ("Checking for " ++ show i ) $ do
   hth <- get
   if i `elem` (Map.keys $ hVars hth) then return $ hf { item = HBasic.Nominal True i r}
   else return $ hf{ item = HBasic.Nominal False i r} -- here we check whether the nominal is a variable or not!
  f -> do
   hth <- get
   let bsig = HSign.baseSig $ hSign hth
       Result ds1 msig = CSign.addSymbToSign (RSign.caslSign bsig) $ CSign.Symbol (genName "ST") CSign.SortAsItemType  
       bsig0 = case msig of
                 Nothing -> error $ "could not add sort to sign"
                 Just x -> x
       --Result ds2 msig' = foldM (\aSig i -> CSign.addSymbToSign aSig $ CSign.Symbol i $  CSign.PredAsItemType $ CSign.PredType []) bsig0 $ HSign.noms $ hSign hth
                            -- have to be able to solve Mixfix_formula (Mixfix_token fifo)
       --bsig1 = case msig' of 
       --          Nothing -> error $ "could not add noms to sign"
       --          Just x -> x
       allIds = CAna.getAllIds (Basic_spec []) emptyMix bsig0
       mix = emptyMix { mixRules = makeRules (CSign.globAnnos bsig0) allIds }
       Result ds3 mf = --CAna.cASLsen_analysis (Basic_spec [], bsig0, f)
                       -- minExpFORMULA (const return) bsig0{CSign.varMap = Map.union (CSign.varMap bsig0) $ hVars hth} f
                       CAna.anaForm (const return) mix bsig0{CSign.varMap = Map.union (CSign.varMap bsig0) $ hVars hth} f
   --let (asens , _bsig') = trace ("\n\ncall for:" ++ show bsen ++ "\n\n in sig " ++ show bsig1) $ runState (CAna.anaVarForms (const return) emptyMix [] [emptyAnno bsen] r) bsig1
   case mf of 
    Nothing -> error $ "could not analyse " ++ show f ++ "error:\n" ++ show ds3
    Just (_, f') -> return $ hf {item = HBasic.Base_formula f' r}
 HBasic.Negation f r -> do
   af' <- anaHFORMULA $ emptyAnno f
   return $ hf { item = HBasic.Negation (item af') r}
 HBasic.Conjunction fs r -> do 
   afs' <- mapM anaHFORMULA $ map emptyAnno fs 
   return $ hf { item = HBasic.Conjunction (map item afs') r}
 HBasic.Disjunction fs r -> do 
   afs' <- mapM anaHFORMULA $ map emptyAnno fs 
   return $ hf { item = HBasic.Disjunction (map item afs') r}
 HBasic.Implication f1 f2 r -> do
   f1' <- anaHFORMULA $ emptyAnno f1
   f2' <- anaHFORMULA $ emptyAnno f2
   return $ hf {item = HBasic.Implication (item f1') (item f2') r} 
 HBasic.Equivalence f1 f2 r -> do
   f1' <- anaHFORMULA $ emptyAnno f1
   f2' <- anaHFORMULA $ emptyAnno f2
   return $ hf { item = HBasic.Equivalence (item f1') (item f2') r }
 HBasic.Nominal b i r -> return hf
 HBasic.AtState i f r -> do 
   f' <- anaHFORMULA $ emptyAnno f 
   return $ hf { item = HBasic.AtState i (item f') r} 
 HBasic.BoxFormula i f r -> do 
   f' <- anaHFORMULA $ emptyAnno f
   return $ hf { item = HBasic.BoxFormula i (item f') r}  
 HBasic.DiamondFormula i f r -> do 
   f' <- anaHFORMULA $ emptyAnno f
   return $ hf{item = HBasic.DiamondFormula i (item f') r}
 HBasic.QuantRigidVars q vs f r -> do 
   hth <- get
   let bsig = HSign.baseSig $ hSign hth
       varPars = concatMap (\(Var_decl xs s _) -> map (\x -> (x,s)) xs) vs
       --Result ds msig = foldM (\aSig (x,s) -> CSign.addSymbToSign aSig $ CSign.Symbol (simpleIdToId x) $ CSign.OpAsItemType$ CSign.OpType Total [] s) bsig varPars
       --vsig = case msig of 
       --         Nothing -> error "can't add vars as sorts"
       --         Just x -> x
       (f', _) = runState (anaHFORMULA $ emptyAnno f) $ hth {hVars = Map.union (hVars hth) $ Map.fromList $ varPars } -- here we must add the variables to the signature, and then remove them
   return $ hf{item = HBasic.QuantRigidVars q vs (item f') r}
 HBasic.QuantNominals q ns f r -> do
   hth <- get
   let (f',_) = runState  (anaHFORMULA $ emptyAnno f) $ hth {hVars = Map.union (hVars hth) $ Map.fromList $ map (\i -> (i, genName "ST") ) ns}
   return $ hf { item = HBasic.QuantNominals q ns (item f') r} 


{-
nomsInSens :: HSign.HSign -> HBasic.HFORMULA -> HBasic.HFORMULA
nomsInSens hsig hsen = 
 case hsen of
  HBasic.Base_formula bsen r ->  case bsen of 
                                  Mixfix_formula (Mixfix_token t) -> -- trace ("base:" ++ show hsen ++ "\nt:" ++ show t ++ "hsig:" ++ show (HSign.noms hsig)) $ 
                                      if Set.member (mkId [t]) $ HSign.noms hsig 
                                       then HBasic.Nominal t r
                                       else hsen
                                  _ -> hsen
  HBasic.Negation f r -> HBasic.Negation (nomsInSens hsig f) r
  HBasic.Conjunction fs r -> HBasic.Conjunction (map (nomsInSens hsig) fs) r
  HBasic.Disjunction fs r -> HBasic.Disjunction (map (nomsInSens hsig) fs) r
  HBasic.Implication f1 f2 r -> HBasic.Implication (nomsInSens hsig f1) (nomsInSens hsig f2) r 
  HBasic.Equivalence f1 f2 r -> HBasic.Equivalence (nomsInSens hsig f1) (nomsInSens hsig f2) r
  HBasic.Nominal _ _ -> hsen 
  HBasic.AtState i f r -> HBasic.AtState i (nomsInSens hsig f) r
  HBasic.BoxFormula i f r -> HBasic.BoxFormula i (nomsInSens hsig f) r  
  HBasic.DiamondFormula i f r -> HBasic.DiamondFormula i (nomsInSens hsig f) r
  HBasic.QuantRigidVars q v f r -> HBasic.QuantRigidVars q v (nomsInSens hsig f) r
  HBasic.QuantNominals q n f r -> HBasic.QuantNominals q n (nomsInSens hsig f) r
-}
