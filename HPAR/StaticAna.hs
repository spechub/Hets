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

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Lib.State
import Common.Id
import Common.Result
import Common.ExtSign

import qualified Data.Map as Map
import qualified Data.Set as Set

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
        sents = hSens accTh
   in Result ds $  Just (newBs, ExtSign outSig (declSyms accTh), sents)

anaBasicSpec :: HBasic.H_BASIC_SPEC -> State HTheoryAna HBasic.H_BASIC_SPEC
anaBasicSpec (HBasic.Basic_spec al) = fmap HBasic.Basic_spec $
      mapAnM anaBasicItems al

anaBasicItems :: HBasic.H_BASIC_ITEMS -> State HTheoryAna HBasic.H_BASIC_ITEMS
anaBasicItems bi = 
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
    let (hth', annofs') = foldl (\(h, l) f -> let (f', h') = runState (anaHFORMULA f) h
                                              in (h', f':l)) (hth, []) annofs 
    let replfs = reverse annofs'
        nfs = map (makeNamedSen.snd) replfs
    put $ hth' {hSens = nfs ++ hSens hth'}
    return $ HBasic.Axiom_items $ map fst replfs
  
anaHFORMULA :: Annoted HBasic.HFORMULA -> State HTheoryAna (Annoted HBasic.HFORMULA, Annoted HBasic.HFORMULA)
anaHFORMULA hf = case item hf of
 HBasic.Base_formula bsen r -> case bsen of
  Mixfix_formula (Mixfix_token i) -> do
   hth <- get
   let hf' = if i `elem` (Map.keys $ hVars hth) then hf { item = HBasic.Nominal True i r}
              else hf{ item = HBasic.Nominal False i r} 
             -- here we check whether the nominal is a variable or not!
   return (hf', hf')
  f -> do
   hth <- get
   let bsig = HSign.baseSig $ hSign hth
       Result ds1 msig = CSign.addSymbToSign (RSign.caslSign bsig) $
                           CSign.Symbol (genName "ST") CSign.SortAsItemType  
       bsig0 = case msig of
                 Nothing -> error $ "could not add sort to sign \n error:\n:" ++ show ds1
                 Just x -> x
       allIds = CAna.getAllIds (Basic_spec []) emptyMix bsig0
       mix = emptyMix { mixRules = makeRules (CSign.globAnnos bsig0) allIds }
       Result ds3 mf = CAna.anaForm (const return) mix 
                                    bsig0{CSign.varMap = Map.union (CSign.varMap bsig0) $ hVars hth} f
   case mf of 
    Nothing -> error $ "could not analyse " ++ show f ++ "\n error:\n" ++ show ds3
    Just (f1, f2) -> let hf1 = hf {item = HBasic.Base_formula f1 r}
                         hf2 = hf {item = HBasic.Base_formula f2 r}
                    in return (hf1, hf2)
 HBasic.Negation f r -> do
   (af1, af2) <- anaHFORMULA $ emptyAnno f
   let hf'= hf { item = HBasic.Negation (item af2) r}
   return (hf{item = HBasic.Negation (item af1) r}, hf')
 HBasic.Conjunction fs r -> do 
   afs' <- mapM anaHFORMULA $ map emptyAnno fs 
   return $ (hf { item = HBasic.Conjunction (map (item.fst) afs') r}, 
             hf { item = HBasic.Conjunction (map (item.snd) afs') r})
 HBasic.Disjunction fs r -> do 
   afs' <- mapM anaHFORMULA $ map emptyAnno fs 
   return $ (hf { item = HBasic.Disjunction (map (item.fst) afs') r}, 
             hf { item = HBasic.Disjunction (map (item.snd) afs') r})
 HBasic.Implication f1 f2 r -> do
   f1' <- anaHFORMULA $ emptyAnno f1
   f2' <- anaHFORMULA $ emptyAnno f2
   return $ (hf {item = HBasic.Implication (item $ fst f1') (item $ fst f2') r}, 
             hf {item = HBasic.Implication (item $ snd f1') (item $ snd f2') r}) 
 HBasic.Equivalence f1 f2 r -> do
   f1' <- anaHFORMULA $ emptyAnno f1
   f2' <- anaHFORMULA $ emptyAnno f2
   return $ (hf {item = HBasic.Equivalence (item $ fst f1') (item $ fst f2') r}, 
             hf {item = HBasic.Equivalence (item $ snd f1') (item $ snd f2') r})
 HBasic.Nominal _b _i _r -> return (hf,hf)
 HBasic.AtState i f r -> do 
   f' <- anaHFORMULA $ emptyAnno f 
   return $ (hf { item = HBasic.AtState i (item $ fst f') r}, 
             hf { item = HBasic.AtState i (item $ snd f') r})
 HBasic.BoxFormula i f r -> do 
   f' <- anaHFORMULA $ emptyAnno f
   return $ (hf { item = HBasic.BoxFormula i (item $ fst f') r}, 
             hf { item = HBasic.BoxFormula i (item $ snd f') r})  
 HBasic.DiamondFormula i f r -> do 
   f' <- anaHFORMULA $ emptyAnno f
   return $ (hf { item = HBasic.DiamondFormula i (item $ fst f') r}, 
             hf { item = HBasic.DiamondFormula i (item $ snd f') r})  
 HBasic.QuantRigidVars q vs f r -> do 
   hth <- get
   let -- bsig = HSign.baseSig $ hSign hth
       varPars = concatMap (\(Var_decl xs s _) -> map (\x -> (x,s)) xs) vs
       (f', _) = runState (anaHFORMULA $ emptyAnno f) $ 
                  hth {hVars = Map.union (hVars hth) $ Map.fromList $ varPars }
   return $ (hf{item = HBasic.QuantRigidVars q vs (item $ fst f') r}, 
             hf{item = HBasic.QuantRigidVars q vs (item $ snd f') r})
 HBasic.QuantNominals q ns f r -> do
   hth <- get
   let (f',_) = runState  (anaHFORMULA $ emptyAnno f) $ 
                 hth {hVars = Map.union (hVars hth) $ Map.fromList $ map (\i -> (i, genName "ST") ) ns}
   return $ (hf { item = HBasic.QuantNominals q ns (item $ fst f') r}, 
             hf { item = HBasic.QuantNominals q ns (item $ snd f') r})
