{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
{- |
Module      :  $Header: $
Description :  interface (type class) for comorphism modifications in Hets
Copyright   :  (c) Mihai Codescu, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  mcodescu@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic)

Interface (type class) for comorphism modifications in Hets

-}

module Logic.Modification where

import Logic.Logic
import Logic.Comorphism
import Common.Result
import Data.Typeable


-- comorphism modifications

class (Language lid, Comorphism cid1
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
          Comorphism cid2
            log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            log4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4)
          => Modification lid cid1 cid2
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2 
            log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            log4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4
            | 
           lid -> cid1 cid2
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
               sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
               sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            log4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4
    where
      tauSigma :: lid -> sign1 -> Result morphism2 
      -- can leave morphism2 here, in the instances morphism2 and morphism4 will be the same
      -- casts needed
      -- component of the natural transformation
      sourceComorphism :: lid -> cid1
      targetComorphism :: lid -> cid2

data IdModif lid = IdModif lid 
  deriving Show

instance Language lid => Language (IdModif lid)

instance Comorphism cid
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
          => Modification (IdModif cid) cid cid
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
               where
 tauSigma (IdModif cid) sigma = do (sigma1, sen1) <- map_sign cid sigma
                                   return (ide (targetLogic cid)  sigma1)
 sourceComorphism (IdModif cid) = cid
 targetComorphism (IdModif cid) = cid



--vertical composition of modifications

data VerCompModif lid1 lid2 = VerCompModif lid1 lid2 deriving Show

instance (Language lid1, Language lid2) => Language (VerCompModif lid1 lid2)

instance (Modification lid1 cid1 cid2
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            log4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4, 
          Modification lid2 cid3 cid4
            log5 sublogics5 basic_spec5 sentence5 symb_items5 symb_map_items5
                sign5 morphism5 symbol5 raw_symbol5 proof_tree5
            log6 sublogics6 basic_spec6 sentence6 symb_items6 symb_map_items6
                sign6 morphism6 symbol6 raw_symbol6 proof_tree6
            log7 sublogics7 basic_spec7 sentence7 symb_item7 symb_map_items7
                sign7 morphism7 symbol7 raw_symbol7 proof_tree7
            log8 sublogics8 basic_spec8 sentence8 symb_items8 symb_map_items8
                sign8 morphism8 symbol8 raw_symbol8 proof_tree8 
            )
         => Modification (VerCompModif lid1 lid2) cid1 cid4
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            log7 sublogics7 basic_spec7 sentence7 symb_item7 symb_map_items7
                sign7 morphism7 symbol7 raw_symbol7 proof_tree7
            log8 sublogics8 basic_spec8 sentence8 symb_items8 symb_map_items8
                sign8 morphism8 symbol8 raw_symbol8 proof_tree8 

          where
 sourceComorphism (VerCompModif lid1 lid2) = sourceComorphism lid1
 targetComorphism (VerCompModif lid1 lid2) = targetComorphism lid2
 tauSigma (VerCompModif lid1 lid2) sigma = do
                                             mor1 <- tauSigma lid1 sigma
                                             case cast sigma of
                                               Nothing -> do fail "Cannot compose modifications"
                                               Just sigma1 -> do mor3 <- tauSigma lid2 sigma1
                                                                 case cast mor3 of
                                                                  Nothing -> do fail "Cannot compose modifications"
                                                                  Just mor2 -> do mor <- comp (targetLogic $ sourceComorphism lid1) mor1 mor2 
                                                                                  return (mor)

-- horizontal composition of modifications

data HorCompModif lid1 lid2 = HorCompModif lid1 lid2 deriving Show 

instance (Language lid1, Language lid2) => Language (HorCompModif lid1 lid2)

instance (Modification lid1 cid1 cid2
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            log4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4, 
          Modification lid2 cid3 cid4
            log5 sublogics5 basic_spec5 sentence5 symb_items5 symb_map_items5
                sign5 morphism5 symbol5 raw_symbol5 proof_tree5
            log6 sublogics6 basic_spec6 sentence6 symb_items6 symb_map_items6
                sign6 morphism6 symbol6 raw_symbol6 proof_tree6
            log7 sublogics7 basic_spec7 sentence7 symb_items7 symb_map_items7
                sign7 morphism7 symbol7 raw_symbol7 proof_tree7
            log8 sublogics8 basic_spec8 sentence8 symb_items8 symb_map_items8
                sign8 morphism8 symbol8 raw_symbol8 proof_tree8, 
          Comorphism (CompComorphism cid1 cid3)
              log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
              sign1 morphism1 symbol1 raw_symbol1 proof_tree1
              log6 sublogics6 basic_spec6 sentence6 symb_items6 symb_map_items6
              sign6 morphism6 symbol6 raw_symbol6 proof_tree6,
          Comorphism (CompComorphism cid2 cid4)
              log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
               sign3 morphism3 symbol3 raw_symbol3 proof_tree3
              log8 sublogics8 basic_spec8 sentence8 symb_items8 symb_map_items8
              sign8 morphism8 symbol8 raw_symbol8 proof_tree8)
         => Modification (HorCompModif lid1 lid2) (CompComorphism cid1 cid3) (CompComorphism cid2 cid4)
              log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
              sign1 morphism1 symbol1 raw_symbol1 proof_tree1
              log6 sublogics6 basic_spec6 sentence6 symb_items6 symb_map_items6
              sign6 morphism6 symbol6 raw_symbol6 proof_tree6 
              log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
               sign3 morphism3 symbol3 raw_symbol3 proof_tree3
              log8 sublogics8 basic_spec8 sentence8 symb_items8 symb_map_items8
              sign8 morphism8 symbol8 raw_symbol8 proof_tree8
  where
   sourceComorphism (HorCompModif lid1 lid2) = CompComorphism (sourceComorphism lid1) (sourceComorphism lid2)
   targetComorphism (HorCompModif lid1 lid2) = CompComorphism (targetComorphism lid1) (targetComorphism lid2)
   tauSigma (HorCompModif lid1 lid2) sigma1 = do
                                               mor2 <- tauSigma lid1 sigma1
                                               case cast mor2 of
                                                 Nothing -> fail "Cannot compose modifications"
                                                 Just mor5 -> do mor6 <- map_morphism (sourceComorphism lid2) mor5
                                                                 case cast sigma1 of
                                                                   Nothing -> fail "Cannot compose modifications"
                                                                   Just sigma3 -> do (sigma4, sen4) <- map_sign (targetComorphism lid1) sigma3
                                                                                     case cast sigma4 of
                                                                                       Nothing -> fail "Cannot compose modifications"          
                                                                                       Just sigma5 ->do  mor61 <- tauSigma lid2 sigma5
                                                                                                         mor <- comp (targetLogic $ sourceComorphism lid2) mor6 mor61
                                                                                                         return mor     



                                           
     
