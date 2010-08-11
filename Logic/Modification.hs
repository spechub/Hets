{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies
  , FlexibleInstances, UndecidableInstances, ExistentialQuantification #-}
{- |
Module      :  $Header$
Description :  interface (type class) for comorphism modifications in Hets
Copyright   :  (c) Mihai Codescu, Uni Bremen 2002-2004
License     :  GPLv2 or higher
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

-- | comorphism modifications
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
      -- in the instances morphism2 and morphism4 will be the same
      -- casts needed
      -- component of the natural transformation
      sourceComorphism :: lid -> cid1
      targetComorphism :: lid -> cid2

data IdModif lid = IdModif lid deriving Show

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
 tauSigma (IdModif cid) sigma = do (sigma1, _) <- map_sign cid sigma
                                   return (ide sigma1)
 sourceComorphism (IdModif cid) = cid
 targetComorphism (IdModif cid) = cid

-- | vertical composition of modifications
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
 sourceComorphism (VerCompModif lid1 _) = sourceComorphism lid1
 targetComorphism (VerCompModif _ lid2) = targetComorphism lid2
 tauSigma (VerCompModif lid1 lid2) sigma = do
   mor1 <- tauSigma lid1 sigma
   case cast sigma of
     Nothing -> fail "Cannot compose modifications"
     Just sigma1 -> do
       mor3 <- tauSigma lid2 sigma1
       case cast mor3 of
         Nothing -> fail "Cannot compose modifications"
         Just mor2 -> comp mor1 mor2

-- | horizontal composition of modifications
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
         => Modification (HorCompModif lid1 lid2) (CompComorphism cid1 cid3)
                (CompComorphism cid2 cid4)
              log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
              sign1 morphism1 symbol1 raw_symbol1 proof_tree1
              log6 sublogics6 basic_spec6 sentence6 symb_items6 symb_map_items6
              sign6 morphism6 symbol6 raw_symbol6 proof_tree6
              log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
               sign3 morphism3 symbol3 raw_symbol3 proof_tree3
              log8 sublogics8 basic_spec8 sentence8 symb_items8 symb_map_items8
              sign8 morphism8 symbol8 raw_symbol8 proof_tree8
  where
   sourceComorphism (HorCompModif lid1 lid2) =
       CompComorphism (sourceComorphism lid1) (sourceComorphism lid2)
   targetComorphism (HorCompModif lid1 lid2) =
       CompComorphism (targetComorphism lid1) (targetComorphism lid2)
   tauSigma (HorCompModif lid1 lid2) sigma1 = do
     mor2 <- tauSigma lid1 sigma1
     case cast mor2 of
       Nothing -> fail "Cannot compose modifications"
       Just mor5 -> do
         mor6 <- map_morphism (sourceComorphism lid2) mor5
         case cast sigma1 of
           Nothing -> fail "Cannot compose modifications"
           Just sigma3 -> do
             (sigma4, _) <- map_sign (targetComorphism lid1) sigma3
             case cast sigma4 of
               Nothing -> fail "Cannot compose modifications"
               Just sigma5 -> tauSigma lid2 sigma5 >>= comp mor6

-- | Modifications
data AnyModification = forall
                     lid cid1 cid2
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            log4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4.
                      Modification lid cid1 cid2
            log1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            log2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            log3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            log4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4
            => Modification lid

instance Eq AnyModification where
  m1 == m2 = compare m1 m2 == EQ

instance Ord AnyModification where
  compare (Modification lid1) (Modification lid2) =
    compare (language_name lid1) $ language_name lid2
    -- maybe needs to be more elaborate

instance Show AnyModification where
   show (Modification lid) = language_name lid
     ++ ":" ++ language_name (sourceComorphism lid)
     ++ "=>" ++ language_name (targetComorphism lid)

idModification :: AnyComorphism -> AnyModification
idModification (Comorphism cid) = Modification (IdModif cid)

-- | vertical compositions of modifications

vertCompModification :: Monad m => AnyModification -> AnyModification
                     -> m AnyModification
vertCompModification (Modification lid1) (Modification lid2) =
   let cid1 = targetComorphism lid1
       cid2 = sourceComorphism lid2
   in
    if language_name cid1 == language_name cid2
    then return $ Modification (VerCompModif lid1 lid2)
    else fail $ "Comorphism mismatch in composition of" ++ language_name lid1
             ++ "and" ++  language_name lid2

-- | horizontal composition of modifications

horCompModification :: Monad m => AnyModification -> AnyModification
                    -> m AnyModification
horCompModification (Modification lid1) (Modification lid2) =
   let cid1 = sourceComorphism lid1
       cid2 = sourceComorphism lid2
   in if language_name (targetLogic cid1) == language_name (sourceLogic cid2)
      then return $ Modification (HorCompModif lid1 lid2)
      else fail $ "Logic mismatch in composition of" ++ language_name lid1
               ++ "and" ++ language_name lid2
