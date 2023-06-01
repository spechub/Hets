{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./THF/Logic_THF.hs
Description :  Instance of class Logic for THF.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
               (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)

Instance of class Logic for THF.
-}

module THF.Logic_THF where

import ATC.ProofTree ()

import Common.DefaultMorphism
import Common.ProofTree

import Data.Monoid ()
import Data.Map (isSubmapOf)
import qualified Data.Map (toList, foldr)
import qualified Data.Set (fromList)

import Logic.Logic

import THF.ATC_THF ()
import THF.Cons
import THF.As (THFFormula, TPTP_THF (..))
import THF.StaticAnalysisTHF
import THF.ProveLeoII
import THF.ProveIsabelle
import THF.ProveSatallax
import THF.Sign
import THF.Print
import THF.ParseTHF
import qualified THF.Sublogic as SL
import THF.Poly (getSymbols)
import THF.Utils (toId)

-- TODO implement more instance methods

data THF = THF deriving Show

instance Language THF where
    description _ =
        "THF is a language for Higher Order Logic from the TPTP standard.\n" ++
        "For further information please refer to" ++
        "http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html"

instance Semigroup BasicSpecTHF where
    (BasicSpecTHF l1) <> (BasicSpecTHF l2) =
        BasicSpecTHF $ l1 ++ l2
instance Monoid BasicSpecTHF where
    mempty = BasicSpecTHF []

instance Logic.Logic.Syntax THF BasicSpecTHF SymbolTHF () () where
    parse_basic_spec THF = Just (\ _ -> fmap BasicSpecTHF parseTHF)
    -- remaining default implementations are fine!

instance Sentences THF THFFormula SignTHF MorphismTHF SymbolTHF where
    map_sen THF _ = return
    print_named THF = printNamedSentenceTHF Nothing
    symsOfSen THF = getSymbols
    sym_name THF = toId . symId
    symKind THF s = case symType s of
                     ST_Type _ -> "type"
                     ST_Const _ -> "constant"
    sym_of THF s = [Data.Set.fromList . map snd . Data.Map.toList . symbols $ s]
    {- negation THF _ =
    other default implementations are fine -}

instance StaticAnalysis THF BasicSpecTHF THFFormula () ()
               SignTHF MorphismTHF SymbolTHF () where
    basic_analysis THF = Just basicAnalysis
    empty_signature THF = emptySign
    signature_union THF = sigUnion
    signatureDiff THF = sigDiff
    intersection THF = sigIntersect
    is_subsig THF s1 s2 = Data.Map.isSubmapOf (types s1) (types s2) &&
                          Data.Map.isSubmapOf (consts s1) (consts s2)
    subsig_inclusion THF = defaultInclusion

{- In order to find the LeoII prover there must be an entry in the
PATH environment variable leading to the leo executable
(The executable leo.opt is not supported. In this case there should be a link
called leo, or something like that.) -}
instance Logic THF SL.THFSl BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    all_sublogics THF = SL.sublogics_all
    stability THF = Testing
    provers THF =
      [ leoIIProver, isaProver, nitpickProver, refuteProver, sledgehammerProver
      , satallaxProver ]

-- Sublogics

instance SemiLatticeWithTop SL.THFSl where
 lub = SL.joinSL
 top = SL.tHF

instance MinSublogic SL.THFSl BasicSpecTHF where
 minSublogic (BasicSpecTHF xs) = foldr (SL.joinSL .
    (\ x -> case x of
     TPTP_THF_Annotated_Formula _ _ f _ -> minSublogic f
     _ -> SL.tHF0
    )) SL.tHF0 xs

instance SublogicName SL.THFSl where
 sublogicName = show

instance MinSublogic SL.THFSl SymbolTHF where
 minSublogic _ = SL.tHF0 -- actually implement this!

instance MinSublogic SL.THFSl () where
 minSublogic _ = SL.tHF0

instance MinSublogic SL.THFSl SignTHF where
 minSublogic (Sign tp c _) = lub (Data.Map.foldr
   (\ t sl -> lub sl $ minSublogic $ typeKind t)
   SL.tHF0 tp)
  (Data.Map.foldr
   (\ cs sl -> lub sl $ minSublogic $ constType cs)
   SL.tHF0 c)

instance MinSublogic SL.THFSl Type where
 minSublogic (ProdType tps) = foldr (SL.joinSL . minSublogic) SL.tHFP tps
 minSublogic TType = SL.tHF0
 minSublogic OType = SL.tHF0
 minSublogic IType = SL.tHF0
 minSublogic (MapType t1 t2) = SL.joinSL (minSublogic t1) (minSublogic t2)
 minSublogic (CType _) = SL.tHF0
 minSublogic (SType _) = SL.tHF0
 minSublogic (VType _) = SL.tHF0_P
 minSublogic (ParType t) = minSublogic t

instance MinSublogic SL.THFSl Kind where
 minSublogic Kind = SL.tHF0

instance MinSublogic SL.THFSl MorphismTHF where
 minSublogic (MkMorphism s1 s2) = lub (minSublogic s1)
                                            (minSublogic s2)

instance ProjectSublogicM SL.THFSl SymbolTHF where
 projectSublogicM _ _ = Nothing

instance ProjectSublogicM SL.THFSl () where
 projectSublogicM _ _ = Nothing

instance ProjectSublogic SL.THFSl SignTHF where
 projectSublogic _ i = i

instance ProjectSublogic SL.THFSl MorphismTHF where
 projectSublogic _ i = i

instance ProjectSublogic SL.THFSl BasicSpecTHF where
 projectSublogic _ i = i
