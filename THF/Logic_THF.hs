{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for THF.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
               (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)

Instance of class Logic for THF.
-}

module THF.Logic_THF where

import ATC.ProofTree ()

import Common.DefaultMorphism
import Common.ProofTree
import Common.ProverTools

import Data.Monoid

import Logic.Logic

import THF.ATC_THF ()
import THF.Cons
import THF.StaticAnalysisTHF
import THF.ProveLeoII
import THF.ProveIsabelle
import THF.ProveSatallax
import THF.Sign
import THF.Print
import THF.ParseTHF
import qualified THF.Sublogic as SL
import THF.As (TPTP_THF (..))

-- TODO implement more instance methods

data THF = THF deriving Show

instance Language THF where
    description _ =
        "THF is a language for Higher Order Logic from the TPTP standard.\n" ++
        "For further information please refer to" ++
        "http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html"

instance Monoid BasicSpecTHF where
    mempty = BasicSpecTHF []
    mappend (BasicSpecTHF l1) (BasicSpecTHF l2) =
        BasicSpecTHF $ l1 ++ l2

instance Logic.Logic.Syntax THF BasicSpecTHF () () where
    parse_basic_spec THF = Just $ fmap BasicSpecTHF parseTHF
    -- remaining default implementations are fine!

instance Sentences THF SentenceTHF SignTHF MorphismTHF SymbolTHF where
    map_sen THF _ = return
    print_named THF = printNamedSentenceTHF
    {- sym_name THF =
    negation THF _ =
    other default implementations are fine -}

instance StaticAnalysis THF BasicSpecTHF SentenceTHF () ()
               SignTHF MorphismTHF SymbolTHF () where
    basic_analysis THF = Just basicAnalysis
    empty_signature THF = emptySign
    signature_union THF = sigUnion
    signatureDiff THF = sigDiff
    intersection THF = sigIntersect
    is_subsig THF _ _ = True
    subsig_inclusion THF = defaultInclusion

{- In order to find the LeoII prover there must be an entry in the
PATH environment variable leading to the leo executable
(The executable leo.opt is not supported. In this case there should be a link
called leo, or something like that.) -}
instance Logic THF SL.THFSl BasicSpecTHF SentenceTHF () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    all_sublogics THF = SL.sublogics_all
    stability THF = Testing
    provers THF = [] ++ unsafeProverCheck "leo" "PATH" leoIIProver
                     ++ unsafeProverCheck "isabelle" "PATH" isaProver
                     ++ unsafeProverCheck "isabelle" "PATH" nitpickProver
                     ++ unsafeProverCheck "isabelle" "PATH" refuteProver
                     ++ unsafeProverCheck "isabelle" "PATH" sledgehammerProver
                     ++ unsafeProverCheck "satallax" "PATH" satallaxProver

-- Sublogics

instance SemiLatticeWithTop SL.THFSl where
 join = SL.join
 top = SL.THF

instance MinSublogic SL.THFSl BasicSpecTHF where
 minSublogic (BasicSpecTHF xs) = foldr SL.join SL.THF0 $
    map (\x -> case x of
     TPTP_THF_Annotated_Formula _ _ f _ -> minSublogic f
     _ -> SL.THF0
    ) xs

instance SublogicName SL.THFSl where
 sublogicName = show

instance MinSublogic SL.THFSl SymbolTHF where
 minSublogic = \ _ -> SL.THF --actually implement this!

instance MinSublogic SL.THFSl () where
 minSublogic = \ _ -> SL.THF -- why do we need this?

instance MinSublogic SL.THFSl SignTHF where
 minSublogic = \ _ -> SL.THF -- actually implement this!

instance MinSublogic SL.THFSl MorphismTHF where
 minSublogic (MkMorphism s1 s2) = join (minSublogic s1)
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
