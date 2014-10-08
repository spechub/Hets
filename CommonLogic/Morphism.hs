{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  $Header$
Description :  Morphism of Common Logic
Copyright   :  (c) Uni Bremen DFKI 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (via Logic.Logic)

Morphism of Common Logic

-}

module CommonLogic.Morphism
  ( Morphism (..)
  , pretty                      -- pretty printing
  , idMor                       -- identity morphism
  , isLegalMorphism             -- check if morhpism is ok
  , composeMor                  -- composition
  , inclusionMap                -- inclusion map
  , mkMorphism                  -- create Morphism
  , mapSentence                 -- map of sentences
  , applyMap                    -- application function for maps
  , applyMorphism               -- application function for morphism
  , morphismUnion
  ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Result as Result
import Common.Id as Id
import Common.Result
import Common.Doc
import Common.DocUtils

import CommonLogic.AS_CommonLogic as AS
import CommonLogic.Sign as Sign

import Control.Monad (unless)

import Data.Data

-- maps of sets
data Morphism = Morphism
  { source :: Sign
  , target :: Sign
  , propMap :: Map.Map Id Id
  } deriving (Eq, Ord, Show, Typeable)

instance Pretty Morphism where
    pretty = printMorphism

-- | Constructs an id-morphism
idMor :: Sign -> Morphism
idMor a = inclusionMap a a

-- | Determines whether a morphism is valid
isLegalMorphism :: Morphism -> Result ()
isLegalMorphism pmor =
    let psource = allItems $ source pmor
        ptarget = allItems $ target pmor
        pdom = Map.keysSet $ propMap pmor
        pcodom = Set.map (applyMorphism pmor) psource
    in unless (Set.isSubsetOf pcodom ptarget && Set.isSubsetOf pdom psource) $
    fail "illegal CommonLogic morphism"

-- | Application funtion for morphisms
applyMorphism :: Morphism -> Id -> Id
applyMorphism mor idt = Map.findWithDefault idt idt $ propMap mor

-- | Application function for propMaps
applyMap :: Map.Map Id Id -> Id -> Id
applyMap pmap idt = Map.findWithDefault idt idt pmap

-- | Composition of morphisms in propositional Logic
composeMor :: Morphism -> Morphism -> Result Morphism
composeMor f g =
  let fSource = source f
      gTarget = target g
      fMap = propMap f
      gMap = propMap g
  in return Morphism
  { source = fSource
  , target = gTarget
  , propMap = if Map.null gMap then fMap else
      Set.fold ( \ i -> let j = applyMap gMap (applyMap fMap i) in
                        if i == j then id else Map.insert i j)
                                  Map.empty $ allItems fSource }

-- | Pretty printing for Morphisms
printMorphism :: Morphism -> Doc
printMorphism m = pretty (source m) <> text "-->" <> pretty (target m)
  <> vcat (map ( \ (x, y) -> lparen <> pretty x <> text ","
  <> pretty y <> rparen) $ Map.assocs $ propMap m)

-- | Inclusion map of a subsig into a supersig
inclusionMap :: Sign.Sign -> Sign.Sign -> Morphism
inclusionMap s1 s2 = Morphism
  { source = s1
  , target = s2
  , propMap = Map.empty }

-- | creates a Morphism
mkMorphism :: Sign.Sign -> Sign.Sign -> Map.Map Id Id -> Morphism
mkMorphism s t p =
  Morphism { source = s
           , target = t
           , propMap = p }

{- | sentence (text) translation along signature morphism
here just the renaming of formulae -}
mapSentence :: Morphism -> AS.TEXT_META -> Result.Result AS.TEXT_META
mapSentence mor tm =
  return $ tm { getText = mapSen_txt mor $ getText tm }

-- propagates the translation to sentences
mapSen_txt :: Morphism -> AS.TEXT -> AS.TEXT
mapSen_txt mor txt = case txt of
  AS.Text phrs r -> AS.Text (map (mapSen_phr mor) phrs) r
  AS.Named_text n t r -> AS.Named_text n (mapSen_txt mor t) r

-- propagates the translation to sentences
mapSen_phr :: Morphism -> AS.PHRASE -> AS.PHRASE
mapSen_phr mor phr = case phr of
  AS.Module m -> AS.Module $ mapSen_mod mor m
  AS.Sentence s -> AS.Sentence $ mapSen_sen mor s
  AS.Comment_text c t r -> AS.Comment_text c (mapSen_txt mor t) r
  x -> x

-- propagates the translation to sentences
mapSen_mod :: Morphism -> AS.MODULE -> AS.MODULE
mapSen_mod mor m = case m of
  AS.Mod n t rn -> AS.Mod n (mapSen_txt mor t) rn
  AS.Mod_ex n exs t rn -> AS.Mod_ex n exs (mapSen_txt mor t) rn

mapSen_sen :: Morphism -> AS.SENTENCE -> AS.SENTENCE
mapSen_sen mor frm = case frm of
  AS.Quant_sent q vs is rn ->
    AS.Quant_sent q (map (mapSen_nos mor) vs) (mapSen_sen mor is) rn
  AS.Bool_sent bs rn -> AS.Bool_sent (case bs of
      AS.Junction j sens -> AS.Junction j (map (mapSen_sen mor) sens)
      AS.Negation sen -> AS.Negation (mapSen_sen mor sen)
      AS.BinOp op s1 s2 ->
          AS.BinOp op (mapSen_sen mor s1) (mapSen_sen mor s2)
    ) rn
  AS.Atom_sent atom rn -> AS.Atom_sent (case atom of
      AS.Equation t1 t2 -> AS.Equation (mapSen_trm mor t1) (mapSen_trm mor t2)
      AS.Atom t tss -> AS.Atom (mapSen_trm mor t) (map (mapSen_trmSeq mor) tss)
    ) rn
  AS.Comment_sent cm sen rn -> AS.Comment_sent cm (mapSen_sen mor sen) rn
  AS.Irregular_sent sen rn -> AS.Irregular_sent (mapSen_sen mor sen) rn

mapSen_trm :: Morphism -> AS.TERM -> AS.TERM
mapSen_trm mor trm = case trm of
  AS.Name_term n -> AS.Name_term (mapSen_tok mor n)
  AS.Funct_term t ts rn ->
      AS.Funct_term (mapSen_trm mor t) (map (mapSen_trmSeq mor) ts) rn
  AS.Comment_term t c rn -> AS.Comment_term (mapSen_trm mor t) c rn
  AS.That_term s rn -> AS.That_term (mapSen_sen mor s) rn

mapSen_nos :: Morphism -> AS.NAME_OR_SEQMARK -> AS.NAME_OR_SEQMARK
mapSen_nos mor nos = case nos of
  AS.Name n -> AS.Name (mapSen_tok mor n)
  AS.SeqMark s -> AS.SeqMark (mapSen_tok mor s)

mapSen_trmSeq :: Morphism -> AS.TERM_SEQ -> AS.TERM_SEQ
mapSen_trmSeq mor ts = case ts of
  AS.Term_seq t -> AS.Term_seq (mapSen_trm mor t)
  AS.Seq_marks s -> AS.Seq_marks (mapSen_tok mor s)

mapSen_tok :: Morphism -> Id.Token -> Id.Token
mapSen_tok mor tok = Id.idToSimpleId $ applyMorphism mor $ Id.simpleIdToId tok

-- | Union of two morphisms.
morphismUnion :: Morphism -> Morphism -> Result.Result Morphism
morphismUnion mor1 mor2 =
  let pmap1 = propMap mor1
      pmap2 = propMap mor2
      p1 = source mor1
      p2 = source mor2
      up1 = Set.difference (allItems p1) $ Map.keysSet pmap1
      up2 = Set.difference (allItems p2) $ Map.keysSet pmap2
      (pds, pmap) = foldr ( \ (i, j) (ds, m) -> case Map.lookup i m of
          Nothing -> (ds, Map.insert i j m)
          Just k -> if j == k then (ds, m) else
              (Diag Error
               ("incompatible mapping of prop " ++ showId i " to "
                ++ showId j " and " ++ showId k "")
               nullRange : ds, m))
          ([], pmap1)
          (Map.toList pmap2 ++ map (\ a -> (a, a))
                      (Set.toList $ Set.union up1 up2))
   in if null pds then return Morphism
      { source = unite p1 p2
      , target = unite (target mor1) $ target mor2
      , propMap = pmap } else Result pds Nothing
