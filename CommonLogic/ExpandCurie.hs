{- |
Module      :  ./CommonLogic/ExpandCurie.hs
Description :  Expansion of abbreviated IRI to full IRI
Copyright   :  (c) Eugen Kuksa, Uni Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Provides a function to expand each abbreviated IRI to a full IRI
in a basic spec.
-}

module CommonLogic.ExpandCurie
  ( expandCurieBS
  ) where

import qualified Common.AS_Annotation as Anno
import Common.Id
import Common.IRI
import CommonLogic.AS_CommonLogic
import CommonLogic.Lexer_CLIF (clLetters)

import qualified Data.HashMap.Strict as Map

{- | Expands each abbreviated IRI to a full IRI in the basic spec according to
the supplemented map @gpm@. An IRI is stored in a name (quoted string). If
the prefix of an abbreviated IRI is not in the map, the IRI won't be expanded.
-}
expandCurieBS :: Map.HashMap String IRI -> BASIC_SPEC -> BASIC_SPEC
expandCurieBS gpm (Basic_spec abis) = Basic_spec $ map
    (\ abi@Anno.Annoted {Anno.item = bi} -> abi {Anno.item = expBI gpm bi})
    abis

expBI :: Map.HashMap String IRI -> BASIC_ITEMS -> BASIC_ITEMS
expBI gpm (Axiom_items atms) =
  Axiom_items $ map (expAnTextMeta gpm) atms

expAnTextMeta :: Map.HashMap String IRI
  -> Anno.Annoted TEXT_META -> Anno.Annoted TEXT_META
expAnTextMeta gpm an@Anno.Annoted {Anno.item = tm} =
  an {Anno.item = expTextMeta gpm tm}

expTextMeta :: Map.HashMap String IRI -> TEXT_META -> TEXT_META
expTextMeta gpm tm =
  tm { getText = expTxt (Map.unionWith (\ _ p2 -> p2) gpm $
                            Map.fromList $ prefix_map tm) (getText tm) }

expTxt :: Map.HashMap String IRI -> TEXT -> TEXT
expTxt pm t = case t of
  Text phrs rn -> Text (map (expPhr pm) phrs) rn
  Named_text n txt rn -> Named_text (expName pm n) (expTxt pm txt) rn

expPhr :: Map.HashMap String IRI -> PHRASE -> PHRASE
expPhr pm p = case p of
  Module m -> Module (expMod pm m)
  Sentence s -> Sentence (expSen pm s)
  Importation i -> Importation (expImp pm i)
  Comment_text c t rn -> Comment_text c (expTxt pm t) rn

expMod :: Map.HashMap String IRI -> MODULE -> MODULE
expMod pm m = case m of
  Mod n t rn -> Mod (expName pm n) (expTxt pm t) rn
  Mod_ex n ns t rn ->
      Mod_ex (expName pm n) (map (expName pm) ns) (expTxt pm t) rn

expImp :: Map.HashMap String IRI -> IMPORTATION -> IMPORTATION
expImp pm (Imp_name n) = Imp_name $ expName pm n

expSen :: Map.HashMap String IRI -> SENTENCE -> SENTENCE
expSen pm s = case s of
  Quant_sent q noss s2 rn ->
    Quant_sent q (map (expNos pm) noss) (expSen pm s2) rn
  Bool_sent bs rn -> Bool_sent (case bs of
      Junction j ss -> Junction j $ map (expSen pm) ss
      Negation s2 -> Negation $ expSen pm s2
      BinOp op s1 s2 -> BinOp op (expSen pm s1) (expSen pm s2)
    ) rn
  Atom_sent as rn -> Atom_sent (case as of
      Equation t1 t2 -> Equation (expTrm pm t1) (expTrm pm t2)
      Atom t tseqs -> Atom (expTrm pm t) $ map (expTseq pm) tseqs
    ) rn
  Comment_sent c cs rn -> Comment_sent c (expSen pm cs) rn
  Irregular_sent is rn -> Irregular_sent (expSen pm is) rn

expNos :: Map.HashMap String IRI -> NAME_OR_SEQMARK -> NAME_OR_SEQMARK
expNos pm nos = case nos of
  Name n -> Name $ expName pm n
  SeqMark s -> SeqMark $ expName pm s

expTrm :: Map.HashMap String IRI -> TERM -> TERM
expTrm pm trm = case trm of
  Name_term n -> Name_term $ expName pm n
  Funct_term t tseqs rn ->
      Funct_term (expTrm pm t) (map (expTseq pm) tseqs) rn
  Comment_term t c rn -> Comment_term (expTrm pm t) c rn
  That_term s rn -> That_term (expSen pm s) rn

expTseq :: Map.HashMap String IRI -> TERM_SEQ -> TERM_SEQ
expTseq pm nos = case nos of
  Term_seq t -> Term_seq $ expTrm pm t
  Seq_marks s -> Seq_marks $ expName pm s

expName :: Map.HashMap String IRI -> NAME -> NAME
expName pm n = case fmap (expandCurie pm) $ parseCurie (strippedQuotesStr n) of
  Just (Just x) -> let s = iriToStringShortUnsecure x
                   in Token (if not $ all clLetters s
                              then "\"" ++ s ++ "\""
                              else s) $ tokPos n
  _ -> n

strippedQuotesStr :: NAME -> String
strippedQuotesStr n =
  let str = tokStr n
      middleStr = init $ tail str
  in case str of
        '\"' : _ : _ -> middleStr
        '\'' : _ : _ -> middleStr
        _ -> str
