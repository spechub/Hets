module CommonLogic.ExpandCurie
  ( expandCurieBS
  , expandCurieAnnotedTextMeta
  , expandCurieTextMeta
  ) where

import qualified Common.AS_Annotation as Anno
import Common.Id
import Common.IRI
import CommonLogic.AS_CommonLogic

import qualified Data.Map as Map

expandCurieBS :: BASIC_SPEC -> BASIC_SPEC
expandCurieBS (Basic_spec abis) =
  Basic_spec $ map
          (\abi@Anno.Annoted{Anno.item = bi} -> abi{Anno.item = expBI bi}) abis

expBI :: BASIC_ITEMS -> BASIC_ITEMS
expBI (Axiom_items atms) = Axiom_items $ map expandCurieAnnotedTextMeta atms

expandCurieAnnotedTextMeta :: Anno.Annoted TEXT_META -> Anno.Annoted TEXT_META
expandCurieAnnotedTextMeta an@Anno.Annoted{Anno.item = tm} =
  an{Anno.item = expandCurieTextMeta tm}

expandCurieTextMeta :: TEXT_META -> TEXT_META
expandCurieTextMeta tm =
  tm { getText = expTxt (Map.fromList $ prefix_map tm) (getText tm) }

expTxt :: Map.Map String IRI -> TEXT -> TEXT
expTxt pm t = case t of
  Text phrs rn -> Text (map (expPhr pm) phrs) rn
  Named_text n txt rn -> Named_text (expName pm n) (expTxt pm txt) rn

expPhr :: Map.Map String IRI -> PHRASE -> PHRASE
expPhr pm p = case p of
  Module m -> Module (expMod pm m)
  Sentence s -> Sentence (expSen pm s)
  Importation i -> Importation (expImp pm i)
  Comment_text c t rn -> Comment_text c (expTxt pm t) rn

expMod :: Map.Map String IRI -> MODULE -> MODULE
expMod pm m = case m of
  Mod n t rn -> Mod (expName pm n) (expTxt pm t) rn
  Mod_ex n ns t rn ->
      Mod_ex (expName pm n) (map (expName pm) ns) (expTxt pm t) rn

expImp :: Map.Map String IRI -> IMPORTATION -> IMPORTATION
expImp pm (Imp_name n) = Imp_name $ expName pm n

expSen :: Map.Map String IRI -> SENTENCE -> SENTENCE
expSen pm s = case s of
  Quant_sent qs rn -> Quant_sent (case qs of
      Universal noss s2 -> Universal (map (expNos pm) noss) (expSen pm s2)
      Existential noss s2 -> Existential (map (expNos pm) noss) (expSen pm s2)
    ) rn
  Bool_sent bs rn -> Bool_sent (case bs of
      Conjunction ss -> Conjunction $ map (expSen pm) ss
      Disjunction ss -> Disjunction $ map (expSen pm) ss
      Negation s2 -> Negation $ expSen pm s2
      Implication s1 s2 -> Implication (expSen pm s1) (expSen pm s2)
      Biconditional s1 s2 -> Biconditional (expSen pm s1) (expSen pm s2)
    ) rn
  Atom_sent as rn -> Atom_sent (case as of
      Equation t1 t2 -> Equation (expTrm pm t1) (expTrm pm t2)
      Atom t tseqs -> Atom (expTrm pm t) $ map (expTseq pm) tseqs
    ) rn
  Comment_sent c cs rn -> Comment_sent c (expSen pm cs) rn
  Irregular_sent is rn -> Irregular_sent (expSen pm is) rn

expNos :: Map.Map String IRI -> NAME_OR_SEQMARK -> NAME_OR_SEQMARK
expNos pm nos = case nos of
  Name n -> Name $ expName pm n
  SeqMark s -> SeqMark $ expName pm s

expTrm :: Map.Map String IRI -> TERM -> TERM
expTrm pm trm = case trm of
  Name_term n -> Name_term $ expName pm n
  Funct_term t tseqs rn ->
      Funct_term (expTrm pm t) (map (expTseq pm) tseqs) rn
  Comment_term t c rn -> Comment_term (expTrm pm t) c rn

expTseq :: Map.Map String IRI -> TERM_SEQ -> TERM_SEQ
expTseq pm nos = case nos of
  Term_seq t -> Term_seq $ expTrm pm t
  Seq_marks s -> Seq_marks $ expName pm s

expName :: Map.Map String IRI -> NAME -> NAME
expName pm n = case fmap (expandCurie pm) $ parseCurie (strippedQuotesStr n) of
  Just (Just x) -> mkSimpleId $ "\"" ++ iriToStringUnsecure x ++ "\""
  _ -> n

strippedQuotesStr :: NAME -> String
strippedQuotesStr n =
  let str = tokStr n
      middleStr = init $ tail str
  in case head $ str of
        '\"' -> middleStr
        '\'' -> middleStr
        _ -> str
