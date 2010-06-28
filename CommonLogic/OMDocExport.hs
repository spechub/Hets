module CommonLogic.OMDocExport where

import CommonLogic.AS_CommonLogic
import CommonLogic.Sign
import CommonLogic.Symbol
import CommonLogic.OMDoc

import OMDoc.DataTypes

import Common.Id
import Common.Result
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel

import qualified Data.Map as Map
import Data.Maybe



type Env = NameMap Symbol                  



exportSymToOmdoc :: Env -> Symbol  -> String -> Result TCElement
exportSymToOmdoc _ _ n = return $ (TCSymbol n const_symbol Obj Nothing)



------------------------------------------------------------
exportSenToOmdoc :: Env -> SENTENCE 
                 -> Result TCorOMElement
exportSenToOmdoc en s = return $ Right $ exportSenToOmdoc' en [] s


exportSenToOmdoc' :: Env -> [NAME_OR_SEQMARK] -> SENTENCE
                  -> OMElement
exportSenToOmdoc' en vars s =  case s of
      Quant_sent qs _ -> case qs of 
                            Universal vars2 s2 -> OMBIND   const_forall
                                                           (map exportVar vars2)
                                                           (exportSenToOmdoc' en (union vars vars2) s2)
                            Existential vars2 s2 -> OMBIND   const_exists
                                                             (map exportVar vars2)
                                                              (exportSenToOmdoc' en (union vars vars2) s2) 
      Bool_sent bs _ -> case bs of
                                   Conjunction ss -> OMA $ const_and : (map (exportSenToOmdoc' en vars) ss)
                                   Disjunction ss -> OMA $ const_or : (map (exportSenToOmdoc' en vars) ss)
                                   Negation s1 -> OMA [ const_not,
                                                        exportSenToOmdoc' en vars s1]
                                   Implication s1 s2 -> OMA [ const_implies,
                                                              exportSenToOmdoc' en vars s1,
                                                              exportSenToOmdoc' en vars s2]
                                   Biconditional s1 s2 -> OMA [ const_equivalent,
                                                                exportSenToOmdoc' en vars s1,
                                                                exportSenToOmdoc' en vars s2]
      Atom_sent at ir -> case at of
                                   Equation t1 t2 -> OMA   [ const_eq ,
                                                             exportTerm en vars t1,
                                                             exportTerm en vars t2 ]
                                   Atom pt tts -> OMA $   (exportTerm en pt) : (map (exportTermSeq en vars) tts)  
      Comment_sent com s1 ir -> OMA [const_comment,
                                     exportSenToOmdoc' en vars s1]
      Irregular_sent s1 ir -> OMA [const_irregular,
                                    exportSenToOmdoc' en vars s1]  

exportTerm :: Env -> [NAME_OR_SEQMARK] -> TERM -> OMElement
exportTerm e vars t = case t of
     Name_term n -> if finds (CommonLogic.AS_CommonLogic.Name n) vars
                    then exportVar (CommonLogic.AS_CommonLogic.Name n)
                    else oms e n 
     Funct_term ft tss ir -> OMA $ (exportTerm e vars ft) : (map (exportTermSeq e vars) tss)
     Comment_term t1 com ir -> OMA [ const_comment_term,
                                     exportTerm e vars t1 ]


exportTermSeq :: Env -> [NAME_OR_SEQMARK] ->  TERM_SEQ -> OMElement
exportTermSeq e vars ts = case ts of
     Term_seq t -> exportTerm e vars t
     Seq_marks s -> if finds (SeqMark s) vars
                    then exportVar (SeqMark s)
                    else oms e s  

exportVar :: NAME_OR_SEQMARK -> OMElement
exportVar (CommonLogic.AS_CommonLogic.Name n) = OMV $ mkSimpleName $ tokStr n
exportVar (SeqMark s) = OMV $ mkSimpleName $ tokStr s



oms :: Env -> Token -> OMElement 
oms e x = let s = toSymbol x 
              err = error $ "oms: no mapping for the symbol"
           in simpleOMS $ findInEnv err e s

findInEnv ::(Ord k) => a -> Map.Map k a -> k -> a
findInEnv err m x = Map.findWithDefault err x m

-- transform a NAME_OR_SEQMARK into a symbol. 
toSymbol :: Token -> Symbol  
toSymbol tk@(Token toks tokp) = Symbol (nameToId toks) 



finds :: NAME_OR_SEQMARK -> [NAME_OR_SEQMARK] -> Bool
finds _ [] = False
finds n  a@(m:vars) = if n == m
                      then True
                      else False

union :: [a] -> [a] -> [a]
union [] v2 = v2
union a@(v:v1) v2 = v : (union v1 v2)