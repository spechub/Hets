{- |
Module      :  $Header$
Description :  CommonLogic-to-OMDoc conversion
Copyright   :  (c) Iulia Ignatov, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  i.ignatov@jacobs-university.de
Stability   :  experimental
Portability :  portable

Common Logic implementation of the interface functions 
export_senToOmdoc and export_symToOmdoc from class Logic. 
The actual instantiation can be found in module "CommonLogic.Logic_CommonLogic".
-}



module CommonLogic.OMDocExport
       ( exportSymToOmdoc
       , exportSenToOmdoc
       ) where

import CommonLogic.AS_CommonLogic as AS
import CommonLogic.Symbol
--import CommonLogic.Sign
import CommonLogic.OMDoc

import OMDoc.DataTypes

import Common.Id
import Common.Result

import qualified Data.Map as Map



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
                                                            (exportSenToOmdoc' en (vars ++ vars2) s2)
                            Existential vars2 s2 -> OMBIND   const_exists
                                                             (map exportVar vars2)
                                                             (exportSenToOmdoc' en (vars ++ vars2) s2) 
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
      Atom_sent at _ -> case at of
                                   Equation t1 t2 -> OMA   [ const_eq ,
                                                             exportTerm en vars t1,
                                                             exportTerm en vars t2 ]
                                   Atom pt tts -> OMA $   (exportTerm en vars pt) : (map (exportTermSeq en vars) tts)  
      Comment_sent com s1 _ -> OMA [const_comment,
                                     exportSenToOmdoc' en vars s1]
      Irregular_sent s1 _ -> OMA [const_irregular,
                                    exportSenToOmdoc' en vars s1]  

exportTerm :: Env -> [NAME_OR_SEQMARK] -> TERM -> OMElement
exportTerm e vars t = case t of
     Name_term n -> if elem (AS.Name n) vars
                    then exportVar (AS.Name n)
                   else oms e n 
     Funct_term ft tss _ -> OMA $ (exportTerm e vars ft) : (map (exportTermSeq e vars) tss)
     Comment_term t1 com _ -> OMA [ const_comment_term,
                                     exportTerm e vars t1 ]


exportTermSeq :: Env -> [NAME_OR_SEQMARK] ->  TERM_SEQ -> OMElement
exportTermSeq e vars ts = case ts of
     Term_seq t -> exportTerm e vars t
     Seq_marks s -> if elem (SeqMark s) vars
                    then exportVar (SeqMark s)
                    else oms e s  

exportVar :: NAME_OR_SEQMARK -> OMElement
exportVar (AS.Name n) = OMV $ mkSimpleName $ tokStr n
exportVar (SeqMark s) = OMV $ mkSimpleName $ tokStr s



oms :: Env -> Token -> OMElement 
oms e x = let s = toSymbol x 
	      err = error $ "oms: no mapping for the symbol " ++ show s -- printId1 (symName s) ++ "\n" ++ show e ++ "\n\n\n" ++ ""
           in simpleOMS $ findInEnv err e s

findInEnv ::(Ord k) => a -> Map.Map k a -> k -> a
findInEnv err m x = Map.findWithDefault err x m

-- transform a NAME_OR_SEQMARK into a symbol. 
toSymbol :: Token -> Symbol  
toSymbol = Symbol . simpleIdToId 


