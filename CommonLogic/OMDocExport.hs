{- |
Module      :  ./CommonLogic/OMDocExport.hs
Description :  CommonLogic-to-OMDoc conversion
Copyright   :  (c) Iulia Ignatov, DFKI Bremen 2009, Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
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
import CommonLogic.OMDoc

import OMDoc.DataTypes

import Common.Id
import Common.Result

import qualified Data.HashMap.Lazy as Map
import Data.Hashable


type Env = NameMap Symbol

-- | Exports the symbol @n@ to OMDoc
exportSymToOmdoc :: Env -> Symbol -> String -> Result TCElement
exportSymToOmdoc _ _ n = return $ TCSymbol n const_symbol Obj Nothing


-- | Exports the text @tm@ to OMDoc
exportSenToOmdoc :: Env -> TEXT_META
                 -> Result TCorOMElement
exportSenToOmdoc en tm = return $ Right $ exportText en [] $ AS.getText tm

exportText :: Env -> [NAME_OR_SEQMARK] -> TEXT -> OMElement
exportText en vars txt = case txt of
  Text phrs _ ->
      OMA $ const_and : map (exportPhr en vars) (filter nonImportation phrs)
  Named_text n t _ ->
      OMA [const_textName, OMV $ mkSimpleName $ tokStr n, exportText en vars t]
  where nonImportation p = case p of
          Importation _ -> False
          _ -> True

exportPhr :: Env -> [NAME_OR_SEQMARK] -> PHRASE -> OMElement
exportPhr en vars phr = case phr of
   Importation _ -> undefined -- does not occur
   Module m -> OMBIND const_module [modName m] $ exportModule en vars m
   Sentence s -> exportSen en vars s
   Comment_text c t _ ->
      OMA [const_comment, varFromComment c, exportText en vars t]
  where modName m = case m of
          Mod n _ _ -> exportVar $ AS.Name n
          Mod_ex n _ _ _ -> exportVar $ AS.Name n

exportModule :: Env -> [NAME_OR_SEQMARK] -> MODULE -> OMElement
exportModule en vars m = case m of
  Mod _ t _ -> exportText en vars t
  Mod_ex _ exs t _ -> OMA $ const_moduleExcludes : exportText en vars t
      : map (exportVar . AS.Name) exs

exportSen :: Env -> [NAME_OR_SEQMARK] -> SENTENCE
                  -> OMElement
exportSen en vars s = case s of
      Quant_sent q vars2 s2 _ ->
        OMBIND (case q of
                   Universal -> const_forall
                   Existential -> const_exists)
        (map exportVar vars2)
        (exportSen en (vars ++ vars2) s2)
      Bool_sent bs _ -> case bs of
          Junction j ss ->
            OMA $ (case j of Conjunction -> const_and
                             Disjunction -> const_or)
            : map (exportSen en vars) ss
          Negation s1 -> OMA [ const_not, exportSen en vars s1]
          BinOp op s1 s2 -> OMA
              [ case op of Implication -> const_implies
                           Biconditional -> const_equivalent
              , exportSen en vars s1
              , exportSen en vars s2]
      Atom_sent at _ -> case at of
          Equation t1 t2 -> OMA
              [ const_eq
              , exportTerm en vars t1
              , exportTerm en vars t2 ]
          Atom pt tts ->
              OMA $ exportTerm en vars pt : map (exportTermSeq en vars) tts
      Comment_sent _com s1 _ ->
          OMA [const_comment, varFromComment _com, exportSen en vars s1]
      Irregular_sent s1 _ ->
          OMA [const_irregular, exportSen en vars s1]

exportTerm :: Env -> [NAME_OR_SEQMARK] -> TERM -> OMElement
exportTerm e vars t = case t of
     Name_term n -> if AS.Name n `elem` vars
                    then exportVar (AS.Name n)
                    else oms e n
     Funct_term ft tss _ ->
         OMA $ exportTerm e vars ft : map (exportTermSeq e vars) tss
     Comment_term t1 _com _ ->
         OMA [ const_comment_term, varFromComment _com, exportTerm e vars t1 ]
     That_term s _ ->
         OMA [ const_that, exportSen e vars s ]

exportTermSeq :: Env -> [NAME_OR_SEQMARK] -> TERM_SEQ -> OMElement
exportTermSeq e vars ts = case ts of
     Term_seq t -> exportTerm e vars t
     Seq_marks s -> if SeqMark s `elem` vars
                    then exportVar (SeqMark s)
                    else oms e s

exportVar :: NAME_OR_SEQMARK -> OMElement
exportVar (AS.Name n) = OMV $ mkSimpleName $ tokStr n
exportVar (SeqMark s) = OMV $ mkSimpleName $ tokStr s

varFromComment :: COMMENT -> OMElement
varFromComment (Comment x _) = OMV $ mkSimpleName x


oms :: Env -> Token -> OMElement
oms e x =
          let s = toSymbol x
              err = error $ "oms: no mapping for the symbol " ++ show s
                  -- printId1 (symName s) ++ "\n" ++ show e ++ "\n\n\n" ++ ""
           in simpleOMS $ findInEnv err e s

findInEnv :: (Ord k, Hashable k) => a -> Map.HashMap k a -> k -> a
findInEnv err m x = Map.findWithDefault err x m

-- transform a NAME_OR_SEQMARK into a symbol.
toSymbol :: Token -> Symbol
toSymbol = Symbol . simpleIdToId
