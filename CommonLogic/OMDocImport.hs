{- |
Module      :  ./CommonLogic/OMDocImport.hs
Description :  OMDoc-to-CommonLogic conversion
Copyright   :  (c) Iulia Ignatov, DFKI Bremen 2009, Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Common Logic implementation of the interface functions
omdocToSym and omdocToSen from class Logic.
The actual instantiation can be found in module "CommonLogic.Logic_CommonLogic".
-}


module CommonLogic.OMDocImport
       ( omdocToSym
       , omdocToSen
       ) where


import OMDoc.DataTypes

import CommonLogic.AS_CommonLogic as AS
import CommonLogic.Symbol
import CommonLogic.OMDoc

import Common.Id
import Common.Result
import Common.AS_Annotation
import qualified Control.Monad.Fail as Fail


type Env = SigMapI Symbol

-- | TCSymbol is transformed into a CommonLogic Symbol with given name
omdocToSym :: Env -> TCElement -> String -> Result Symbol
omdocToSym _ (TCSymbol _ _ sr _) n =
     case sr of
       Obj -> return $ Symbol (nameToId n)
       _ -> Fail.fail $ "omdocToSym: only objects are allowed as symbol roles, but found" ++ show sr
omdocToSym _ symb _ = Fail.fail $ "omdocToSym: only TCSymbols are allowed, but found: " ++ show symb


-- | Sentences from OMElements
omdocToSen :: Env -> TCElement -> String -> Result (Maybe (Named TEXT_META))
omdocToSen e (TCSymbol _ t sr _) n =
    case nameDecode n of
      Just _ ->
          return Nothing -- don't translate encoded names here
      Nothing ->
          let ns = makeNamed n $ emptyTextMeta { getText = toText e t }
              res b = return $ Just $ ns { isAxiom = b }
          in case sr of
               Axiom -> res True
               Theorem -> res False
               _ -> return Nothing
omdocToSen _ sym _ = Fail.fail $ concat [ "omdocToSen: only TCSymbol is allowed,"
                                   , " but found: ", show sym ]

toText :: Env -> OMElement -> TEXT
toText e om = case om of
  OMA (op : subl)
    | op == const_and -> Text (map (toPhrase e) subl) nullRange
    | op == const_textName -> case subl of
        [OMV (OMName n _), txt@(OMA _)] -> Named_text (strToToken n) (toText e txt) nullRange
        _ -> error $ "toText: only two arguments supported, but found " ++ show subl
    | otherwise -> error $ concat ["toText: only ", show const_and , " and ",
            show const_textName, " and Named_text supported, but found ", show op]
  _ -> error $ "toText: only OMA with at lease one argument is allowed, but found " ++ show om

toPhrase :: Env -> OMElement -> PHRASE
toPhrase e om = case om of
  OMBIND op [n] m ->
      if op == const_module
      then Module $ toModule e m n
      else Sentence $ toSen e om
  OMA (op : cmt : [txt]) ->
      if op == const_comment
      then Comment_text (varToComment cmt) (toText e txt) nullRange
      else Sentence $ toSen e om
  _ -> Sentence $ toSen e om

toModule :: Env -> OMElement -> OMElement -> MODULE
toModule e om n = case om of
  OMA (op : txt : exs) ->
      if op == const_moduleExcludes
      then Mod_ex (toName n) (map toName exs) (toText e txt) nullRange
      else Mod (toName n) (toText e om) nullRange
  _ -> Mod (toName n) (toText e om) nullRange
  where toName (OMV (OMName k _)) = strToToken k
        toName k = error $ "toModule: only OMV OMName supported, but found " ++ show k


toSen :: Env -> OMElement -> SENTENCE
toSen e om = case om of
  OMBIND binder args body ->
    let vars = map toNameSeqmark args
        sent = toSen e body
        quant | binder == const_forall = Universal
              | binder == const_exists = Existential
              | otherwise = error "toSen: not supported binder"
        in Quant_sent quant vars sent nullRange
  OMA (omh : os)
    | omh == const_and ->
      Bool_sent (Junction Conjunction (map (toSen e) os)) nullRange
    | omh == const_or ->
      Bool_sent (Junction Disjunction (map (toSen e) os)) nullRange
    | omh == const_implies ->
      let s1 : s2 : [] = map (toSen e) os
      in Bool_sent (BinOp Implication s1 s2) nullRange
    | omh == const_equivalent ->
      let s1 : s2 : [] = map (toSen e) os
      in Bool_sent (BinOp Biconditional s1 s2) nullRange
    | omh == const_not -> let ns : [] = map (toSen e) os
                          in Bool_sent (Negation ns) nullRange
    | omh == const_eq -> let t1 : t2 : [] = map (omdocToTerm e) os
                         in Atom_sent (Equation t1 t2) nullRange
    | omh == const_comment && not (null os) ->
      let s : [] = map (toSen e) $ tail os
      in Comment_sent (varToComment $ head os) s nullRange
    | omh == const_comment -> error "toSen: commented sentence has no comment"
    | omh == const_irregular -> let s : [] = map (toSen e) os
                                in Irregular_sent s nullRange
    | otherwise -> Atom_sent (Atom (omdocToTerm e omh)
                              (map (omdocToTermSeq e) os)) nullRange
  _ -> error $
       concat [ "toSen: only applications and quantifications are allowed,"
              , " but found: ", show om ]

toNameSeqmark :: OMElement -> NAME_OR_SEQMARK
toNameSeqmark (OMV (OMName n _)) = let dec = strToToken n
                                     in if isSeqMark n
                                        then SeqMark dec
                                        else AS.Name dec
toNameSeqmark _ = error "toNameSeqmark: only variables allowed"

omdocToTerm :: Env -> OMElement -> TERM
omdocToTerm e (OMA (omh : om))
                     | omh == const_comment_term
                        && not (null om) = let t : [] = map (omdocToTerm e) $ tail om
                                           in Comment_term t (varToComment $ head om) nullRange
                     | omh == const_comment_term = error "omdocToTerm: commented term has no comment"
                     | otherwise = let th = omdocToTerm e omh
                                       ts = map (omdocToTermSeq e) om
                                    in Funct_term th ts nullRange
omdocToTerm _ (OMS (_, OMName n _)) = Name_term (strToToken n)
omdocToTerm _ (OMV (OMName n _)) = Name_term (strToToken n)
omdocToTerm _ om = error $ "omdocToTerm: only applications and symbols allowed, but found: " ++ show om


omdocToTermSeq :: Env -> OMElement -> TERM_SEQ
omdocToTermSeq e om@(OMA _) = Term_seq $ omdocToTerm e om
omdocToTermSeq _ (OMS (_, OMName n _)) = let dec = strToToken n
                                         in if isSeqMark n
                                            then Seq_marks dec
                                            else Term_seq (Name_term dec)
omdocToTermSeq _ (OMV (OMName n _)) = let dec = strToToken n
                                       in if isSeqMark n
                                          then Seq_marks dec
                                          else Term_seq (Name_term dec)
omdocToTermSeq _ om = error $ "omdocToTermSeq: only applications, symbols and variables allowed, but found: " ++ show om

strToToken :: String -> Token
strToToken s = Token s nullRange

isSeqMark :: String -> Bool
isSeqMark ('.' : _) = True
isSeqMark _ = False

varToComment :: OMElement -> COMMENT
varToComment (OMV (OMName cmt _)) = Comment cmt nullRange
varToComment om = error $ "varToComment: only OMV OMName supported, but found: " ++ show om
