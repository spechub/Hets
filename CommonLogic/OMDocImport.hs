{- |
Module      :  $Header$
Description :  OMDoc-to-CommonLogic conversion
Copyright   :  (c) Iulia Ignatov, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  i.ignatov@jacobs-university.de
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




type Env = SigMapI Symbol

 --------------- TCSymbol is transformed into a CommonLogic Symbol with given name
omdocToSym :: Env -> TCElement -> String -> Result Symbol
omdocToSym _ (TCSymbol _ _ sr _) n =
     case sr of
       Obj -> return $  (Symbol (nameToId n)) 
       _ -> fail $ concat ["omdocToSym: only objects are allowed as symbol roles, but found", show sr]
omdocToSym _ symb _ = fail $ concat ["omdocToSym: only TCSymbols are allowed, but found: ", show symb] 



 
 --------------- Sentences from OMElements
omdocToSen :: Env -> TCElement -> String -> Result (Maybe (Named TEXT))
omdocToSen e (TCSymbol _ t sr _) n =
    case nameDecode n of
      Just _ ->
          return Nothing -- don't translate encoded names here
      Nothing ->
          let ns = makeNamed n $ toText e t
              res b = return $ Just $ ns { isAxiom = b }
          in case sr of
               Axiom -> res True
               Theorem -> res False
               _ -> return Nothing
omdocToSen _ sym _ = fail $ concat [ "omdocToSen: only TCSymbol is allowed,"
                                   , " but found: ", show sym ]

toText :: Env -> OMElement -> TEXT
toText e om = case om of
  OMA (const_and : phrs) -> Text (map (toPhrase e) phrs) nullRange
  OMATTT txt (OMAttr const_textName (OMV (OMName n _))) ->
    Named_text n (toText e txt) nullRange
  _ -> error $ "toText: unsupported " ++ show om

toPhrase :: Env -> OMElement -> PHRASE
toPhrase e om = case om of
  OMBIND const_module [n] m -> Module $ toModule e m n
  OMBIND const_module _ _ -> error "toPhrase: only one bound module name allowed"
  OMA (const_comment : OMV (OMName cmt _) : [txt]) ->
      Comment_text (Comment cmt nullRange) (toText e txt) nullRange
  OMA (const_comment : _ : txt) -> error "toPhrase: comment itself must be a OMName"
  OMA (const_comment : _ : _) -> error "toPhrase: text must be single element"
  _ -> Sentence $ toSen e om
  

toModule :: Env -> OMElement -> OMElement -> MODULE
toModule e om n = case om of
  OMA (const_moduleExcludes : txt : exs) ->
      Mod_ex (toName n) (map toName exs) (toText e txt) nullRange
  txt -> Mod (toName n) (toText e txt) nullRange
  where toName (OMV (OMName k _)) = strToToken k
        toName k = error $ "toModule: only name supported, but found " ++ show k


toSen :: Env -> OMElement -> SENTENCE
toSen e om = case om of
                        OMBIND binder args body -> let vars = map toNameSeqmark args
                                                       sent = toSen e body
                                                       quant 
                                                             | binder == const_forall = Universal
                                                             | binder == const_exists = Existential
                                                             | otherwise = error "toSen: not supported binder"
                                                    in Quant_sent (quant vars sent) nullRange
                        OMA (omh : os)
                                | omh == const_and -> Bool_sent (Conjunction (map (toSen e) os)) nullRange
                                | omh == const_or -> Bool_sent (Disjunction (map (toSen e) os)) nullRange
                                | omh == const_implies -> let s1:s2:[] = map (toSen e) os
                                                           in Bool_sent (Implication s1 s2) nullRange
                                | omh == const_equivalent -> let s1:s2:[] = map (toSen e) os
                                                              in Bool_sent (Biconditional s1 s2) nullRange
                                | omh == const_not -> let ns:[] = map (toSen e) os
                                                       in Bool_sent (Negation ns) nullRange
                                | omh == const_eq -> let t1:t2:[] = map (omdocToTerm e) os
                                                      in Atom_sent (Equation t1 t2) nullRange
                                | omh == const_comment -> let s:[] = map (toSen e) os
                                                           in Comment_sent (Comment "" nullRange) s nullRange
                                | omh == const_irregular -> let s:[] = map (toSen e) os
                                                             in Irregular_sent s nullRange
                                | otherwise ->  Atom_sent (Atom (omdocToTerm e omh)  (map (omdocToTermSeq e) os)) nullRange
                        _ -> error $ concat [ "toSen: only applications and quantifications are allowed,"
                                              , " but found: ", show om ]

toNameSeqmark :: OMElement -> NAME_OR_SEQMARK 
toNameSeqmark (OMV (OMName n _)) =  let dec = strToToken n
                                     in if isSeqMark n
                                        then SeqMark dec
                                        else AS.Name dec
toNameSeqmark _ = error $ "toNameSeqmark: only variables allowed"

omdocToTerm :: Env -> OMElement -> TERM
omdocToTerm e (OMA (omh : om)) 
                     | omh == const_comment_term = let t:[] = map (omdocToTerm e) om 
                                                    in Comment_term t (Comment "" nullRange) nullRange
                     | otherwise = let th = omdocToTerm e omh 
                                       ts = map (omdocToTermSeq e) om
                                    in Funct_term th ts nullRange
omdocToTerm _ (OMS (_, OMName n _)) = Name_term (strToToken n)
omdocToTerm _ (OMV (OMName n _)) = Name_term (strToToken n)
omdocToTerm _ om = error $ "omdocToTerm: only applications and symbols allowed, but found: " ++ show om


omdocToTermSeq :: Env -> OMElement -> TERM_SEQ 
omdocToTermSeq e om@(OMA _) = Term_seq $ omdocToTerm e om
omdocToTermSeq _ (OMS (_,OMName n _)) = let dec = strToToken n 
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
isSeqMark ('.':_) = True
isSeqMark _ = False