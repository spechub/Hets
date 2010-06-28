module CommonLogic.OMDocImport where


import OMDoc.DataTypes

import CommonLogic.AS_CommonLogic as AS
import CommonLogic.Symbol
import CommonLogic.OMDoc

import Common.Id
import Common.Result
import Common.AS_Annotation as AN

import qualified Data.Map as Map
import Data.List


type Env = SigMapI Symbol

 --------------- TCSymbol is transformed into a CommonLogic Symbol with given name
omdocToSym :: Env -> TCElement -> String -> Result Symbol
omdocToSym _ tcs@(TCSymbol _ _ sr _) n =
     case sr of
       Obj -> return $  (Symbol (nameToId n)) 
       _ -> fail $ concat ["omdocToSym: only objects are allowed as symbol roles, but found", show sr]
omdocToSym _ symb _ = fail $ concat ["omdocToSym: only TCSymbols are allowed, but found: ", show symb] 

 
 
 --------------- Sentences from OMElements
omdocToSen :: Env -> TCElement -> String
           -> Result (Maybe (Named SENTENCE))
omdocToSen e (TCSymbol _ t sr _) n =
    case nameDecode n of
      Just _ ->
          return Nothing -- don't translate encoded names here
      Nothing ->
          let ns = makeNamed n $ omdocToSen' e t
              res b = return $ Just $ ns { isAxiom = b }
          in case sr of
               Axiom -> res True
               Theorem -> res False
               _ -> return Nothing
               
omdocToSen' :: Env -> OMElement -> SENTENCE                         
omdocToSen' e om = case om of
                        OMBIND binder args body -> let vars = map toNameSeqmark args
                                                       sent = omdocToSen' e body
                                                       quant 
                                                             | binder == const_forall = Universal
                                                             | binder == const_exists = Existential
                                                             | otherwise = error "omdocToSen': not supported binder"
                                                    in Quant_sent (quant vars sent) nullRange
                        OMA (omh : os)
                                | omh == const_and -> Bool_sent (Conjunction (map (omdocToSen' e) os)) nullRange
                                | omh == const_or -> Bool_sent (Disjunction (map (omdocToSen' e) os)) nullRange
                                | omh == const_implies -> let s1:s2:[] = map (omdocToSen' e) os
                                                           in Bool_sent (Implication s1 s2) nullRange
                                | omh == const_equivalent -> let s1:s2:[] = map (omdocToSen' e) os 
                                                              in Bool_sent (Biconditional s1 s2) nullRange
                                | omh == const_not -> let ns:[] = map (omdocToSen' e) os
                                                       in Bool_sent (Negation ns) nullRange
                                | omh == const_eq -> let t1:t2:[] = map (omdocToTerm e) os
                                                      in Atom_sent (Equation t1 t2) nullRange
                                | omh == const_comment -> let s:[] = map (omdocToSen' e) os
                                                           in Comment_sent (Comment "" nullRange) s nullRange
                                | omh == const_irregular -> let s:[] = map (omdocToSen' e) os
                                                             in Irregular_sent s nullRange
                                | otherwise ->  Atom_sent (Atom (omdocToTerm e omh)  (map (omdocToTermSeq e) os)) nullRange

toNameSeqmark :: OMElement -> NAME_OR_SEQMARK 
toNameSeqmark (OMV (OMName n _)) =  let dec = strToToken n
                                     in if isSeqMark n
                                        then SeqMark dec
                                        else AS.Name dec

omdocToTerm :: Env -> OMElement -> TERM
omdocToTerm e (OMA (omh : om)) 
                     | omh == const_comment_term = let t:[] = map (omdocToTerm e) om 
                                                    in Comment_term t (Comment "" nullRange) nullRange
                     | otherwise = let th = omdocToTerm e omh 
                                       ts = map (omdocToTermSeq e) om
                                    in Funct_term th ts nullRange
omdocToTerm e (OMS (_, OMName n _)) = Name_term (strToToken n)

omdocToTermSeq :: Env -> OMElement -> TERM_SEQ 
omdocToTermSeq e om@(OMA _) = Term_seq $ omdocToTerm e om
omdocToTermSeq e (OMS (_,OMName n _)) = let dec = strToToken n 
                                         in if isSeqMark n
                                            then Seq_marks dec
                                            else Term_seq (Name_term dec)

strToToken :: String -> Token
strToToken s = Token s nullRange

isSeqMark :: String -> Bool
isSeqMark s@('.':_) = True
isSeqMark _ = False