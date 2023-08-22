{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HolLight/Sentence.hs
Description :  Sentence for HolLight logic
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

Definition of sentences for HolLight logic

  Ref.

  <http://www.cl.cam.ac.uk/~jrh13/hol-light/>

-}
module HolLight.Sentence where

import Common.DocUtils
import Common.Doc
import HolLight.Helper as Helper
import HolLight.Term
import Data.Data
import Data.Maybe (fromJust, catMaybes, isNothing)
import qualified Data.Char as Char

data Sentence = Sentence {
  term :: Term,
  proof :: Maybe HolProof
  } deriving (Eq, Ord, Show, Typeable, Data)

instance Pretty Sentence where
  pretty = ppPrintTerm . term

ppPrintTerm :: Term -> Doc
ppPrintTerm = printTerm 0

precParens :: Int -> Doc -> Doc
precParens prec = if prec /= 0 then parens else id

replacePt :: Term -> HolParseType -> Term
replacePt tm pt = case tm of
  Var s t _ -> Var s t (HolTermInfo (pt, Nothing))
  Const s t _ -> Const s t (HolTermInfo (pt, Nothing))
  _ -> tm

printTerm :: Int -> Term -> Doc
printTerm prec tm =
 let _1 = case destNumeral tm of
         Just i -> Just (text (show i))
         _ -> Nothing in
  let _2 = case destList tm of
         Just tms -> case Helper.typeOf tm of
           Just t -> case destType t of
             Just (_, x : _) -> case destType x of
               Just ("char", _) -> let cs = map codeOfTerm tms
                 in if any isNothing cs then Nothing
                    else Just (quotes (text (foldr ((:) . Char.chr) []
                                              (catMaybes cs))))
               _ -> Nothing
             _ -> Nothing
           _ -> Nothing
         _ -> Nothing in
 let _3 = if isNothing _2 then case destList tm of
            Just tms -> Just (brackets (printTermSequence "; " 0 tms))
            _ -> Nothing
       else Nothing in
 let _4 = if isGabs tm then Just (printBinder prec tm)
       else Nothing in
 let (s, _, args, hop) = case stripComb tm of
               (hop', args') -> case fromJust (Helper.typeOf hop') of
               {- not really sure in which cases (typeOf hop) == Nothing,
               but shouldn't happen if i understand the original
               ocaml code correctly -}
                  ty0' ->
                    let s0 = nameOf hop' in
                    case reverseInterface (s0, hop') of
                      (s', Just pt) -> (s', ty0', args', replacePt hop' pt)
                      _ -> (s0, ty0', args', hop') in
 let _5 = case (s, isConst tm, null args) of
         ("EMPTY", True, True) -> Just (braces empty)
         ("UNIV", True, True) -> case Helper.typeOf tm of
            Just t -> case destFunTy t of
              Just (ty, _) -> Just (parens (hcat [text ":", ppPrintType ty]))
              _ -> Nothing
            _ -> Nothing
         ("INSERT", _, _) ->
            let (mems, oth) = splitlist (destBinary' "INSERT") tm
            in case (isConst oth, destConst oth) of
                 (True, Just ("EMPTY", _)) -> Just (braces (printTermSequence
                                                     ", " 14 mems))
                 _ -> Nothing
         ("GSPEC", _, _) -> case rand tm of
            Just rtm -> case body rtm of
              Just b -> let (evs, bod) = stripExists b
                        in case destComb bod of
                             Nothing -> Nothing
                             Just (bod1, fabs) ->
                               case destComb bod1 of
                                 Nothing -> Nothing
                                 Just (bod2, babs) ->
                                   case rator bod2 of
                                     Nothing -> Nothing
                                     Just c ->
                                       case destConst c of
                                         Just ("SETSPEC", _) ->
                                          Just (braces (hcat [
                                           printTerm 0 fabs,
                                           text " | ",
                                           printTermSequence "," 14 evs,
                                           text " | ",
                                           printTerm 0 babs
                                          ]))
                                         _ -> Nothing
              _ -> Nothing
            _ -> Nothing
         _ -> Nothing in
 let _6 = case destLet tm of
         Just (e : eqs, _) -> case mkEq e of
           Just e' -> let eqs' = map (\ (v, t) -> mkEq (v, t)) eqs
             in if elem Nothing eqs' then Nothing else
                Just (precParens prec
                        (hcat [
                          text "let ",
                          printTerm 0 e',
                          vcat (map (\ eq -> hcat [
                               text "and ",
                               printTerm 0 eq]) (catMaybes eqs')
                                ++ [text " in", text ""])
                        ]))
           _ -> Nothing
         _ -> Nothing in
 let _7 = if s == "DECIMAL" && length args > 2 then
         case (destNumeral (head args), destNumeral (args !! 1)) of
           (Just n_num, Just n_den) -> if not (powerof10 n_den) then Nothing
             else let s_num = text (show (n_num `quot` n_den)) in
                  let s_den = text (concat (tail (map (: [])
                                    (show (n_den + (n_num `mod` n_den)))
                                   )))
                   in Just (hcat [text "#", s_num, if n_den == 1 then empty
                                            else text ".",
                            s_den])
           _ -> Nothing
       else Nothing in
 let _8 = if s == "_MATCH" && length args == 2 then
         case destClauses (args !! 1) of
           Just cls -> Just (precParens prec (vcat [
             hcat [text "match ",
              printTerm 0 (head args),
              text " with"],
             printClauses cls]))
           _ -> Nothing
       else Nothing in
 let _9 = if s == "_FUNCTION" && length args == 1 then
            case destClauses (head args) of
              Just cls -> Just (precParens prec (vcat [
                  text "function",
                  printClauses cls
                ]))
              _ -> Nothing
          else Nothing in
 let _10 = if s == "COND" && length args == 3 then
         Just (precParens prec (vcat [
          hcat [text "if ", printTerm 0 (head args)],
          hcat [text " then ", printTerm 0 (args !! 1)],
          hcat [text " else ", printTerm 0 (args !! 2)]
         ]))
       else Nothing in
 let _11 = if isPrefix hop && length args == 1 then
          Just ((if prec == 1000 then parens else id)
                (hcat $ if all Char.isAlphaNum s || s == "--"
                    || (
                        case destComb (head args) of
                          Just (l, _) -> let (s0, _) = (nameOf l, Helper.typeOf l)
                            in fst (reverseInterface (s0, hop)) == "--"
                               || (case destConst l of
                                    Just (f, _) -> f `elem` ["real_of_num",
                                                          "int_of_num"]
                                    _ -> False)
                          _ -> False)
                    || s == "~" then
                        [text s, printTerm 999 (head args), text " "]
                 else [text s, printTerm 999 (head args)]))
        else Nothing in
 let _12 = if parsesAsBinder hop && length args == 1 && isGabs (head args)
           then Just (printBinder prec tm)
           else Nothing in
 let _13 = if canGetInfixStatus hop && length args == 2 then
          let bargs = if aright hop then
                        let (tms, tmt) = splitlist (destBinary hop) tm
                                         in tms ++ [tmt]
                      else
                        let (tmt, tms) = revSplitlist (destBinary hop) tm
                                         in tmt : tms in
          let (newprec, unspaced_binops) = (getPrec hop, [",", "..", "$"])
          in Just ((if newprec <= prec then parens else id) (hcat
                    (printTerm newprec (head bargs) :
                     map (\ x -> hcat $
                      if s `elem` unspaced_binops then [text s,
                                                        printTerm newprec x]
                      else
                       [text " ", text s, text " ", printTerm newprec x]
                     ) (tail bargs)
                  )))
        else Nothing in
 let _14 = if (isConst hop || isVar hop) && null args then
             let s' = if parsesAsBinder hop || canGetInfixStatus hop
                         || isPrefix tm then parens (text s) else text s
             in Just s'
           else Nothing in
 let _15 = case destComb tm of
              Just (l, r) -> let mem = case destConst l of
                                        Just (s', _) -> s' `elem`
                                          ["real_of_num", "int_of_num"]
                                        _ -> False
                            in Just ((if prec == 1000 then parens else id)
                                         (hcat $ if not mem
                                          then [printTerm 999 l, text " ",
                                                printTerm 1000 r]
                                          else [printTerm 999 l,
                                                printTerm 1000 r]))
              _ -> Nothing
 in head (catMaybes [_1, _2, _3, _4, _5, _6, _7, _8, _9,
                     _10, _11, _12, _13, _14, _15, Just empty])

printTermSequence :: String -> Int -> [Term] -> Doc
printTermSequence sep' prec tms =
  if null tms then empty
  else hcat (punctuate (text sep') (map (printTerm prec) tms))

printBinder :: Int -> Term -> Doc
printBinder prec tm =
    let absf = isGabs tm in
    let s' = if absf then Just "\\"
             else case rator tm of
                   Just r -> Just (nameOf r)
                   Nothing -> Nothing in
    case s' of
     Just s -> let collectvs tm'
                    | absf =
                       if isAbs tm' then
                        case destAbs tm' of
                         Just (v, t) -> let (vs, bod) = collectvs t
                                        in ((False, v) : vs, bod)
                         _ -> ([], tm')
                       else if isGabs tm' then
                        case destGabs tm' of
                         Just (v, t) -> let (vs, bod) = collectvs t
                                        in ((True, v) : vs, bod)
                         _ -> ([], tm')
                       else ([], tm')
                    | isComb tm' =
                       case rator tm' of
                        Just r'' -> if nameOf r'' == s then
                         case rand tm' of
                          Just r'
                           | isAbs r' ->
                              case destAbs r' of
                               Just (v, t) -> let (vs, bod) = collectvs t
                                              in ((False, v) : vs, bod)
                               _ -> ([], tm')
                           | isGabs r' ->
                              case destGabs r' of
                               Just (v, t) -> let (vs, bod) = collectvs t
                                              in ((True, v) : vs, bod)
                               _ -> ([], tm')
                           | otherwise -> ([], tm')
                          _ -> ([], tm')
                         else ([], tm')
                        _ -> ([], tm')
                    | otherwise = ([], tm') in
       let (vs, bod) = collectvs tm in
         precParens prec (hcat ([
           text s,
           if all Char.isAlphaNum s then text " " else empty]
           ++ map (\ (b, x) -> hcat [
                 (if b then parens else id) (printTerm 0 x),
                 text " "] )
               (init vs)
           ++ [
            if fst (last vs) then text "(" else empty,
            printTerm 0 (snd (last vs)),
            if fst (last vs) then text ")" else empty,
            text ".",
            if length vs == 1 then text " " else empty,
            printTerm 0 bod
           ]
          ))
     _ -> empty

printClauses :: [[Term]] -> Doc
printClauses cls = case cls of
  [] -> empty
  c : cls' -> vcat (printClause c :
   map (\ cl -> hcat [text "| ", printClause cl]) cls')

printClause :: [Term] -> Doc
printClause cl = case cl of
  [p, g, r] -> hcat [printTerm 1 p,
                   text " when ",
                   printTerm 1 g,
                   text " -> ",
                   printTerm 1 r]
  [p, r] -> hcat [printTerm 1 p,
                 text " -> ",
                 printTerm 1 r]
  _ -> empty
