{- |
Module      :  $Header$
Description :  parser for SORT-ITEMs
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parser for SORT-ITEMs (sort and subsort declarations and definitions)
-}

{-
   parse SORT-ITEM and "sort/sorts SORT-ITEM ; ... ; SORT-ITEM"
   parse DATATYPE-DECL

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module CASL.SortItem (sortItem, datatype) where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import Text.ParserCombinators.Parsec
import Common.Token
import CASL.Formula

-- ------------------------------------------------------------------------
-- sortItem
-- ------------------------------------------------------------------------

commaSortDecl :: [String] -> Id -> AParser st (SORT_ITEM f)
commaSortDecl ks s =
    do c <- anComma
       (is, cs) <- sortId ks `separatedBy` anComma
       let l = s : is
           p = catRange (c:cs)
       subSortDecl ks (l, p) <|> return (Sort_decl l p)

isoDecl :: AParsable f => [String] -> Id -> AParser st (SORT_ITEM f)
isoDecl ks s =
    do e <- equalT
       subSortDefn ks (s, tokPos e) <|>
           (do (l, p) <- sortId ks `separatedBy` equalT
               return (Iso_decl (s:l) (catRange (e:p))))

subSortDefn :: AParsable f => [String] -> (Id, Range)
            -> AParser st (SORT_ITEM f)
subSortDefn ks (s, e) =
    do a <- annos
       o <- oBraceT << addAnnos
       v <- varId ks
       c <- colonT
       t <- sortId ks
       d <- dotT
       f <- formula ks
       a2 <- annos
       p <- cBraceT
       return $ Subsort_defn s v t (Annoted f nullRange a a2)
                  (e `appRange` catRange [o, c, d, p])

subSortDecl :: [String] -> ([Id], Range) -> AParser st (SORT_ITEM f)
subSortDecl ks (l, p) =
    do t <- lessT
       s <- sortId ks
       return $ Subsort_decl l s (p `appRange` tokPos t)

sortItem :: AParsable f => [String] -> AParser st (SORT_ITEM f)
sortItem ks =
    do s <- sortId ks
       subSortDecl ks ([s],nullRange) <|> commaSortDecl ks s
          <|> isoDecl ks s  <|> return (Sort_decl [s] nullRange)

-- ------------------------------------------------------------------------
-- typeItem
-- ------------------------------------------------------------------------

datatype :: [String] -> AParser st DATATYPE_DECL
datatype ks =
    do s <- sortId ks
       e <- asKey defnS
       a <- getAnnos
       (Annoted v _ _ b:alts, ps) <- aAlternative ks `separatedBy` barT
       return (Datatype_decl s (Annoted v nullRange a b:alts)
                        (catRange (e:ps)))

aAlternative :: [String] -> AParser st (Annoted ALTERNATIVE)
aAlternative ks =
    do a <- alternative ks
       an <- lineAnnos
       return (Annoted a nullRange [] an)

alternative :: [String] -> AParser st ALTERNATIVE
alternative ks =
    do s <- pluralKeyword sortS
       (ts, cs) <- sortId ks `separatedBy` anComma
       return (Subsorts ts (catRange (s:cs)))
    <|>
    do i <- consId ks
       do   o <- wrapAnnos oParenT
            (cs, ps) <- component ks `separatedBy` anSemi
            c <- addAnnos >> cParenT
            let qs = toRange o ps c
            do   q <- try (addAnnos >> quMarkT)
                 return (Alt_construct Partial i cs (qs `appRange` tokPos q))
              <|> return (Alt_construct Total i cs qs)
         <|> return (Alt_construct Total i [] nullRange)

isSortId :: Id -> Bool
isSortId (Id is _ _) = case is of
                       [Token (c : _) _] -> caslLetters c
                       _ -> False

component :: [String] -> AParser st COMPONENTS
component ks =
    do (is, cs) <- parseId ks `separatedBy` anComma
       if isSingle is && isSortId (head is) then
          compSort ks is cs <|> return (Sort (head is))
          else compSort ks is cs

compSort :: [String] -> [OP_NAME] -> [Token] -> AParser st COMPONENTS
compSort ks is cs =
    do c <- anColon
       (b, t, qs) <- opSort ks
       let p = catRange (cs++[c]) `appRange` qs
       return $ Cons_select (if b then Partial else Total) is t p
