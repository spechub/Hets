{- |
Module      :  ./CASL/Parse_AS_Basic.hs
Description :  Parsing CASL's SIG-ITEMS, BASIC-ITEMS and BASIC-SPEC
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parser for CASL basic specifications (SIG-ITEMS, BASIC-ITEMS, BASIC-SPEC)
   Follows Sect. II:3.1 of the CASL Reference Manual.
-}

{-
   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module CASL.Parse_AS_Basic where

import Common.AS_Annotation
import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.GlobalAnnotations (PrefixMap)

import CASL.AS_Basic_CASL
import CASL.Formula
import CASL.SortItem
import CASL.OpItem

import Text.ParserCombinators.Parsec

-- * signature items

sortItems, typeItems, opItems, predItems, sigItems
    :: (AParsable s, TermParser f) => [String] -> AParser st (SIG_ITEMS s f)
sortItems ks = itemList ks esortS sortItem (Sort_items PossiblyEmptySorts)
    <|> itemList ks sortS sortItem (Sort_items NonEmptySorts)
typeItems ks = itemList ks typeS datatype (Datatype_items NonEmptySorts)
    <|> itemList ks etypeS datatype (Datatype_items PossiblyEmptySorts)

opItems ks = itemList ks opS opItem Op_items
predItems ks = itemList ks predS predItem Pred_items
sigItems ks = fmap Ext_SIG_ITEMS aparser <|>
           sortItems ks <|> opItems ks <|> predItems ks <|> typeItems ks

-- * helpers

datatypeToFreetype :: (AParsable b, AParsable s, TermParser f) =>
                      SIG_ITEMS s f -> Range -> BASIC_ITEMS b s f
datatypeToFreetype d pos =
   case d of
     Datatype_items sk ts ps -> Free_datatype sk ts (pos `appRange` ps)
     _ -> error "datatypeToFreetype"

axiomToLocalVarAxioms :: (AParsable b, AParsable s, TermParser f) =>
     BASIC_ITEMS b s f -> [Annotation] -> [VAR_DECL] -> Range
     -> BASIC_ITEMS b s f
axiomToLocalVarAxioms ai a vs posl =
   case ai of
     Axiom_items (Annoted ft qs as rs : fs) ds ->
         let aft = Annoted ft qs (a ++ as) rs
             in Local_var_axioms vs (aft : fs) (posl `appRange` ds)
     _ -> error "axiomToLocalVarAxioms"

-- * basic items

basicItems :: (AParsable b, AParsable s, TermParser f) =>
              [String] -> AParser st (BASIC_ITEMS b s f)
basicItems ks = fmap Ext_BASIC_ITEMS aparser <|> fmap Sig_items (sigItems ks)
  <|> do
    f <- asKey freeS
    ti <- typeItems ks
    return (datatypeToFreetype ti (tokPos f))
  <|> do
    g <- asKey generatedS
    do t <- typeItems ks
       return (Sort_gen [Annoted t nullRange [] []] $ tokPos g)
      <|> do
        o <- oBraceT
        is <- annosParser (sigItems ks)
        c <- cBraceT
        a <- lineAnnos
        return (Sort_gen (init is ++ [appendAnno (last is) a])
                (toRange g [o] c))
  <|> do
    v <- pluralKeyword varS
    (vs, ps) <- varItems ks
    return (Var_items vs (catRange (v : ps)))
  <|> do
    f <- forallT
    (vs, ps) <- varDecls ks
    a <- annos
    ai <- dotFormulae True ks
    return (axiomToLocalVarAxioms ai a vs $ catRange (f : ps))
  <|> dotFormulae True ks
  <|> itemList ks axiomS formula Axiom_items

varItems :: [String] -> AParser st ([VAR_DECL], [Token])
varItems ks =
    do v <- varDecl ks
       do s <- trySemiOrComma
          do tryItemEnd (ks ++ startKeyword)
             return ([v], [s])
            <|> do
              (vs, ts) <- varItems ks
              return (v : vs, s : ts)
         <|> return ([v], [])

dotFormulae :: (AParsable b, AParsable s, TermParser f) =>
  Bool -> [String] -> AParser st (BASIC_ITEMS b s f)
dotFormulae requireDot ks =
    do d <- (if requireDot then id else option $ mkSimpleId ".") dotT
       (fs, ds) <- aFormula ks `separatedBy` dotT
       (m, an) <- optSemi
       let ps = catRange (d : ds)
           ns = init fs ++ [appendAnno (last fs) an]
       return $ Axiom_items ns (ps `appRange` catRange m)

aFormula :: TermParser f => [String] -> AParser st (Annoted (FORMULA f))
aFormula = allAnnoParser . formula

-- * basic spec

basicSpec :: (TermParser f, AParsable s, AParsable b) =>
             [String] -> PrefixMap -> AParser st (BASIC_SPEC b s f)
basicSpec bi _ = (fmap Basic_spec . annosParser . basicItems) bi
