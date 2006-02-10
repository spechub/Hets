{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

parse SIG-ITEMS, BASIC-ITEMS, BASIC-SPEC 
   Follows Sect. II:3.1 of the CASL Reference Manual.
-}

{- 
   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module ConstraintCASL.Parse_AS_Basic where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import CASL.AS_Basic_CASL
import ConstraintCASL.AS_ConstraintCASL
import Common.AS_Annotation
import Text.ParserCombinators.Parsec
import ConstraintCASL.Formula
import CASL.Formula (varDecl)
import CASL.SortItem
import CASL.OpItem

type B = ()
type S = ()
type F = ConstraintFORMULA

-- ------------------------------------------------------------------------
-- sigItems
-- ------------------------------------------------------------------------

sortItems, typeItems, opItems, predItems, sigItems 
    :: [String] -> AParser st (SIG_ITEMS S F)
sortItems ks = itemList ks sortS sortItem Sort_items
typeItems ks = itemList ks typeS datatype Datatype_items
opItems   ks = itemList ks opS opItem Op_items
predItems ks = itemList ks predS predItem Pred_items
sigItems ks = fmap Ext_SIG_ITEMS aparser <|>
           sortItems ks <|> opItems ks <|> predItems ks <|> typeItems ks

---- helpers ----------------------------------------------------------------

datatypeToFreetype :: SIG_ITEMS S F -> Range -> BASIC_ITEMS B S F 
datatypeToFreetype d pos =
   case d of
     Datatype_items ts ps -> Free_datatype ts (pos `appRange` ps)
     _ -> error "datatypeToFreetype"

axiomToLocalVarAxioms ::  
   BASIC_ITEMS B S F -> [Annotation] -> [VAR_DECL] -> Range 
     -> BASIC_ITEMS B S F
axiomToLocalVarAxioms ai a vs posl =
   case ai of
     Axiom_items ((Annoted ft qs as rs):fs) ds ->  
         let aft = Annoted ft qs (a++as) rs
             in Local_var_axioms vs (aft:fs) (posl `appRange` ds)
     _ -> error "axiomToLocalVarAxioms"

-- ------------------------------------------------------------------------
-- basicItems
-- ------------------------------------------------------------------------

basicItems :: [String] -> AParser st (BASIC_ITEMS B S F)
basicItems ks = fmap Ext_BASIC_ITEMS aparser <|> fmap Sig_items (sigItems ks)
             <|> do f <- asKey freeS
                    ti <- typeItems ks
                    return (datatypeToFreetype ti (tokPos f))
             <|> do g <- asKey generatedS
                    do t <- typeItems ks
                       return (Sort_gen [Annoted t nullRange [] []] $ tokPos g)
                      <|> 
                      do o <- oBraceT
                         is <- annosParser (sigItems ks)
                         c <- cBraceT
                         a <- lineAnnos 
                         return (Sort_gen (init is ++ [appendAnno (last is) a])
                                   (toPos g [o] c)) 
             <|> do v <- pluralKeyword varS
                    (vs, ps) <- varItems ks
                    return (Var_items vs (catPos (v:ps)))
             <|> do f <- forallT 
                    (vs, ps) <- varDecl ks `separatedBy` anSemi 
                    a <- annos
                    ai <- dotFormulae ks
                    return (axiomToLocalVarAxioms ai a vs 
                           $ catPos (f:ps))
             <|> dotFormulae ks
             <|> itemList ks axiomS formula Axiom_items

varItems :: [String] -> AParser st ([VAR_DECL], [Token])
varItems ks = 
    do v <- varDecl ks
       do s <- try (addAnnos >> Common.Lexer.semiT) << addLineAnnos
          do   tryItemEnd (ks ++ startKeyword)
               return ([v], [s])
            <|> do (vs, ts) <- varItems ks
                   return (v:vs, s:ts)
         <|> return ([v], [])
             
dotFormulae :: [String] -> AParser st (BASIC_ITEMS B S F)
dotFormulae ks = 
    do d <- dotT
       (fs, ds) <- aFormula ks `separatedBy` dotT
       (m, an) <- optSemi
       let ps = catPos (d:ds) 
           ns = init fs ++ [appendAnno (last fs) an]
       return $ Axiom_items ns (ps `appRange` catPos m)

aFormula  :: [String] -> AParser st (Annoted (FORMULA F))
aFormula ks = bind appendAnno (annoParser $ formula ks) lineAnnos

-- ------------------------------------------------------------------------
-- basicSpec
-- ------------------------------------------------------------------------

basicSpec :: [String] -> AParser st (BASIC_SPEC B S F)
basicSpec ks = (fmap Basic_spec $ annosParser $ basicItems ks)
            <|> (oBraceT >> cBraceT >> return (Basic_spec []))

