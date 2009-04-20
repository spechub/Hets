{- |
Module      :  $Header$
Description :  Parser for first-order logic with dependent types (DFOL)
-}

module DFOL.Parse_AS_DFOL
       (
           basicSpec           -- parser for DFOL specifications
       ,   symbItems           -- parser for symbol lists
       ,   symbMapItems        -- parser for symbol map lists
       )
       where

import qualified Common.Lexer as Lexer
import qualified Common.Keywords as Keywords
import qualified Common.AnnoState as AnnoState
import DFOL.AS_DFOL
import Text.ParserCombinators.Parsec

-- keywords which cannot appear as identifiers in a signature
reserved :: [String]
reserved = [Keywords.trueS,
            Keywords.falseS,
            Keywords.notS,
            Keywords.forallS,
            Keywords.existsS,
            "Univ",
            "Sort",
            "Form",
            "Pi"]

-- parser for basic spec
basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec = fmap Basic_spec (AnnoState.trailingAnnosParser basicItemP)
            <|>
            (Lexer.oBraceT >> Lexer.cBraceT >> (return $ Basic_spec []))

-- parser for basic items
basicItemP :: AnnoState.AParser st BASIC_ITEM
basicItemP = do AnnoState.dotT
                f <- formulaP
                return $ Axiom_item f
             <|>
             do ns <- namesP
                AnnoState.asKey "::"
                t <- typeP
                return $ Decl_item (ns, t)

-- parser for all types
typeP :: AnnoState.AParser st TYPE
typeP = do AnnoState.asKey "Pi"
           vs <- varsP
           t <- typeP
           return $ Pi vs t
        <|>
        do t <- type1P
           (do AnnoState.asKey Keywords.funS
               (ts, _) <- type1P `Lexer.separatedBy` 
                            (AnnoState.asKey Keywords.funS)
               let xs = t:ts
               return $ Func (init xs) (last xs)
            <|>
            return t)

-- parser for basic types and types enclosed in parentheses
type1P :: AnnoState.AParser st TYPE
type1P = do AnnoState.asKey "Sort"
            return Sort
         <|>
         do AnnoState.asKey "Form"
            return Form
         <|>
         do AnnoState.asKey "Univ"
            Lexer.oParenT
            t <- termP
            Lexer.cParenT
            return $ Univ t
         <|>
         do t <- termP
            return $ Univ t
         <|>
         do Lexer.oParenT
            t <- typeP
            Lexer.cParenT
            return t

-- parser for terms
termP :: AnnoState.AParser st TERM
termP = do f <- nameP
           (do Lexer.oParenT
               (as, _) <- termP `Lexer.separatedBy` AnnoState.anComma
               Lexer.cParenT
               return $ Appl (Identifier f) as
            <|>
            do return $ Identifier f)

-- parsers for names
nameP :: AnnoState.AParser st NAME
nameP = Lexer.pToken $ Lexer.reserved reserved Lexer.scanAnyWords

namesP :: AnnoState.AParser st [NAME]
namesP = fmap fst $ nameP `Lexer.separatedBy` AnnoState.anComma

-- parser for variable declarations
varP :: AnnoState.AParser st ([NAME], TYPE)
varP = do ns <- namesP
          AnnoState.asKey Keywords.colonS
          t <- typeP
          return (ns, t)

varsP :: AnnoState.AParser st [([NAME], TYPE)]
varsP = do (vs, _) <- varP `Lexer.separatedBy` (AnnoState.asKey ";")
           AnnoState.dotT
           return vs

-- parser for all formulas
formulaP :: AnnoState.AParser st FORMULA
formulaP = forallP
           <|>
           existsP
           <|>
           formula1P

{- parser for equivalences, implications, conjunctions, disjunctions, 
   negations, equalities, atomic formulas, and formulas in parentheses -}
formula1P :: AnnoState.AParser st FORMULA
formula1P = do f <- formula2P
               (-- equivalences
                do AnnoState.asKey Keywords.equivS
                   g <- formula2P
                   return $ Equivalence f g
                <|>
                -- implications
                do AnnoState.asKey Keywords.implS
                   g <- formula2P
                   return $ Implication f g
                <|>
                -- all other cases
                return f)

{- parser for conjunctions, disjunctions, negations, equalities, 
   atomic formulas, and formulas in parentheses -}
formula2P :: AnnoState.AParser st FORMULA
formula2P = do f <- formula3P
               (-- conjunctions
                do AnnoState.asKey Keywords.lAnd
                   (fs, _) <- formula3P `Lexer.separatedBy` 
                                (AnnoState.asKey Keywords.lAnd)
                   return $ Conjunction (f:fs)
                <|>
                -- disjunctions
                do AnnoState.asKey Keywords.lOr
                   (fs, _) <- formula3P `Lexer.separatedBy` 
                                (AnnoState.asKey Keywords.lOr)
                   return $ Disjunction (f:fs)
                <|>
                -- all other cases
                return f)

{- parser for negations, equalities, atomic formulas, 
   and formulas in parentheses -}
formula3P :: AnnoState.AParser st FORMULA
formula3P = parenFormulaP
            <|>
            negP
            <|>
            formula4P
            <|>
            trueP
            <|>
            falseP

-- parser for equalities and predicate formulas
formula4P :: AnnoState.AParser st FORMULA
formula4P = do x <- termP
               (-- equalities
                do AnnoState.asKey "=="
                   y <- termP
                   return $ Equality x y
                <|>
                -- predicates
                return (Pred x))

-- parser for formulas enclosed in parentheses
parenFormulaP :: AnnoState.AParser st FORMULA
parenFormulaP = do Lexer.oParenT
                   f <- formulaP
                   Lexer.cParenT
                   return f

-- parser for forall formulas
forallP :: AnnoState.AParser st FORMULA
forallP = do AnnoState.asKey Keywords.forallS
             vs <- varsP
             f <- formulaP
             return $ Forall vs f

-- parser for exists formulas
existsP :: AnnoState.AParser st FORMULA
existsP = do AnnoState.asKey Keywords.existsS
             vs <- varsP
             f <- formulaP
             return $ Exists vs f

-- parser for negations
negP :: AnnoState.AParser st FORMULA
negP = do AnnoState.asKey Keywords.negS <|> AnnoState.asKey Keywords.notS
          f <- formula3P
          return $ Negation f

-- parser for true
trueP :: AnnoState.AParser st FORMULA
trueP = do AnnoState.asKey Keywords.trueS
           return $ T

-- parser for false
falseP :: AnnoState.AParser st FORMULA
falseP = do AnnoState.asKey Keywords.falseS
            return $ F

-- parser for symbol items
symbItems :: AnnoState.AParser st SYMB_ITEMS
symbItems = fmap Symb_items $ namesP

-- parser for symbol map items
symbMapItems :: AnnoState.AParser st SYMB_MAP_ITEMS
symbMapItems = do (xs, _) <- symbOrMap `Lexer.separatedBy` AnnoState.anComma
                  return $ Symb_map_items xs

-- parser for symbols or symbol maps
symbOrMap :: AnnoState.AParser st SYMB_OR_MAP
symbOrMap = do s <- nameP
               (do AnnoState.asKey Keywords.mapsTo
                   t <- nameP
                   return $ Symb_map s t
                <|>
                return (Symb s))
