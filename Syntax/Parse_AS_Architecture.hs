{- |
   Module     : $Header$
   Author     : Maciek Makowski
   Maintainer : m.makowski@students.mimuw.edu.pl
   Year       : 2003

   Parsing the architectural part of heterogenous specifications.
   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.3 Structured Specifications

   TODO:
   - make sure the precedence is OK
   - annotations
   > see specific TODOs in functions
-}

module Syntax.Parse_AS_Architecture where

import Logic.Grothendieck
import Logic.Logic

import CASL.Logic_CASL  -- we need the default logic

import Syntax.AS_Structured
import Syntax.AS_Architecture
import Syntax.AS_Library
import Syntax.Parse_AS_Structured
import Common.AS_Annotation
import Common.AnnoState
import Common.Id(tokPos)
import Common.Keywords
import Common.Lexer
import Common.Token
import Common.Lib.Parsec
import Common.Lib.Parsec.Char (digit)
import qualified Common.Lib.Map as Map
import Common.Id
import Data.List

import Data.Maybe(maybeToList)


------------------------------------------------------------------------
-- * Parsing functions


-- | Parse annotated architectural specification
annotedArchSpec :: (AnyLogic, LogicGraph) -> AParser (Annoted ARCH_SPEC)
annotedArchSpec l@(log, lG) = annoParser2 (archSpec l)


-- | Parse architectural specification
-- @
-- ARCH-SPEC ::= BASIC-ARCH-SPEC | GROUP-ARCH-SPEC
-- @
-- TODO: groupArchSpec
archSpec :: (AnyLogic, LogicGraph) -> AParser (Annoted ARCH_SPEC)
archSpec l = basicArchSpec l


-- | Parse basic architectural specification
-- @
-- BASIC-ARCH-SPEC ::= unit/units UNIT-DECL-DEFNS
--                                result UNIT-EXPRESSION ;/
-- @
basicArchSpec :: (AnyLogic, LogicGraph) -> AParser (Annoted ARCH_SPEC)
basicArchSpec l = 
    do kUnit <- (do u <- asKey unitS; return u) <|> (do u <- asKey "units"; return u) -- TODO: more elegant
       declDefn <- unitDeclDefns l
       kResult <- asKey resultS
       expr <- unitExpr l
       kSc <- option Nothing (fmap Just (asKey ";"))
       return (Annoted (Syntax.AS_Architecture.Basic_arch_spec declDefn expr
			    (map tokPos ([kUnit, kResult] ++ maybeToList kSc))) 
	                [] [] [])


-- | Parse a nonempty list of unit declarations/definitions separated by
-- semicolons, with optional semicolon at the end.
-- @
-- UNIT-DECL-DEFNS ::= UNIT-DECL-DEFN ; ... ; UNIT-DECL-DEFN ;/
-- @
unitDeclDefns :: (AnyLogic, LogicGraph) -> AParser [Annoted UNIT_DECL_DEFN]
unitDeclDefns l =
    do dd <- unitDeclDefn l
       ann <- annos
       dds <- option []
	      (do sc <- asKey ";"
		  dds <- option [] (unitDeclDefns l)
	          return dds)
       return ((Annoted dd [] [] ann) : dds)


-- | Parse unit declaration/definition
-- @
-- UNIT-DECL-DEFN ::= UNIT-DECL | UNIT-DEFN
-- @
unitDeclDefn :: (AnyLogic, LogicGraph) -> AParser UNIT_DECL_DEFN
unitDeclDefn l = 
        -- unit declaration 
    do decl <- unitDecl l
       return decl
    <|> -- unit definition
    do defn <- unitDefn l
       return defn



-- | Parse unit declaration
-- @
-- UNIT-DECL ::= UNIT-NAME : UNIT-SPEC
--             | UNIT-NAME : UNIT-SPEC given GROUP-UNIT-TERMS
-- @
unitDecl :: (AnyLogic, LogicGraph) -> AParser UNIT_DECL_DEFN
unitDecl l = 
        do name <- simpleId
	   sep1 <- asKey ":"
	   spec <- unitSpec l
	   (kGiven, guts) <- option (Nothing, [])
			     (do kGiven <- fmap Just (asKey givenS)
				 guts <- groupUnitTerms l
				 return (kGiven, guts))
	   return (Syntax.AS_Architecture.Unit_decl name spec guts
		       (map tokPos (sep1 : maybeToList kGiven)))


-- | Parse unit specification
-- @
-- UNIT-SPEC ::= SPEC-NAME
--             | GROUP-SPECS( * ... * GROUP-SPEC) -> GROUP-SPEC
--             | arch spec GROUP-ARCH-SPEC
--             | closed UNIT-SPEC
-- @
-- TODO: is the grammar OK? (differs from one in the CASL docs)
-- TODO: other cases
unitSpec :: (AnyLogic, LogicGraph) -> AParser UNIT_SPEC
unitSpec l =
        -- specification name 
    do name <- simpleId
       return (Syntax.AS_Architecture.Spec_name name)
    <|> -- specification type
    do (gss, poss) <- groupSpecs l
       gs <- groupSpec l
       return (Syntax.AS_Architecture.Unit_type gss (emptyAnno gs) poss)


-- | Parse a (possibly empty) list of group specs separated by "*"
-- and ending with "->".
-- @
-- GROUP-SPECS ::= GROUP-SPEC * ... * GROUP-SPEC ->
-- @
groupSpecs :: (AnyLogic, LogicGraph) -> AParser ([Annoted SPEC], [Pos])
-- ^ returns the list of (annotated) group specs and a list of "*" and 
-- "->" positions
groupSpecs l = 
    do return ([], [])
    <|> 
    do kFun <- asKey funS
       return ([], map tokPos [kFun])
    <|>
    do gs <- groupSpec l
       kAst <- asKey prodS
       (gss, poss) <- groupSpecs l
       return ((emptyAnno gs) : gss, (tokPos kAst) : poss)


-- | Parse a nonempty list of group unit terms separated by commas.
-- The positions of commas are stored in annotations.
-- @
-- GROUP-UNIT-TERMS ::= GROUP-UNIT-TERM ,..., GROUP-UNIT-TERM
-- @
-- TODO: remember comma positions in [Pos] one level higher,
--       not in annotations (?)
groupUnitTerms :: (AnyLogic, LogicGraph) -> AParser [Annoted UNIT_TERM]
groupUnitTerms l =
    do gut <- groupUnitTerm l
       (com, guts) <- option (Nothing, [])
		      (do com <- fmap Just (asKey ",")
			  guts <- groupUnitTerms l
			  return (com, guts))
       return ((Annoted gut (map tokPos (maybeToList com)) [] []) : guts)
		     

-- | Parse group unit term
-- @
-- GROUP-UNIT-TERM ::= UNIT-NAME
--                   | UNIT-NAME FIT-ARG-UNITS
--                   | { UNIT-TERM }
-- @
groupUnitTerm :: (AnyLogic, LogicGraph) -> AParser UNIT_TERM
groupUnitTerm l =
        -- unit name/application
    do name <- simpleId
       (args, pos) <- fitArgUnits l
       return (Syntax.AS_Architecture.Unit_appl name args pos)
    <|> -- unit term in brackets
    do lbr <- asKey "{"
       ut <- unitTerm l
       rbr <- asKey "}"
       return (Syntax.AS_Architecture.Group_unit_term ut (map tokPos [lbr, rbr]))


-- | Parse the (possibly empty) list of arguments for unit application.
-- @
-- FIT-ARG-UNITS ::= [ FIT-ARG-UNIT ] ... [ FIT-ARG-UNIT ]
-- @
fitArgUnits :: (AnyLogic, LogicGraph) -> AParser ([FIT_ARG_UNIT], [Pos])
-- ^ returns a list of arguments for unit application and a list of 
-- "[" and "]" positions
fitArgUnits l = 
    option ([], []) 
    (do opBr <- asKey "["
	fau <- fitArgUnit l
	clBr <- asKey "]"
        (faus, poss) <- fitArgUnits l
        return (fau : faus, [tokPos opBr, tokPos clBr] ++ poss))


-- | Parse an argument for unit application.
-- @
-- FIT-ARG-UNIT ::= UNIT-TERM
--                | UNIT-TERM fit SYMB-MAP-ITEMS-LIST
-- @
-- The SYMB-MAP-ITEMS-LIST is parsed using parseItemsMap.
-- TODO: use current logic (fst l) instead of CASL in empty map
fitArgUnit :: (AnyLogic, LogicGraph) -> AParser FIT_ARG_UNIT
fitArgUnit l = 
    do ut <- unitTerm l
       (kFit, smis) <- option (Nothing, G_symb_map_items_list CASL [])
		       (do kFit <- fmap Just (asKey fitS)
			   (smis, _) <- parseItemsMap (fst l)
			   return (kFit, smis))
       return (Syntax.AS_Architecture.Fit_arg_unit ut smis 
	           (map tokPos (maybeToList kFit)))


-- | Parse unit term.
-- @
-- UNIT-TERM ::= UNIT-TERM RENAMING
--             | UNIT-TERM RESTRICTION
--             | UNIT-TERM and ... and UNIT-TERM
--             | local UNIT-DEFNS within UNIT-TERM
--             | GROUP-UNIT-TERM
-- @
-- This will be done by subsequent functions in order to preserve
-- the operator precedence; see other 'unitTerm*' functions.
unitTerm :: (AnyLogic, LogicGraph) -> AParser (Annoted UNIT_TERM)
unitTerm l = unitTermAmalgamation l


-- | Parse unit amalgamation.
-- @
-- UNIT-TERM-AMALGAMATION ::= UNIT-TERM-LOCAL and ... and UNIT-TERM-LOCAL
-- @
unitTermAmalgamation :: (AnyLogic, LogicGraph) -> AParser (Annoted UNIT_TERM)
unitTermAmalgamation l = 
    do (uts, toks) <- annoParser2 (unitTermLocal l) `separatedBy` (asKey andS)
       return (case uts of
	       [ut] -> ut
	       otherwise -> emptyAnno (Amalgamation uts (map tokPos toks)))


-- | Parse local unit term
-- @
-- UNIT-TERM-LOCAL ::= local UNIT-DEFNS within UNIT-TERM-LOCAL
--                   | UNIT-TERM-TRANS-RED
-- @
unitTermLocal :: (AnyLogic, LogicGraph) -> AParser (Annoted UNIT_TERM)
unitTermLocal l =
        -- local unit
    do kLocal <- asKey localS
       uDefns <- unitDefns l
       kWithin <- asKey withinS
       uTerm <- unitTermLocal l
       return (Annoted (Syntax.AS_Architecture.Local_unit uDefns uTerm
			    (map tokPos [kLocal, kWithin]))
	               [] [] [])
    <|> -- translation/reduction
    do ut <- unitTermTransRed l
       return ut


-- | Parse translation/reduction unit term
-- The original grammar
-- @
-- UNIT-TERM-TRANS-RED ::= UNIT-TERM-TRANS-RED RENAMING
--                       | UNIT-TERM-TRANS-RED RESTRICTION
--                       | GROUP-UNIT-TERM
-- @
-- has been rewritten to
-- @
-- UNIT-TERM-TRANS-RED  ::= GROUP-UNIT-TERM UNIT-TERM-TRANS-RED'
-- UNIT-TERM-TRANS-RED' ::= RENAMING UNIT-TERM-TRANS-RED'
--                        | RESTRICTION UNIT-TERM-TRANS-RED'
--                        | EPSILON
-- @
-- in order to eliminate left-hand-side recursion.
unitTermTransRed :: (AnyLogic, LogicGraph) -> AParser (Annoted UNIT_TERM)
unitTermTransRed l =
    do ut <- groupUnitTerm l
       tr <- unitTermTransRed' l (emptyAnno ut)
       return tr

-- | Parse the helper unit term productions
unitTermTransRed' :: (AnyLogic, LogicGraph) 
    -> Annoted UNIT_TERM           -- ^ the unit term that came before the renaming/restriction clause
    -> AParser (Annoted UNIT_TERM) -- ^ the resulting unit term
unitTermTransRed' l ut =
        -- translation
    do ren <- renaming l
       ut' <- unitTermTransRed' l (emptyAnno (Unit_translation ut ren))
       return ut'
    <|> -- reduction
    do res <- restriction l
       ut' <- unitTermTransRed' l (emptyAnno (Unit_reduction ut res))       
       return ut'
    <|> -- epsilon
    do return ut


-- | Parse renaming
-- @
-- RENAMING ::= with SYMB-MAP-ITEMS-LIST
-- @
-- SYMB-MAP-ITEMS-LIST is parsed using parseMapping
renaming :: (AnyLogic, LogicGraph) -> AParser RENAMING
renaming l =
    do kWith <- asKey withS
       (mappings, commas) <- parseMapping l
       return (Renaming mappings (map tokPos (kWith : commas)))


-- | Parse restriction
-- @
-- RESTRICTION ::= hide SYMB-ITEMS-LIST
--               | reveal SYMB-MAP-ITEMS-LIST
-- @
-- SYMB-ITEMS-LIST is parsed using parseHiding; SYMB-MAP-ITEMS-LIST is 
-- parsed using parseItemsMap
restriction :: (AnyLogic, LogicGraph) -> AParser RESTRICTION
restriction l =
        -- hide
    do kHide <- asKey hideS
       (symbs, commas) <- parseHiding l
       return (Hidden symbs (map tokPos (kHide : commas)))
    <|> -- reveal
    do kReveal <- asKey revealS
       (mappings, commas) <- parseItemsMap (fst l)
       return (Revealed mappings (map tokPos (kReveal : commas)))


-- | Parse unit expression
-- @
-- UNIT-EXPRESSION ::= lambda UNIT-BINDINGS "." UNIT-TERM
--                   | UNIT-TERM 
-- @
unitExpr :: (AnyLogic, LogicGraph) -> AParser (Annoted UNIT_EXPRESSION)
unitExpr l =
         do (bindings, poss) <- option ([], [])
				(do kLambda <- asKey lambdaS
				    (bindings, poss) <- unitBindings l
				    kDot <- asKey dotS
				    return (bindings,
					    [tokPos kLambda] ++ poss ++ [tokPos kDot]))
	    ut <- unitTerm l
	    return (Annoted (Syntax.AS_Architecture.Unit_expression bindings ut poss) [] [] [])


-- | Parse a nonempty list of unit bindings separated by
-- semicolons.
unitBindings :: (AnyLogic, LogicGraph) -> AParser ([UNIT_BINDING], [Pos])
-- ^ returns the list of unit bindings and a list of semicolon positions
unitBindings l =
    do ub <- unitBinding l
       (ubs, poss) <- option ([], [])
		          (do sc <- asKey ";"
		              (ubs, poss) <- unitBindings l
			      return (ubs, (tokPos sc) : poss))
       return (ub : ubs, poss)


-- | Parse unit binding
-- @
-- UNIT-BINDING ::= UNIT-NAME : UNIT-SPEC
-- @
unitBinding :: (AnyLogic, LogicGraph) -> AParser UNIT_BINDING
unitBinding l =
    do name <- simpleId
       kCol <- asKey colonS
       spec <- unitSpec l
       return (Syntax.AS_Architecture.Unit_binding name spec [tokPos kCol])


-- | Parse a nonempty list of unit definitions separated by
-- semicolons, with optional semicolon at the end.
-- @
-- UNIT-DEFNS ::= UNIT-DEFN ; ... ; UNIT-DEFN ;/
-- @
unitDefns :: (AnyLogic, LogicGraph) -> AParser [Annoted UNIT_DECL_DEFN]
unitDefns l =
    do ud <- unitDefn l
       ann <- annos
       uds <- option []
	      (do sc <- asKey ";"
		  uds <- option [] (unitDefns l)
	          return uds)
       return ((Annoted ud [] [] ann) : uds)


-- | Parse an unit definition
-- @
-- UNIT-DEFN ::= UNIT-NAME = UNIT-EXPRESSION
-- @
unitDefn :: (AnyLogic, LogicGraph) -> AParser UNIT_DECL_DEFN
unitDefn l =
    do name <- simpleId
       kEqu <- asKey equalS
       expr <- unitExpr l
       return (Syntax.AS_Architecture.Unit_defn name (item expr) (map tokPos [kEqu]))

