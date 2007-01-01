{- |
   Module      :  $Header$
   Copyright   :  (c) Maciek Makowski, Warsaw University 2003-2004, C. Maeder
   License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
   Maintainer  :  maeder@tzi.de
   Stability   :  provisional
   Portability :  non-portable (via imports)

   Description :  parser for CASL architectural specifications

   Follows Sect. II:3.1.4 of the CASL Reference Manual plus refinement
   extensions

   TODO:
    check UNIT-BINDING
-}

module Syntax.Parse_AS_Architecture where

import Logic.Grothendieck
import Logic.Logic
import Syntax.AS_Structured
import Syntax.AS_Architecture
import Syntax.Parse_AS_Structured
import Common.AS_Annotation
import Common.AnnoState
import Common.Keywords
import Common.Lexer
import Common.Token
import Text.ParserCombinators.Parsec
import Common.Id

------------------------------------------------------------------------
-- * Parsing functions


-- | Parse annotated architectural specification
annotedArchSpec :: LogicGraph -> AParser AnyLogic (Annoted ARCH_SPEC)
annotedArchSpec l = annoParser2 (archSpec l)


-- | Parse architectural specification
-- @
-- ARCH-SPEC ::= BASIC-ARCH-SPEC | GROUP-ARCH-SPEC
-- @
archSpec :: LogicGraph -> AParser AnyLogic (Annoted ARCH_SPEC)
archSpec l =
    do asp <- basicArchSpec l
       return asp
    <|>
    do asp <- groupArchSpec l
       return asp


-- | Parse group architectural specification
-- @
-- GROUP-ARCH-SPEC ::= { ARCH-SPEC } | ARCH-SPEC-NAME
-- @
groupArchSpec :: LogicGraph -> AParser AnyLogic (Annoted ARCH_SPEC)
groupArchSpec l =
    do kOpBr <- oBraceT
       asp <- annoParser $ archSpec l
       kClBr <- cBraceT
       return (replaceAnnoted
               (Group_arch_spec (item asp) $ toPos kOpBr [] kClBr) asp)
    <|>
    do name <- simpleId
       return (emptyAnno $ Arch_spec_name name)


-- | Parse basic architectural specification
-- @
-- BASIC-ARCH-SPEC ::= unit/units UNIT-DECL-DEFNS
--                                result UNIT-EXPRESSION ;/
-- @
basicArchSpec :: LogicGraph -> AParser AnyLogic (Annoted ARCH_SPEC)
basicArchSpec l =
    do kUnit <- pluralKeyword unitS
       (declDefn, ps) <- auxItemList [resultS] [] (unitDeclDefn l) (,)
       kResult <- asKey resultS
       expr <- annoParser2 $ unitExpr l
       (m, an) <- optSemi
       return (emptyAnno $ Basic_arch_spec declDefn (appendAnno expr an)
                     (tokPos kUnit `appRange` ps `appRange` catPos (kResult:m)))

-- | Parse unit declaration or definition
-- @
-- UNIT-DECL-DEFN ::= UNIT-DECL | UNIT-DEFN
-- @
unitDeclDefn :: LogicGraph -> AParser AnyLogic UNIT_DECL_DEFN
unitDeclDefn l = do
    name <- simpleId
    do c <- colonT     -- unit declaration
       decl <- refSpec l
       (gs, ps) <- option ([], []) $
         do kGiven <- asKey givenS
            (guts, qs) <- groupUnitTerm l `separatedBy` anComma
            return (guts, kGiven:qs)
       return (Unit_decl name decl gs $ catPos (c:ps))
     <|> -- unit definition
     unitDefn' l name

-- | Parse unit declaration
-- @
-- UNIT-REF ::= UNIT-NAME : REF-SPEC
-- @
unitRef :: LogicGraph -> AParser AnyLogic UNIT_REF
unitRef l =
        do name <- simpleId
           sep1 <- asKey toS
           usp <- refSpec l
           return $ Unit_ref name usp $ tokPos sep1


-- | Parse unit specification
-- @
-- UNIT-SPEC ::= GROUP-SPEC
--             | GROUP-SPEC * .. * GROUP-SPEC -> GROUP-SPEC
--             | closed UNIT-SPEC
-- @
unitSpec :: LogicGraph -> AParser AnyLogic UNIT_SPEC
unitSpec l =
       -- closed unit spec
    do kClosed <- asKey closedS
       uSpec <- unitSpec l
       return (Closed_unit_spec uSpec $ tokPos kClosed)
    <|> -- unit type
{- NOTE: this can also be a spec name. If this is the case, this unit spec
           will be converted on the static analysis stage.
           See Static.AnalysisArchitecture.ana_UNIT_SPEC. -}
    do gps@(gs:gss, _) <- annoParser (groupSpec l) `separatedBy` crossT
       let rest = unitRestType l gps
       if null gss then do
            option ( {- case item gs of
                    Spec_inst sn [] _ -> Spec_name sn -- annotations are lost
                    _ -> -} Unit_type [] gs nullRange) rest
            else rest

unitRestType :: LogicGraph -> ([Annoted SPEC], [Token])
             -> AParser AnyLogic UNIT_SPEC
unitRestType l (gs, ps) = do
    a <- asKey funS
    g <- annoParser $ groupSpec l
    return (Unit_type gs g $ catPos (ps ++ [a]))

refSpec :: LogicGraph -> AParser AnyLogic REF_SPEC
refSpec l = do
      (rs, ps) <- basicRefSpec l `separatedBy` (asKey thenS)
      return $ if isSingle rs then head rs
         else Compose_ref rs $ catPos ps

-- | Parse refinement specification
-- @
-- REF-SPEC ::= UNIT_SPEC
--             | UNIT_SPEC [bahav..] refined [via SYMB-MAP-ITEMS*] to REF-SPEC
--             | arch spec GROUP-ARCH-SPEC
--             | { UNIT-DECL, ..., UNIT-DECL }
-- @
basicRefSpec :: LogicGraph -> AParser AnyLogic REF_SPEC
basicRefSpec l = -- component spec
    do o <- oBraceT `followedWith` (simpleId >> asKey toS)
       (us, ps) <- unitRef l `separatedBy` anComma
       c <- cBraceT
       return (Component_ref us $ toPos c ps o)
    <|> -- unit spec
    do uSpec <- unitSpec l
       refinedRestSpec l uSpec <|> return (Unit_spec uSpec)
    <|> -- architectural spec
    do kArch <- asKey archS
       kSpec <- asKey specS
       asp <- groupArchSpec l
       return (Arch_unit_spec asp (toPos kArch [] kSpec))


refinedRestSpec :: LogicGraph -> UNIT_SPEC -> AParser AnyLogic REF_SPEC
refinedRestSpec l u = do
      b <- asKey behaviourallyS
      onlyRefinedRestSpec l (tokPos b) u
    <|> onlyRefinedRestSpec l nullRange u

onlyRefinedRestSpec :: LogicGraph -> Range -> UNIT_SPEC ->
                       AParser AnyLogic REF_SPEC
onlyRefinedRestSpec l b u = do
    r <- asKey refinedS
    (ms, ps) <- option ([], []) $ do
                 v <- asKey viaS -- not a keyword
                 (m, ts) <- parseMapping l
                 return (m, v : ts)
    t <- asKey toS
    rsp <- refSpec l
    return $ Refinement (isNullRange b) u ms rsp (b `appRange` toPos r ps t)

-- | Parse group unit term
-- @
-- GROUP-UNIT-TERM ::= UNIT-NAME
--                   | UNIT-NAME FIT-ARG-UNITS
--                   | { UNIT-TERM }
-- @
groupUnitTerm :: LogicGraph -> AParser AnyLogic (Annoted UNIT_TERM)
groupUnitTerm l = annoParser $
        -- unit name/application
    do name <- simpleId
       args <- many (fitArgUnit l)
       return (Unit_appl name args nullRange)
    <|> -- unit term in brackets
    do lbr <- oBraceT
       ut <- unitTerm l
       rbr <- cBraceT
       return (Group_unit_term ut (catPos [lbr, rbr]))

-- | Parse an argument for unit application.
-- @
-- FIT-ARG-UNIT ::= [ UNIT-TERM ]
--                | [ UNIT-TERM fit SYMB-MAP-ITEMS-LIST ]
-- @
-- The SYMB-MAP-ITEMS-LIST is parsed using parseItemsMap.
fitArgUnit :: LogicGraph -> AParser AnyLogic FIT_ARG_UNIT
fitArgUnit l =
    do o <- oBracketT
       ut <- unitTerm l
       (fargs, qs) <- option ([], [])
                       (do kFit <- asKey fitS
                           (smis, ps) <- parseMapping l
                           return (smis, kFit:ps))
       c <- cBracketT
       return $ Fit_arg_unit ut fargs $ toPos o qs c


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
unitTerm :: LogicGraph -> AParser AnyLogic (Annoted UNIT_TERM)
unitTerm l = unitTermAmalgamation l


-- | Parse unit amalgamation.
-- @
-- UNIT-TERM-AMALGAMATION ::= UNIT-TERM-LOCAL and ... and UNIT-TERM-LOCAL
-- @
unitTermAmalgamation :: LogicGraph -> AParser AnyLogic (Annoted UNIT_TERM)
unitTermAmalgamation l =
    do (uts, toks) <- annoParser2 (unitTermLocal l) `separatedBy` (asKey andS)
       return (case uts of
               [ut] -> ut
               _ -> emptyAnno (Amalgamation uts (catPos toks)))


-- | Parse local unit term
-- @
-- UNIT-TERM-LOCAL ::= local UNIT-DEFNS within UNIT-TERM-LOCAL
--                   | UNIT-TERM-TRANS-RED
-- @
unitTermLocal :: LogicGraph -> AParser AnyLogic (Annoted UNIT_TERM)
unitTermLocal l =
        -- local unit
    do kLocal <- asKey localS
       (uDefns, ps) <- auxItemList [withinS] [] (unitDefn l) (,)
       kWithin <- asKey withinS
       uTerm <- unitTermLocal l
       return (emptyAnno $ Local_unit uDefns uTerm
                         (tokPos kLocal `appRange` ps `appRange` tokPos kWithin))
    <|> -- translation/reduction
    do ut <- unitTermTransRed l
       return ut


-- | Parse translation or reduction unit term
-- The original grammar
-- @
-- UNIT-TERM-TRANS-RED ::= UNIT-TERM-TRANS-RED RENAMING
--                       | UNIT-TERM-TRANS-RED RESTRICTION
--                       | GROUP-UNIT-TERM
-- @

unitTermTransRed :: LogicGraph -> AParser AnyLogic (Annoted UNIT_TERM)
unitTermTransRed l = groupUnitTerm l >>=
    translation_list l Unit_translation Unit_reduction

-- | Parse unit expression
-- @
-- UNIT-EXPRESSION ::= lambda UNIT-BINDINGS "." UNIT-TERM
--                   | UNIT-TERM
-- @
unitExpr :: LogicGraph -> AParser AnyLogic (Annoted UNIT_EXPRESSION)
unitExpr l =
         do (bindings, poss) <- option ([], nullRange)
             (do kLambda <- asKey lambdaS
                 (bindings, poss) <- unitBinding l `separatedBy` anSemi
                 kDot <- dotT
                 return (bindings, toPos kLambda poss kDot))
            ut <- unitTerm l
            return (emptyAnno $ Unit_expression bindings ut poss)

-- | Parse unit binding
-- @
-- UNIT-BINDING ::= UNIT-NAME : UNIT-SPEC
-- @
unitBinding :: LogicGraph -> AParser AnyLogic UNIT_BINDING
unitBinding l =
    do name <- simpleId
       kCol <- colonT
       usp <- unitSpec l
       return (Unit_binding name usp $ tokPos kCol)

-- | Parse an unit definition
-- @
-- UNIT-DEFN ::= UNIT-NAME = UNIT-EXPRESSION
-- @
unitDefn :: LogicGraph -> AParser AnyLogic UNIT_DECL_DEFN
unitDefn l = simpleId >>= unitDefn' l

unitDefn' :: LogicGraph -> SIMPLE_ID -> AParser AnyLogic UNIT_DECL_DEFN
unitDefn' l name = do
       kEqu <- equalT
       expr <- annoParser2 $ unitExpr l
       return (Unit_defn name (item expr) $ tokPos kEqu)
