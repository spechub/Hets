{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Preprocessor for sentences written in some logic.
   The sentences are replaced with corresponding abstract syntax trees in Haskell.
   This frees the programmer from writing AS tree expressions.

   The syntax for inline sentences is

      inlineAxioms <logic-name> <basic-spec>

   where <logic-name> must be a logic in the logic graph, and <basic-spec> a
   basic specification in that logic. Only the sentences are extracted from
   the basic specification, but the used identifiers must be declared.
   Identifiers are left as Haskell variables, which means that they must
   be bound by the enclosing expression. E.g.

generateAxioms :: Sign f e -> [Named (FORMULA f)]
generateAxioms sig = 
  concat [inlineAxioms CASL
            "  sorts s < s'; op inj : s->s' \
             \ forall x,y:s . inj(x)=inj(y) => x=y  %(ga_embedding_injectivity)% "
           | (s,s') <- Rel.toList (sortRel sig)]
  where x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = mkId [mkSimpleId "_inj"]

-}

module Main where -- Comorphisms.PreProcessor where

import Haskell.Hatchet.HsPretty as HP
import Haskell.Hatchet.HsSyn
import Haskell.Haskell2DG

import Common.GlobalAnnotations 
import Common.AnnoState
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.Lib.Parsec
import Common.Result

import System
import System.Console.GetOpt
import Data.List

import Comorphisms.LogicGraph
import Logic.Logic
import Logic.Grothendieck

instance PrettyPrint HsModule where
    printText0 _ m = text $ HP.render $ ppHsModule m

-- hack: delete position info of form "[nlineAxioms ...]", replace with "[]"
deletePos :: String -> String
deletePos s = reverse (deletePos1 s "")
  where 
  deletePos1 "" acc = acc
  deletePos1 ('[':'i':'n':'l':'i':'n':'e':'A':'x':'i':'o':'m':'s':s1) acc =
    deletePos1 (skipBra s1) (']':'[':acc)
  deletePos1 (c:s1) acc = deletePos1 s1 (c:acc)
  skipBra "" = ""
  skipBra (']':s2) = s2
  skipBra (_:s2) = skipBra s2

-- parse inline for Haskell decls and exps

piHsFieldUpdate :: HsFieldUpdate -> HsFieldUpdate
piHsFieldUpdate (HsFieldUpdate qn expr) = HsFieldUpdate qn (piHsExp expr)

piHsStmt :: HsStmt -> HsStmt
piHsStmt (HsGenerator loc pat expr) = HsGenerator loc pat (piHsExp expr)
piHsStmt (HsQualifier expr) = HsQualifier (piHsExp expr)
piHsStmt (HsLetStmt decls) = HsLetStmt (map piHsDecl decls)

piHsGuardedAlt :: HsGuardedAlt -> HsGuardedAlt
piHsGuardedAlt (HsGuardedAlt loc expr1 expr2) =
  HsGuardedAlt loc (piHsExp expr1) (piHsExp expr2)

piHsGuardedAlts :: HsGuardedAlts -> HsGuardedAlts
piHsGuardedAlts (HsUnGuardedAlt expr) = HsUnGuardedAlt (piHsExp expr)
piHsGuardedAlts (HsGuardedAlts alts) = HsGuardedAlts (map piHsGuardedAlt alts)

piHsAlt :: HsAlt -> HsAlt
piHsAlt (HsAlt loc pat alts decls) =
  HsAlt loc pat (piHsGuardedAlts alts) (map piHsDecl decls)

piHsExp :: HsExp -> HsExp
piHsExp (HsInfixApp expr1 expr2 expr3) =
  HsInfixApp (piHsExp expr1) (piHsExp expr2) (piHsExp expr3)
piHsExp (HsApp (HsApp (HsVar (UnQual (HsIdent "inlineAxioms"))) 
                      (HsCon (UnQual (HsIdent logStr)))) 
               (HsLit (HsString str))) =
  case lookupLogic "inlineAxioms: " logStr logicGraph of
    Logic lid -> case parse_basic_spec lid of
      Nothing -> error ("No parser for logic "++logStr)
      Just p -> case runParser p emptyAnnos "inlineAxioms" str of
        Left err -> error (show err)
        Right ast -> case basic_analysis lid of
          Nothing -> error ("No static analysis for logic "++logStr)
          Just b -> case maybeResult $ b (ast,empty_signature lid,emptyGlobalAnnos) of
            Nothing -> error "Error during static analysis of inlineAxioms"
            Just (_,_,_,sens) ->
               HsVar (UnQual (HsIdent (deletePos $ show sens)))
piHsExp (HsApp expr1 expr2) =
  HsApp (piHsExp expr1) (piHsExp expr2)
piHsExp (HsNegApp expr) =
  HsNegApp (piHsExp expr)
piHsExp (HsLambda loc pats expr) =
  HsLambda loc pats (piHsExp expr)
piHsExp (HsLet decls expr) =
  HsLet (map piHsDecl decls) (piHsExp expr)
piHsExp (HsIf expr1 expr2 expr3) =
  HsIf (piHsExp expr1) (piHsExp expr2) (piHsExp expr3)
piHsExp (HsCase expr alts) = HsCase (piHsExp expr) (map piHsAlt alts)
piHsExp (HsDo stmts) = HsDo (map piHsStmt stmts)
piHsExp (HsTuple exprs) = HsTuple (map piHsExp exprs)
piHsExp (HsList exprs) = HsList (map piHsExp exprs) 
piHsExp (HsParen expr) = HsParen (piHsExp expr)
piHsExp (HsLeftSection expr1 expr2) = HsLeftSection (piHsExp expr1) (piHsExp expr2)
piHsExp (HsRightSection expr1 expr2) =  HsRightSection (piHsExp expr1) (piHsExp expr2)
piHsExp (HsRecConstr qn fields) = HsRecConstr qn (map piHsFieldUpdate fields)
piHsExp (HsRecUpdate expr fields) = 
  HsRecUpdate (piHsExp expr) (map piHsFieldUpdate fields)
piHsExp (HsEnumFrom expr) = HsEnumFrom (piHsExp expr)
piHsExp (HsEnumFromTo expr1 expr2) = HsEnumFromTo (piHsExp expr1) (piHsExp expr2)
piHsExp (HsEnumFromThen expr1 expr2) = HsEnumFromThen (piHsExp expr1) (piHsExp expr2)
piHsExp (HsEnumFromThenTo expr1 expr2 expr3) = 
  HsEnumFromThenTo (piHsExp expr1) (piHsExp expr2) (piHsExp expr3)
piHsExp (HsListComp expr stmts) = HsListComp (piHsExp expr) (map piHsStmt stmts)
piHsExp (HsExpTypeSig loc expr qt) = HsExpTypeSig loc (piHsExp expr) qt
piHsExp expr = expr

piHsGuardedRhs :: HsGuardedRhs ->HsGuardedRhs
piHsGuardedRhs (HsGuardedRhs loc expr1 expr2) =
  HsGuardedRhs loc (piHsExp expr1) (piHsExp expr2)

piHsRhs :: HsRhs -> HsRhs
piHsRhs (HsUnGuardedRhs expr) = HsUnGuardedRhs (piHsExp expr)
piHsRhs (HsGuardedRhss rhss) = HsGuardedRhss (map piHsGuardedRhs rhss)

piHsMatch :: HsMatch -> HsMatch
piHsMatch (HsMatch loc qn pats rhs decls) =
  HsMatch loc qn pats (piHsRhs rhs) decls

piHsDecl :: HsDecl -> HsDecl
piHsDecl (HsFunBind ms) = HsFunBind (map piHsMatch ms)
piHsDecl decl = decl

parseInline :: HsModule -> HsModule
parseInline (HsModule modu expr imp decls) =
  HsModule modu expr imp (map piHsDecl decls)


processFile :: String -> IO ()
processFile file = do
  let f = case findIndex (=='.') file of
           Nothing -> file
           Just n -> take n file
      infile = f++".inline.hs"
      outfile = f++".hs"
  putStrLn ("Preprocessing inline axioms in "++infile)
  decls <- parseFile infile
  let decls' = parseInline decls
      decls'' = parseHsSource (showPretty decls' "")
  writeFile outfile $! showPretty decls'' "" 
     -- $! ensures that file is only written if some value is delivered

main :: IO ()
main = do args <- getArgs
          case (getOpt RequireOrder opts args) of
            (_,files@(_:_),[]) -> do 
              mapM processFile files
              return ()
            (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header opts))
          where header = "Usage: inlineAxioms file [file ...]"
                opts = [] -- no options