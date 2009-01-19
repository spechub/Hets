{- |
Module      :  $Id$
Copyright   :  (c) T.Mossakowski, C.Maeder, K.Luettich, Uni Bremen 2002-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Preprocessor for sentences or signatures
   written in some logic, usually used for
   transforming file.inline.hs into file.hs.  The sentences / signature are
   replaced with corresponding abstract syntax trees in Haskell.  This
   frees the programmer from writing AS tree expressions.

   The syntax for inline sentences is

      inlineAxioms <logic-name> <basic-spec>

   and the syntax for inlining signatures is
      inlineSign <logic-name> <basic-spec>

   where <logic-name> must be a logic in the logic graph, and <basic-spec> a
   basic specification in that logic. Only the sentences are extracted from
   the basic specification, but the used identifiers must be declared.
-}
{-
 * for sentences:

   Identifiers are left as Haskell variables, which means that they must
   be bound by the enclosing expression. E.g.

generateAxioms :: Sign f e -> [Named (FORMULA f)]
generateAxioms sig =
  concat [inlineAxioms CASL
            "  sorts s < s'; op inj : s->s' \
             \ forall x,y:s . inj(x)=inj(y) => x=y
                                  %(ga_embedding_injectivity)% "
           | (s,s') <- Rel.toList (sortRel sig)]
  where x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = mkId [mkSimpleId "_inj"]

 * for signatures the resulting expression is a record update of
   CASL.Sign.emptySign with an appropiate argument and
   all Maps/Sets/Rels turned into lists, which are transformed back
   by *.fromList.
-}

module Main where

import Language.Haskell.Pretty as HP
import Language.Haskell.Syntax
import Language.Haskell.Parser

import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel
import qualified Data.Set as Set
import Common.GlobalAnnotations
import Common.AnnoState
import Text.ParserCombinators.Parsec
import Common.Id (Id (Id), Token (Token))
import Common.Result
import Common.AS_Annotation (SenAttr)
import Common.ExtSign
import Common.Utils

import System.Environment
import Data.Char (ord, isSpace)
import Data.List (nub, isPrefixOf, intersperse)

-- avoid the whole Logic (and uni) overhead
import CASL.AS_Basic_CASL (FORMULA)
import CASL.Parse_AS_Basic (basicSpec)
import CASL.Sign (emptySign, Sign (..), OpType (..), PredType (..), Symbol)
import CASL.StaticAna (basicCASLAnalysis)
import Modal.AS_Modal (M_FORMULA)
import Modal.Parse_AS (modal_reserved_words)
import Modal.ModalSign (emptyModalSign, ModalSign)
import Modal.StatAna (basicModalAnalysis)

-- | selects the requested output
data ResType = InAxioms | InSign

parseResType :: String -> ResType
parseResType s = case s of
  "inlineAxioms" -> InAxioms
  "inlineSign" -> InSign
  _ -> error $ "inlineAxioms: unknown result type: "++s

class ToString x where
    toString :: x -> String
    toString _ = error "inlineAxioms: toString not implemented"

showSign :: (ToString e) => Sign f e -> String
showSign sig =
    "(emptySign "++extendedInfoS++"){"++
         concat (intersperse "," [sortSetS,sortRelS,opMapS,
                                  assocOpsS,predMapS])++
    "}"
    where
     sortSetS = "sortSet = Set.fromList "++
                toString (Set.toList $ sortSet sig)
     sortRelS = "sortRel = Rel.fromList "++
                toString (Rel.toList $ sortRel sig)
     opMapS = "opMap = Map.fromList "++
              toString (Map.toList $ opMap sig)
     assocOpsS = "assocOps = Map.fromList "++
                 toString (Map.toList $ assocOps sig)
     predMapS = "predMap = Map.fromList "++
                toString (Map.toList $ predMap sig)
     extendedInfoS = toString (extendedInfo sig)

instance (ToString x) => ToString (Set.Set x) where
    toString s = "Set.fromList "++toString (Set.toList s)

instance (ToString x,ToString y) => ToString (x,y) where
    toString (x,y) = '(':toString x++',':toString y++")"

instance ToString OpType where
    toString (OpType k args res) =
        "OpType "++show k++' ': toString args ++" ("++toString res++")"

instance ToString PredType where
    toString (PredType args) = "PredType "++ toString args

instance ToString Id where
    toString (Id ts is _) = "Id "++toString ts++' ':toString is++" nullRange"

instance ToString Token where
    toString (Token s _) = "Token "++show s++" nullRange"

instance (ToString e) => ToString (Sign f e) where
    toString = showSign

instance ToString ModalSign where
    toString _ = error "inlineAxioms: toString not implemented for ModalSign"

instance (ToString x) => ToString [x] where
    toString l = '[': concat (intersperse "," $ map toString l) ++"]"

instance (Show a, ToString a, Show b) => ToString (SenAttr a b) where
    toString = show

instance (ToString x) => ToString (FORMULA x)
instance ToString () where
    toString _ = "()"
instance ToString M_FORMULA

parseAndAnalyse :: (Show sens, Show sign, ToString sens, ToString sign)
                => AParser () basic_spec -> sign
                -> ((basic_spec, sign, GlobalAnnos)
                    -> Result (basic_spec, ExtSign sign Symbol, sens))
                -> ResType
                -> String -> String
parseAndAnalyse pars empt ana resType str =
  case runParser pars (emptyAnnos ()) "inlineAxioms" str of
  Left err -> error (show err)
  Right ast -> let Result ds m = ana (ast, empt, emptyGlobalAnnos) in
            case m of
              Just (_, ExtSign s1 _, sens) ->
                  case resType of
                    InAxioms -> toString sens
                    InSign -> toString s1
              _ -> error ("Error during static analysis of inlineAxioms\n" ++
                          unlines (map show ds))

caslAna, modalAna :: ResType -> String -> String
caslAna = parseAndAnalyse (basicSpec []) (emptySign ()) basicCASLAnalysis
modalAna = parseAndAnalyse (basicSpec modal_reserved_words)
   (emptySign emptyModalSign) basicModalAnalysis

-- currently only logic CASL and Modal are used
lookupLogic_in_LG :: ResType -> String -> String -> String -> String
lookupLogic_in_LG rt err s = if s == "CASL" then caslAna rt
                          else if s == "Modal" then modalAna rt
                          else error (err ++ "unsupported logic " ++ s)

-- hack: delete position info of form "[inlineAxioms ...]", replace with "[]"
deletePos :: String -> String
deletePos "" = ""
deletePos cs@(c : s) = case deletePrefixes ["[inlineAxioms", "[(line "] cs of
      Just r -> "nullRange" ++ deletePos r
      _ -> c : deletePos s
  where
   deletePrefixes [] _ = Nothing
   deletePrefixes (x:xs) str = if isPrefixOf x str then
     let r = dropWhile (/= ']') $ drop (length x) str in
          if null r then error "missing bracket"  else Just $ tail r
     else deletePrefixes xs  str

-- parse Haskell expression and insert list comprehensions for x_i variables
-- We rely on show for Ids giving just strings, such that these are
-- recognized as Haskell ids
listComp :: ResType -> String -> HsExp
listComp rt s = case rt of
                InAxioms -> lcHsExp 0 expr
                InSign -> expr
  where
  modStr = "module M where\nf="++deletePos s
  expr = case parseModule modStr of
    ParseOk (HsModule _ _ _ _ [HsPatBind _ _ (HsUnGuardedRhs expr1) _])
        -> expr1
    err -> error ("inlineAxioms: " ++ show err)


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
piHsExp (HsInfixApp expr1 qOp expr3) =
  HsInfixApp (piHsExp expr1) qOp (piHsExp expr3)
piHsExp (HsApp (HsApp (HsVar (UnQual (HsIdent typeStr)))
                      (HsCon (UnQual (HsIdent logStr))))
               (HsLit (HsString str))) =
  listComp (parseResType typeStr) $
           lookupLogic_in_LG (parseResType typeStr)
                             "inlineAxioms: " logStr str
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
piHsExp (HsLeftSection expr1 qOp) = HsLeftSection (piHsExp expr1) qOp
piHsExp (HsRightSection qOp expr2) =  HsRightSection qOp (piHsExp expr2)
piHsExp (HsRecConstr qn fields) = HsRecConstr qn (map piHsFieldUpdate fields)
piHsExp (HsRecUpdate expr fields) =
  HsRecUpdate (piHsExp expr) (map piHsFieldUpdate fields)
piHsExp (HsEnumFrom expr) = HsEnumFrom (piHsExp expr)
piHsExp (HsEnumFromTo expr1 expr2) =
  HsEnumFromTo (piHsExp expr1) (piHsExp expr2)
piHsExp (HsEnumFromThen expr1 expr2) =
  HsEnumFromThen (piHsExp expr1) (piHsExp expr2)
piHsExp (HsEnumFromThenTo expr1 expr2 expr3) =
  HsEnumFromThenTo (piHsExp expr1) (piHsExp expr2) (piHsExp expr3)
piHsExp (HsListComp expr stmts) =
  HsListComp (piHsExp expr) (map piHsStmt stmts)
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
  HsMatch loc qn pats (piHsRhs rhs) (map piHsDecl decls)

piHsDecl :: HsDecl -> HsDecl
piHsDecl (HsFunBind ms) = HsFunBind (map piHsMatch ms)
piHsDecl (HsPatBind loc pat rhs decls) =
  HsPatBind loc pat (piHsRhs rhs) (map piHsDecl decls)
piHsDecl decl = decl

parseInline :: HsModule -> HsModule
parseInline (HsModule loc modu expr imp decls) =
  HsModule loc modu expr imp (map piHsDecl decls)


-- transformation of x_i to list comprehension x_i<-x

lcHsFieldUpdate :: HsFieldUpdate -> HsFieldUpdate
lcHsFieldUpdate (HsFieldUpdate qn expr) = HsFieldUpdate qn (lcHsExp 0 expr)

lcHsStmt :: HsStmt -> HsStmt
lcHsStmt (HsGenerator loc pat expr) = HsGenerator loc pat (lcHsExp 0 expr)
lcHsStmt (HsQualifier expr) = HsQualifier (lcHsExp 0 expr)
lcHsStmt (HsLetStmt decls) = HsLetStmt (map lcHsDecl decls)

lcHsGuardedAlt :: HsGuardedAlt -> HsGuardedAlt
lcHsGuardedAlt (HsGuardedAlt loc expr1 expr2) =
  HsGuardedAlt loc (lcHsExp 0 expr1) (lcHsExp 0 expr2)

lcHsGuardedAlts :: HsGuardedAlts -> HsGuardedAlts
lcHsGuardedAlts (HsUnGuardedAlt expr) = HsUnGuardedAlt (lcHsExp 0 expr)
lcHsGuardedAlts (HsGuardedAlts alts) = HsGuardedAlts (map lcHsGuardedAlt alts)

lcHsAlt :: HsAlt -> HsAlt
lcHsAlt (HsAlt loc pat alts decls) =
  HsAlt loc pat (lcHsGuardedAlts alts) (map lcHsDecl decls)

-- look for a variable of form x_i or x_..._i and return it as a string,
-- if present. Also return the number of underscores

indexVar :: HsExp -> [(String,Int)]
indexVar (HsVar (UnQual (HsIdent v))) =
  case reverse v of
    i : '_' : _ -> [(v, ord i - ord 'h')]
    _ -> []
-- special treatment of CASL Var_decls, since these should not count
-- as enumerated lists
indexVar (HsVar _) = error "inlineAxioms: qualified var"
indexVar (HsApp (HsCon (UnQual (HsIdent "Var_decl"))) (HsList exprs)) =
  concatMap indexVar exprs
indexVar (HsApp expr1 expr2) =
  indexVar expr1++indexVar expr2
indexVar (HsTuple exprs) = concatMap indexVar exprs
indexVar (HsParen expr) = indexVar expr
indexVar (HsList exprs) =
  [(v, n - 1) | e <- exprs, (v, n) <- indexVar e, n > 1]
indexVar _ = []

lcHsExp :: Int -> HsExp -> HsExp
lcHsExp n (HsInfixApp expr1 qOp expr3) =
  HsInfixApp (lcHsExp n expr1) qOp (lcHsExp n expr3)
lcHsExp n (HsApp expr1 expr2) =
  HsApp (lcHsExp n expr1) (lcHsExp n expr2)
lcHsExp n (HsNegApp expr) =
  HsNegApp (lcHsExp n expr)
lcHsExp n (HsLambda loc pats expr) =
  HsLambda loc pats (lcHsExp n expr)
lcHsExp n (HsLet decls expr) =
  HsLet (map lcHsDecl decls) (lcHsExp n expr)
lcHsExp n (HsIf expr1 expr2 expr3) =
  HsIf (lcHsExp n expr1) (lcHsExp n expr2) (lcHsExp n expr3)
lcHsExp n (HsCase expr alts) = HsCase (lcHsExp n expr) (map lcHsAlt alts)
lcHsExp _ (HsDo stmts) = HsDo (map lcHsStmt stmts)
lcHsExp n (HsTuple exprs) = HsTuple (map (lcHsExp n) exprs)
lcHsExp n (HsList exprs)
  | null exprs = HsList []
  | n > 0 = HsList $ map (lcHsExp (n - 1)) exprs
  | otherwise = let expr = head exprs in
  case nub $ indexVar expr of
    [] -> HsList (map (lcHsExp 0) exprs)
    vs@((v, k) : r) -> let
      vs' = map fst vs
      v0 = reverse . drop 2 . reverse
      len = length vs'
      ext = if len == 2 then "" else show len
      mkZip = foldl HsApp $ HsVar $ Qual (Module "Data.List")
                $ HsIdent $ "zip" ++ ext
     in HsListComp (lcHsExp (max (k - 1) 0) expr)
        [ HsGenerator (SrcLoc "" 0 0)
              (if null r then HsPVar $ HsIdent v
               else HsPTuple $ map (HsPVar . HsIdent) vs')
              $ if null r then HsVar $ UnQual $ HsIdent $ v0 v
               else mkZip $ map (HsVar . UnQual . HsIdent . v0) vs' ]
               -- The list variable v0 is just v without index
lcHsExp n (HsParen expr) = HsParen (lcHsExp n expr)
lcHsExp n (HsLeftSection expr1 qOp) = HsLeftSection (lcHsExp n expr1) qOp
lcHsExp n (HsRightSection qOp expr2) =  HsRightSection qOp (lcHsExp n expr2)
lcHsExp _ (HsRecConstr qn fields) = HsRecConstr qn (map lcHsFieldUpdate fields)
lcHsExp n (HsRecUpdate expr fields) =
  HsRecUpdate (lcHsExp n expr) (map lcHsFieldUpdate fields)
lcHsExp n (HsEnumFrom expr) = HsEnumFrom (lcHsExp n expr)
lcHsExp n (HsEnumFromTo expr1 expr2) =
  HsEnumFromTo (lcHsExp n expr1) (lcHsExp n expr2)
lcHsExp n (HsEnumFromThen expr1 expr2) =
  HsEnumFromThen (lcHsExp n expr1) (lcHsExp n expr2)
lcHsExp n (HsEnumFromThenTo expr1 expr2 expr3) =
  HsEnumFromThenTo (lcHsExp n expr1) (lcHsExp n expr2) (lcHsExp n expr3)
lcHsExp n (HsListComp expr stmts) =
  HsListComp (lcHsExp n expr) (map lcHsStmt stmts)
lcHsExp n (HsExpTypeSig loc expr qt) = HsExpTypeSig loc (lcHsExp n expr) qt
lcHsExp _ expr = expr

lcHsGuardedRhs :: HsGuardedRhs ->HsGuardedRhs
lcHsGuardedRhs (HsGuardedRhs loc expr1 expr2) =
  HsGuardedRhs loc (lcHsExp 0 expr1) (lcHsExp 0 expr2)

lcHsRhs :: HsRhs -> HsRhs
lcHsRhs (HsUnGuardedRhs expr) = HsUnGuardedRhs (lcHsExp 0 expr)
lcHsRhs (HsGuardedRhss rhss) = HsGuardedRhss (map lcHsGuardedRhs rhss)

lcHsMatch :: HsMatch -> HsMatch
lcHsMatch (HsMatch loc qn pats rhs decls) =
  HsMatch loc qn pats (lcHsRhs rhs) decls

lcHsDecl :: HsDecl -> HsDecl
lcHsDecl (HsFunBind ms) = HsFunBind (map lcHsMatch ms)
lcHsDecl (HsPatBind loc pat rhs decls) =
  HsPatBind loc pat (lcHsRhs rhs) (map lcHsDecl decls)
lcHsDecl decl = decl

-- main functions

processFile :: String -> String -> IO ()
processFile prog file = do
  src <- readFile file
  let hsModRes = parseModuleWithMode (ParseMode file) src
      firstLineSrc = takeWhile (/='\n') src
      firstLine = if isPrefixOf "{-# OPTIONS " firstLineSrc
                  then firstLineSrc ++"\n"
                  else ""
  case hsModRes of
       ParseOk hsMod -> putStrLn $
              firstLine ++
              "{- |\nModule      :  " ++ file ++
             "\nDescription :  with inlined axioms" ++
             "\nCopyright   :  (c) Uni and DFKI Bremen 2005-2007" ++
             "\nLicense     :  similar to LGPL, see HetCATS/LICENSE.txt" ++
             "\n\nMaintainer  :  Christian.Maeder@dfki.de" ++
             "\nStability   :  provisional" ++
             "\nPortability :  portable\n" ++
             "\nModule with inlined inlineAxioms-strings generated by " ++
                prog ++ ".\n" ++
             "  Don't touch! Original source follows as comment.\n-}\n\n{-\n"
               ++ src ++ "\n-}\n\n"
               ++ unlines
               (map trimRight $ lines $ HP.prettyPrint $ parseInline hsMod)
       ParseFailed loc err -> fail $
           err ++ " in '" ++ file ++ "' line " ++ show (srcLine loc)

main :: IO ()
main = do args <- getArgs
          prog <- getProgName
          case args of
            [file] -> processFile prog file
            _ -> fail $ "Usage: " ++ prog ++ " file"
