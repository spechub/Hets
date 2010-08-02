{- |
Module      :  $Id$
Copyright   :  (c) Jonathan von Schroeder, C.Maeder, DFKI GmbH 2010
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
            "  sorts s < s'; op inj : s->s'
               forall x, y : s . inj(x)=inj(y) => x=y
                                  %(ga_embedding_injectivity)% "
           | (s, s') <- Rel.toList (sortRel sig)]
  where x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = mkId [mkSimpleId "_inj"]

 * for signatures the resulting expression is a record update of
   CASL.Sign.emptySign with an appropiate argument and
   all Maps/Sets/Rels turned into lists, which are transformed back
   by *.fromList.
-}

module Main where

import Language.Haskell.Exts.Pretty as HP
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Parser

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
import Data.Char (ord)
import Data.List (nub, isPrefixOf, intercalate)

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
  _ -> error $ "inlineAxioms: unknown result type: " ++ s

class ToString x where
    toString :: x -> String
    toString _ = error "inlineAxioms: toString not implemented"

showSign :: (ToString e) => Sign f e -> String
showSign sig =
    "(emptySign " ++ extendedInfoS ++ "){"
    ++ intercalate "," [sortSetS, sortRelS, opMapS, assocOpsS, predMapS]
    ++ "}"
    where
     sortSetS = "sortSet = Set.fromList " ++
                toString (Set.toList $ sortSet sig)
     sortRelS = "sortRel = Rel.fromList " ++
                toString (Rel.toList $ sortRel sig)
     opMapS = "opMap = Map.fromList " ++
              toString (Map.toList $ opMap sig)
     assocOpsS = "assocOps = Map.fromList " ++
                 toString (Map.toList $ assocOps sig)
     predMapS = "predMap = Map.fromList " ++
                toString (Map.toList $ predMap sig)
     extendedInfoS = toString (extendedInfo sig)

instance (ToString x) => ToString (Set.Set x) where
    toString s = "Set.fromList " ++ toString (Set.toList s)

instance (ToString x, ToString y) => ToString (x, y) where
    toString (x, y) = '(' : toString x ++ ',' : toString y ++ ")"

instance ToString OpType where
    toString (OpType k args res) =
        "OpType " ++ show k ++ ' ' : toString args
         ++ " (" ++ toString res ++ ")"

instance ToString PredType where
    toString (PredType args) = "PredType " ++ toString args

instance ToString Id where
    toString (Id ts is _) =
        "Id " ++ toString ts ++ ' ' : toString is ++ " nullRange"

instance ToString Token where
    toString (Token s _) = "Token " ++ show s ++ " nullRange"

instance (ToString e) => ToString (Sign f e) where
    toString = showSign

instance ToString ModalSign where
    toString _ = error "inlineAxioms: toString not implemented for ModalSign"

instance (ToString x) => ToString [x] where
    toString l = '[' : intercalate "," (map toString l) ++ "]"

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
lookupLogic_in_LG rt err s = case s of
  "CASL" -> caslAna rt
  "Modal" -> modalAna rt
  _ -> error $ err ++ "unsupported logic " ++ s

-- hack: delete position info of form "[inlineAxioms ...]", replace with "[]"
deletePos :: String -> String
deletePos "" = ""
deletePos cs@(c : s) = case deletePrefixes ["[inlineAxioms", "[(line "] cs of
      Just r -> "nullRange" ++ deletePos r
      _ -> c : deletePos s
  where
   deletePrefixes [] _ = Nothing
   deletePrefixes (x : xs) str = if isPrefixOf x str then
     let r = dropWhile (/= ']') $ drop (length x) str in
          if null r then error "missing bracket" else Just $ tail r
     else deletePrefixes xs str

{- parse Haskell expression and insert list comprehensions for x_i variables
We rely on show for Ids giving just strings, such that these are
recognized as Haskell ids -}
listComp :: ResType -> String -> Exp
listComp rt s = case rt of
                InAxioms -> lcHsExp 0 expr
                InSign -> expr
  where
  modStr = "module M where\nf=" ++ deletePos s
  expr = case parseModule modStr of
    ParseOk (Module _ _ _ _ _ _ [PatBind _ _ _ (UnGuardedRhs expr1) _])
        -> expr1
    err -> error ("inlineAxioms: " ++ show err)


-- parse inline for Haskell decls and exps

piHsFieldUpdate :: FieldUpdate -> FieldUpdate
piHsFieldUpdate (FieldUpdate qn expr) = FieldUpdate qn (piHsExp expr)
piHsFieldUpdate f = f

piHsQualStmt :: QualStmt -> QualStmt
piHsQualStmt (QualStmt stmt) = QualStmt (piHsStmt stmt)
piHsQualStmt (ThenTrans expr) = ThenTrans (piHsExp expr)
piHsQualStmt (ThenBy expr1 expr2) = ThenBy (piHsExp expr1) (piHsExp expr2)
piHsQualStmt (GroupBy expr) = GroupBy (piHsExp expr)
piHsQualStmt (GroupUsing expr) = GroupUsing (piHsExp expr)
piHsQualStmt (GroupByUsing expr1 expr2) =
    GroupByUsing (piHsExp expr1) (piHsExp expr2)

piHsBind :: IPBind -> IPBind
piHsBind (IPBind loc name expr) = IPBind loc name (piHsExp expr)

piHsBinds :: Binds -> Binds
piHsBinds (BDecls decls) = BDecls (map piHsDecl decls)
piHsBinds (IPBinds binds) = IPBinds (map piHsBind binds)

piHsStmt :: Stmt -> Stmt
piHsStmt (Generator loc pat expr) = Generator loc pat (piHsExp expr)
piHsStmt (Qualifier expr) = Qualifier (piHsExp expr)
piHsStmt (LetStmt binds) = LetStmt (piHsBinds binds)
piHsStmt (RecStmt stmts) = RecStmt (map piHsStmt stmts)

piHsGuardedAlt :: GuardedAlt -> GuardedAlt
piHsGuardedAlt (GuardedAlt loc stmts expr) =
  GuardedAlt loc (map piHsStmt stmts) (piHsExp expr)

piHsGuardedAlts :: GuardedAlts -> GuardedAlts
piHsGuardedAlts (UnGuardedAlt expr) = UnGuardedAlt (piHsExp expr)
piHsGuardedAlts (GuardedAlts alts) = GuardedAlts (map piHsGuardedAlt alts)

piHsAlt :: Alt -> Alt
piHsAlt (Alt loc pat alts binds) =
  Alt loc pat (piHsGuardedAlts alts) (piHsBinds binds)

piHsExp :: Exp -> Exp
piHsExp (InfixApp expr1 qOp expr3) =
  InfixApp (piHsExp expr1) qOp (piHsExp expr3)
piHsExp (App (App (Var (UnQual (Ident typeStr)))
                      (Con (UnQual (Ident logStr))))
               (Lit (String str))) =
  listComp (parseResType typeStr) $
           lookupLogic_in_LG (parseResType typeStr)
                             "inlineAxioms: " logStr str
piHsExp (App expr1 expr2) =
  App (piHsExp expr1) (piHsExp expr2)
piHsExp (NegApp expr) =
  NegApp (piHsExp expr)
piHsExp (Lambda loc pats expr) =
  Lambda loc pats (piHsExp expr)
piHsExp (Let (BDecls decls) expr) =
  Let (BDecls (map piHsDecl decls)) (piHsExp expr)
piHsExp (If expr1 expr2 expr3) =
  If (piHsExp expr1) (piHsExp expr2) (piHsExp expr3)
piHsExp (Case expr alts) = Case (piHsExp expr) (map piHsAlt alts)
piHsExp (Do stmts) = Do (map piHsStmt stmts)
piHsExp (Tuple exprs) = Tuple (map piHsExp exprs)
piHsExp (List exprs) = List (map piHsExp exprs)
piHsExp (Paren expr) = Paren (piHsExp expr)
piHsExp (LeftSection expr1 qOp) = LeftSection (piHsExp expr1) qOp
piHsExp (RightSection qOp expr2) = RightSection qOp (piHsExp expr2)
piHsExp (RecConstr qn fields) = RecConstr qn (map piHsFieldUpdate fields)
piHsExp (RecUpdate expr fields) =
  RecUpdate (piHsExp expr) (map piHsFieldUpdate fields)
piHsExp (EnumFrom expr) = EnumFrom (piHsExp expr)
piHsExp (EnumFromTo expr1 expr2) =
  EnumFromTo (piHsExp expr1) (piHsExp expr2)
piHsExp (EnumFromThen expr1 expr2) =
  EnumFromThen (piHsExp expr1) (piHsExp expr2)
piHsExp (EnumFromThenTo expr1 expr2 expr3) =
  EnumFromThenTo (piHsExp expr1) (piHsExp expr2) (piHsExp expr3)
piHsExp (ListComp expr stmts) =
  ListComp (piHsExp expr) (map piHsQualStmt stmts)
piHsExp (ExpTypeSig loc expr qt) = ExpTypeSig loc (piHsExp expr) qt
piHsExp expr = expr

piHsGuardedRhs :: GuardedRhs -> GuardedRhs
piHsGuardedRhs (GuardedRhs loc stmts expr) =
  GuardedRhs loc (map piHsStmt stmts) (piHsExp expr)

piHsRhs :: Rhs -> Rhs
piHsRhs (UnGuardedRhs expr) = UnGuardedRhs (piHsExp expr)
piHsRhs (GuardedRhss rhss) = GuardedRhss (map piHsGuardedRhs rhss)

piHsMatch :: Match -> Match
piHsMatch (Match loc qn pats t rhs binds) =
  Match loc qn pats t (piHsRhs rhs) (piHsBinds binds)

piHsDecl :: Decl -> Decl
piHsDecl (FunBind ms) = FunBind (map piHsMatch ms)
piHsDecl (PatBind loc pat t rhs binds) =
  PatBind loc pat t (piHsRhs rhs) (piHsBinds binds)
piHsDecl decl = decl

parseInline :: Module -> Module
parseInline (Module loc modu opts warn expr imp decls) =
  Module loc modu opts warn expr imp (map piHsDecl decls)


-- transformation of x_i to list comprehension x_i<-x

lcHsFieldUpdate :: FieldUpdate -> FieldUpdate
lcHsFieldUpdate (FieldUpdate qn expr) = FieldUpdate qn (lcHsExp 0 expr)
lcHsFieldUpdate f = f

lcHsQualStmt :: QualStmt -> QualStmt
lcHsQualStmt (QualStmt stmt) = QualStmt (lcHsStmt stmt)
lcHsQualStmt (ThenTrans expr) = ThenTrans (lcHsExp 0 expr)
lcHsQualStmt (ThenBy expr1 expr2) = ThenBy (lcHsExp 0 expr1) (lcHsExp 0 expr2)
lcHsQualStmt (GroupBy expr) = GroupBy (lcHsExp 0 expr)
lcHsQualStmt (GroupUsing expr) = GroupUsing (lcHsExp 0 expr)
lcHsQualStmt (GroupByUsing expr1 expr2) =
    GroupByUsing (lcHsExp 0 expr1) (lcHsExp 0 expr2)

lcHsStmt :: Stmt -> Stmt
lcHsStmt (Generator loc pat expr) = Generator loc pat (lcHsExp 0 expr)
lcHsStmt (Qualifier expr) = Qualifier (lcHsExp 0 expr)
lcHsStmt (LetStmt binds) = LetStmt (lcHsBinds binds)
lcHsStmt (RecStmt stmts) = RecStmt (map lcHsStmt stmts)

lcHsGuardedAlt :: GuardedAlt -> GuardedAlt
lcHsGuardedAlt (GuardedAlt loc stmts expr) =
  GuardedAlt loc (map lcHsStmt stmts) (lcHsExp 0 expr)

lcHsGuardedAlts :: GuardedAlts -> GuardedAlts
lcHsGuardedAlts (UnGuardedAlt expr) = UnGuardedAlt (lcHsExp 0 expr)
lcHsGuardedAlts (GuardedAlts alts) = GuardedAlts (map lcHsGuardedAlt alts)

lcHsAlt :: Alt -> Alt
lcHsAlt (Alt loc pat alts binds) =
  Alt loc pat (lcHsGuardedAlts alts) (lcHsBinds binds)

{- look for a variable of form x_i or x_..._i and return it as a string,
if present. Also return the number of underscores -}

indexVar :: Exp -> [(String, Int)]
indexVar (Var (UnQual (Ident v))) =
  case reverse v of
    i : '_' : _ -> [(v, ord i - ord 'h')]
    _ -> []
{- special treatment of CASL Var_decls, since these should not count
as enumerated lists -}
indexVar (Var _) = error "inlineAxioms: qualified var"
indexVar (App (Con (UnQual (Ident "Var_decl"))) (List exprs)) =
  concatMap indexVar exprs
indexVar (App expr1 expr2) =
  indexVar expr1 ++ indexVar expr2
indexVar (Tuple exprs) = concatMap indexVar exprs
indexVar (Paren expr) = indexVar expr
indexVar (List exprs) =
  [(v, n - 1) | e <- exprs, (v, n) <- indexVar e, n > 1]
indexVar _ = []

lcHsExp :: Int -> Exp -> Exp
lcHsExp n (InfixApp expr1 qOp expr3) =
  InfixApp (lcHsExp n expr1) qOp (lcHsExp n expr3)
lcHsExp n (App expr1 expr2) =
  App (lcHsExp n expr1) (lcHsExp n expr2)
lcHsExp n (NegApp expr) =
  NegApp (lcHsExp n expr)
lcHsExp n (Lambda loc pats expr) =
  Lambda loc pats (lcHsExp n expr)
lcHsExp n (Let binds expr) =
  Let (lcHsBinds binds) (lcHsExp n expr)
lcHsExp n (If expr1 expr2 expr3) =
  If (lcHsExp n expr1) (lcHsExp n expr2) (lcHsExp n expr3)
lcHsExp n (Case expr alts) = Case (lcHsExp n expr) (map lcHsAlt alts)
lcHsExp _ (Do stmts) = Do (map lcHsStmt stmts)
lcHsExp n (Tuple exprs) = Tuple (map (lcHsExp n) exprs)
lcHsExp n (List exprs)
  | null exprs = List []
  | n > 0 = List $ map (lcHsExp (n - 1)) exprs
  | otherwise = let expr = head exprs in
  case nub $ indexVar expr of
    [] -> List (map (lcHsExp 0) exprs)
    vs@((v, k) : r) -> let
      vs' = map fst vs
      v0 = reverse . drop 2 . reverse
      len = length vs'
      ext = if len == 2 then "" else show len
      mkZip = foldl App $ Var $ Qual (ModuleName "Data.List")
                $ Ident $ "zip" ++ ext
     in ListComp (lcHsExp (max (k - 1) 0) expr)
        [ QualStmt (Generator (SrcLoc "" 0 0)
              (if null r then PVar $ Ident v
               else PTuple $ map (PVar . Ident) vs')
              $ if null r then Var $ UnQual $ Ident $ v0 v
               else mkZip $ map (Var . UnQual . Ident . v0) vs') ]
               -- The list variable v0 is just v without index
lcHsExp n (Paren expr) = Paren (lcHsExp n expr)
lcHsExp n (LeftSection expr1 qOp) = LeftSection (lcHsExp n expr1) qOp
lcHsExp n (RightSection qOp expr2) = RightSection qOp (lcHsExp n expr2)
lcHsExp _ (RecConstr qn fields) = RecConstr qn (map lcHsFieldUpdate fields)
lcHsExp n (RecUpdate expr fields) =
  RecUpdate (lcHsExp n expr) (map lcHsFieldUpdate fields)
lcHsExp n (EnumFrom expr) = EnumFrom (lcHsExp n expr)
lcHsExp n (EnumFromTo expr1 expr2) =
  EnumFromTo (lcHsExp n expr1) (lcHsExp n expr2)
lcHsExp n (EnumFromThen expr1 expr2) =
  EnumFromThen (lcHsExp n expr1) (lcHsExp n expr2)
lcHsExp n (EnumFromThenTo expr1 expr2 expr3) =
  EnumFromThenTo (lcHsExp n expr1) (lcHsExp n expr2) (lcHsExp n expr3)
lcHsExp n (ListComp expr stmts) =
  ListComp (lcHsExp n expr) (map lcHsQualStmt stmts)
lcHsExp n (ExpTypeSig loc expr qt) = ExpTypeSig loc (lcHsExp n expr) qt
lcHsExp _ expr = expr

lcHsGuardedRhs :: GuardedRhs -> GuardedRhs
lcHsGuardedRhs (GuardedRhs loc stmts expr2) =
  GuardedRhs loc (map lcHsStmt stmts) (lcHsExp 0 expr2)

lcHsRhs :: Rhs -> Rhs
lcHsRhs (UnGuardedRhs expr) = UnGuardedRhs (lcHsExp 0 expr)
lcHsRhs (GuardedRhss rhss) = GuardedRhss (map lcHsGuardedRhs rhss)

lcHsMatch :: Match -> Match
lcHsMatch (Match loc qn pats t rhs decls) =
  Match loc qn pats t (lcHsRhs rhs) decls

lcHsBind :: IPBind -> IPBind
lcHsBind (IPBind loc name expr) = IPBind loc name (lcHsExp 0 expr)

lcHsBinds :: Binds -> Binds
lcHsBinds (BDecls decls) = BDecls (map lcHsDecl decls)
lcHsBinds (IPBinds binds) = IPBinds (map lcHsBind binds)

lcHsDecl :: Decl -> Decl
lcHsDecl (FunBind ms) = FunBind (map lcHsMatch ms)
lcHsDecl (PatBind loc pat t rhs binds) =
  PatBind loc pat t (lcHsRhs rhs) (lcHsBinds binds)
lcHsDecl decl = decl

-- main functions

processFile :: String -> String -> IO ()
processFile prog file = do
  src <- readFile file
  let hsModRes = parseModuleWithMode defaultParseMode
        { parseFilename = file } src
      firstLineSrc = takeWhile (/= '\n') src
      firstLine = if isPrefixOf "{-# LANGUAGE " firstLineSrc
                  then firstLineSrc ++ "\n"
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
main = do
  args <- getArgs
  prog <- getProgName
  case args of
    [file] -> processFile prog file
    _ -> fail $ "Usage: " ++ prog ++ " file"
