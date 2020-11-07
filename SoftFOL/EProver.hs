{- |
Module      :  ./SoftFOL/EProver.hs
Description :  Analyze eprover output
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2013
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  portable
-}

module SoftFOL.EProver (processProof, zipF, supportsProofObject,
                        digraph, axioms, conjectures, alias, proofInfo) where

import Text.ParserCombinators.Parsec
import Common.Parsec
import SoftFOL.ParseTPTP (singleQuoted, form, genTerm, ppGenTerm)
import SoftFOL.PrintTPTP (printTPTP)
import SoftFOL.Sign (SPTerm (..))
import qualified Data.Set as Set
import System.Exit
import Common.Utils (executeProcess)
import Common.Doc (renderText)
import Common.GlobalAnnotations (emptyGlobalAnnos)
import qualified Data.HashMap.Strict as Map
import Data.Char (toLower)
import Data.Maybe (fromJust, fromMaybe, isNothing)
import Data.List (foldl', intercalate)
import Control.Monad (liftM)

data Role = Axiom | Conjecture | Other deriving (Show, Eq)

data InferenceParent = PTerm String |
                       PInferred InferenceRule |
                       PBuiltinTheory String deriving (Show, Eq, Ord)

data InferenceRule = ProofOf String
   | File { _fileName :: String, formulaName :: String }
   | Rule { rule :: String, parent :: String }
   | NoRule { parent :: String }
   | InferenceRule { rule :: String, status :: String,
                     parents :: Set.Set InferenceParent,
                     _fact :: Bool }
     deriving (Show, Eq, Ord)

parentsOf :: InferenceRule -> Set.Set InferenceParent
parentsOf (ProofOf s) = Set.singleton $ PTerm s
parentsOf (File _ _) = Set.empty
parentsOf (Rule _ s) = Set.singleton $ PTerm s
parentsOf (NoRule s) = Set.singleton $ PTerm s
parentsOf (InferenceRule _ _ ps _) = ps

termParents :: Set.Set InferenceParent -> [String]
termParents s = foldl (\ l p -> case p of
                                PTerm s' -> s' : l
                                PInferred ir ->
                                 l ++ termParents (parentsOf ir)
                                _ -> l) [] $ Set.toList s

data ProofStep = ProofStep {
 name :: String,
 role :: Role,
 formula :: Maybe SPTerm,
 inference :: InferenceRule } | Empty deriving (Show, Eq)

whiteSpace :: Parser ()
whiteSpace = forget $ oneOf "\r\t\v\f "

lexeme :: GenParser Char () b -> GenParser Char () b
lexeme p = skipMany whiteSpace >> p

lString :: String -> GenParser Char () String
lString s = lexeme $ string s

lChar :: Char -> GenParser Char () Char
lChar c = lexeme $ char c

line :: Parser ProofStep
line = ((do
 lString "cnf" <|> lString "fof"
 lChar '('
 n <- tok
 r <- tok
 f <- lexeme form
 lChar ','
 i <- lexeme (noRule <|> fromFile <|> inferenceRule <|> proofOf)
 lString ")."
 return $ ProofStep n (if r == "axiom" then Axiom
                       else if r == "conjecture" then Conjecture
                       else Other)
  (Just f) i) <|> commentOrEmptyLine) << eof

commentOrEmptyLine :: Parser ProofStep
commentOrEmptyLine = ((skipMany (char '#') >>
 manyTill anyChar (lookAhead eof))
 <|> (skipMany whiteSpace >> return "")) >> return Empty

tok :: Parser String
tok = lexeme $ many (noneOf ",") << char ','

fromFile :: Parser InferenceRule
fromFile = do
   lString "file" >> lChar '('
   f <- lexeme singleQuoted
   lChar ',' >> skipMany whiteSpace
   n <- manyTill anyChar (char ')')
   return $ File f n

proofOf :: Parser InferenceRule
proofOf = do
   n <- tok
   lString "['"
   r <- manyTill anyChar (lookAhead $ oneOf "'")
   lString "']"
   return $ case r of
             "proof" -> ProofOf n
             _ -> Rule r n

noRule :: Parser InferenceRule
noRule = try $ do
 t <- lexeme $ many (noneOf ",)")
 lookAhead $ lString ")."
 return $ NoRule t

inferenceRule :: Parser InferenceRule
inferenceRule = do
   lString "inference" >> lChar '('
   r <- tok
   lChar '[' >> lString "status" >> lChar '('
   s <- manyTill anyChar (char ')')
   lChar ']' >> lChar ',' >> lChar '['
   ps <- sepBy inferenceParent (lChar ',')
   lChar ']' >> lChar ')'
   b <- try (lChar ',' >> lString "['proof']" >> return True)
        <|> return False
   return $ InferenceRule r s (Set.fromList ps) b

inferenceParent :: Parser InferenceParent
inferenceParent = lexeme $
   liftM PInferred inferenceRule <|>
   do
    t' <- genTerm
    let t = show $ ppGenTerm t'
    return $ case t of
     't' : 'h' : 'e' : 'o' : 'r' : 'y' : '(' : _ -> PBuiltinTheory t
     _ -> PTerm t

supportsProofObject :: IO Bool
supportsProofObject = do
 (ex, _, _) <- executeProcess "eprover" ["--proof-object", "-V"] ""
 case ex of
  ExitSuccess -> return True
  ExitFailure _ -> return False

processProof :: (a -> ProofStep -> a) -> a -> [String] -> (a, Maybe String)
processProof fn a = foldl' (\ (a', result) l -> case result of
 Just _ -> (a', result)
 Nothing -> case runParser line () "" l of
  Right p | p /= Empty -> (fn a' p, result)
  Left e -> (a', Just . unlines $ "Warning - Failed to parse eprover proof"
               : map ((:) '\t') (("Input: " ++ l) : lines (show e)))
  _ -> (a', result)
 ) (a, Nothing)

zipF :: (a -> b -> a) -> (c -> b -> c) -> (a, c) -> b -> (a, c)
zipF f1 f2 (a, c) b = (f1 a b, f2 c b)

axioms :: [(String, String)] -> ProofStep -> [(String, String)]
axioms l p = case inference p of
              File _ _ | role p == Axiom ->
               (formulaName . inference $ p, name p) : l
              _ -> l

conjectures :: [(String, String)] -> ProofStep -> [(String, String)]
conjectures l p = if role p == Conjecture
                  then (formulaName . inference $ p, name p) : l else l

alias :: Map.HashMap String String -> ProofStep -> Map.HashMap String String
alias m p = case inference p of
             NoRule s -> case Map.lookup s m of
                          Just s' -> Map.insert (name p) s' m
                          Nothing -> Map.insert (name p) s m
             _ -> m

proofInfo :: Set.Set String -> ProofStep -> Set.Set String
proofInfo p_set p =
 if Set.null p_set || Set.member (name p) p_set
 then Set.union p_set $ Set.fromList $
       name p : termParents (parentsOf $ inference p)
 else p_set

showTerm :: ProofStep -> String
showTerm = renderText emptyGlobalAnnos . printTPTP . fromJust . formula

facts :: Set.Set String -> ProofStep -> Set.Set String
facts s p =
 let isFact n = case n of
                 PTerm n' -> Set.member n' s
                 PInferred ir -> all (`Set.member` s) $
                                  termParents $ parentsOf ir
                 PBuiltinTheory _ -> True
 in if (role p /= Conjecture) &&
       all isFact (Set.toList $ parentsOf $ inference p)
    then Set.insert (name p) s else s

attributes :: [(String, String)] -> String
attributes attrs = case attrs of
 [] -> ""
 _ -> "[" ++ intercalate ","
  (map (\ (n, v) -> n ++ "=\"" ++ v ++ "\"") attrs) ++ "]"

vertex :: String -> [(String, String)] -> String
vertex s attrs = s ++ attributes attrs

edge :: Bool -> String -> String -> [(String, String)] -> String
edge inv v1 v2 attrs' =
 let attrs = ("splines", "curved") : attrs'
 in if inv then v2 ++ " -> " ++ v1 ++ attributes attrs
    else v1 ++ " -> " ++ v2 ++ attributes attrs

digraph :: Set.Set String -> Map.HashMap String String ->
           (Set.Set String, Set.Set String, String,
            Map.HashMap (String, [String]) String) -> ProofStep ->
           (Set.Set String, Set.Set String,
            String, Map.HashMap (String, [String]) String)
digraph p_set aliases (s, neg, d, m) p =
 let s' = facts s p
     neg_ = Set.insert (name p) neg
     negated = any (`Set.member` neg)
                   (termParents $ parentsOf $ inference p)
     alias' n = fromMaybe n (Map.lookup n aliases)
     neg' = case inference p of
             (InferenceRule _ st _ _)
              | elem (map toLower st) ["cth", "unc", "uns"]
                          -> if negated then neg else neg_
              | negated -> neg_
              | otherwise -> neg
             _ -> if negated then neg_ else neg
     isFact' = case inference p of
                InferenceRule _ _ _ b -> b
                _ -> False
     color' = ("fillcolor", if role p == Axiom || Set.member (name p) s'
                           then "green" else "yellow") :
              ("style", "filled") : (if Set.member (name p) neg'
               then [("color", "red")] else [("color", "green")])
     color = case inference p of
               ProofOf _ | role p == Other ->
                if negated then [("style", "filled"), ("fillcolor", "red"),
                                 ("color", "red")]
                else [("style", "filled"), ("fillcolor", "green"),
                      ("color", "green")]
               _ -> color'
     (s'', neg'', m', d') = (case role p of
           Axiom -> case inference p of
            File f n -> (s', neg', m, [vertex ('v' : name p) $ color ++
             [("label", "Axiom " ++ n ++ " (File: " ++ f ++ ")\\n" ++
                        showTerm p)]])
            _ -> (s', neg', m, [])
           Conjecture -> case inference p of
            File f n -> (s', neg', m, [vertex ('v' : name p) $ color ++
             [("label", "Conjecture " ++ n ++ " (File: " ++ f ++ ")\\n" ++
                        showTerm p)]])
            _ -> (s', neg', m, [])
           Other ->
            let (s'_, neg'_, m'', d'') = case inference p of
                 ProofOf tm ->
                  (s', neg', m, [edge True ('v' : alias' tm)
                                           ('v' : alias' (name p))
                      [("label", (if negated then "dis" else "")
                                 ++ "proves")]])
                 r@(Rule _ _) -> (s', neg', m,
                                   [edge False ('v' : alias' (parent r))
                                               ('v' : alias' (name p))
                                     [("label", rule r)]])
                 r@(NoRule _) -> (s', neg', m,
                                 [edge False ('v' : alias' (parent r))
                                             ('v' : alias' (name p)) []])
                 inf@(InferenceRule {}) ->
                  let (r, l1, m1, new) =
                       case Map.lookup
                        (rule inf, termParents $ parents inf) m of
                                Just r' -> (r',
                                 [edge False r' ('v' : alias' (name p)) []],
                                 m, False)
                                _ ->
                                 let r1 = 'r' : show (Map.size m)
                                 in (r1, [vertex r1
                                     [("label", "Apply rule " ++ rule inf),
                                      ("style", "dotted")],
                                     if not isFact' then edge False r1
                                      ((if head (name p) == 'r' then ""
                                        else "v") ++
                                      alias' (name p)) [] else ""],
                                      Map.insert (rule inf, termParents $
                                       parents inf) r1 m, True)
                      (s2', neg2', l3, m3) =
                       foldl (\ (s1', neg1', l2, m2) s1 -> case s1 of
                                 PTerm s2 -> if new then
                                  (s1', neg1', l2 ++ [edge False
                                                      ('v' : alias' s2) r [],
                                        edge (not $ Set.member s2 s')
                                             ('v' : alias' s2) r
                                         [("label", "SZS " ++ status inf),
                                          ("color", "blue"),
                                          ("fontcolor", "blue")] ], m2)
                                  else (s1', neg1', l2, m2)
                                 PInferred ir ->
                                  let (s1'', neg1'', l2', m2') = digraph p_set
                                       aliases (s1', neg1', unlines l2, m2) $
                                        ProofStep r Other Nothing ir
                                  in (s1'', neg1'', [l2'], m2')
                                 PBuiltinTheory s2 ->
                                  case Map.lookup (s2, []) m2 of
                                   Just s2'' -> (s1', neg1', l2 ++
                                                 [edge False s2'' r []], m2)
                                   Nothing ->
                                    let s2'' = 't' : show (Map.size m2)
                                    in (s1', neg1', l2 ++ [vertex s2''
                                            [("style", "filled"),
                                             ("fillcolor", "green"),
                                             ("color", "green"), ("label", s2)],
                                             edge False s2'' r []],
                                       Map.insert (s2, []) s2'' m2))
                                (s', neg', l1, m1) (Set.toList $ parentsOf inf)
                  in (s2', neg2', m3, l3)
                 _ -> (s', neg', m, [])
            in (s'_, neg'_, m'', case formula p of
                               Just _ | not isFact' -> vertex ('v' : name p)
                                (color ++ [("label", showTerm p)]) : d''
                               _ -> d''))
 in if (Set.member (name p) p_set || isNothing (formula p)) &&
       notElem (name p) (Map.keys aliases)
    then (s'', neg'', unlines $ d : d', m')
    else (s', neg', d, m)
