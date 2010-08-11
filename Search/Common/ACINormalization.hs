{- |
Module      :  $Header$
Description :  Normalization w.r.t. associativity and commutativity
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Common.ACINormalization where

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Search.Utils.List
import Search.Utils.SetMap
import Text.ParserCombinators.Parsec

data Term t = ACI (Set.Set (Term t)) | Sequence [Term t] | Symbol t | Number Int deriving (Eq,Ord)

{-----------------------------------------------------------------------
-- Show
-}

instance (Show t) => Show (Term t) where
    show (Number n) = show n
    show (Symbol s) = show s
    show (Sequence ts) = "[" ++ (mapShow "," ts) ++ "]"
    show (ACI ts) = "{" ++ (mapShow "," (Set.toList ts)) ++ "}"

{-----------------------------------------------------------------------
-- Parse
-}

atom :: Parser (Term String)
atom = do ls <- many1 letter
	  ds <- many digit
	  return (Symbol (ls ++ ds))

aciParser :: Parser (Term String)
aciParser = 
    do char '['
       children <- sepBy1 aciParser (char ',')
       char ']'
       return (Sequence children)
    <|>
    do char '{'
       children <- sepBy1 aciParser (char ',')
       char '}'
       return (ACI (Set.fromList children))
    <|>
    do a <- atom
       return a

run :: Show a => Parser a -> String -> IO ()
run p input
        = case (parse p "" input) of
            Left err -> do{ putStr "parse error at "
                          ; print err
                          }
            Right x  -> print x

{-----------------------------------------------------------------------
-- Normalize
-}

compareTerms :: Term t -> Term t -> Ordering
compareTerms (ACI ts1) (ACI ts2) =
    case compare (Set.size ts1) (Set.size ts2)
    of LT -> LT
       GT -> GT
       EQ -> compareListOfTerms (List.sortBy compareTerms (Set.toList ts1)) (List.sortBy compareTerms (Set.toList ts2))
compareTerms (Sequence ts1) (Sequence ts2) =
    case compare (length ts1) (length ts2)
    of LT -> LT
       GT -> GT
       EQ -> compareListOfTerms ts1 ts2
compareTerms (Symbol _) (Symbol _) = EQ
compareTerms (Number m) (Number n) = compare m n
compareTerms (Number _) _ = LT
compareTerms (Symbol _) (Number _) = GT
compareTerms (Symbol _) _ = LT
compareTerms (Sequence _) (ACI _) = LT
compareTerms (Sequence _) _ = GT
compareTerms (ACI _) _ = GT
compareListOfTerms [] [] = EQ
compareListOfTerms (t1:t1s) (t2:t2s) =
    if (termOrd == EQ) then (compareListOfTerms t1s t2s) else termOrd
    where termOrd = compareTerms t1 t2

{- |
   (replace symbList term) renames each symbol in the term by its position number in symbList
   if the symbol is member of symbolList otherwise the symbol remains the same; e.g.:
   replace ["b","a","c"] {["Q",{"a","b"}],["Q",{"c","b"}]}
   -> {["Q",{0,1}],["Q",{0,2}]}
-}
replace :: (Eq s,Ord s)  => [s] -> Term s -> Term s
replace ss (ACI terms) = ACI (Set.map (replace ss) terms)
replace ss (Sequence terms) = Sequence (map (replace ss) terms)
replace _ (Number n) = Number n
replace ss (Symbol s) = 
    case lookUpFirstEntry s ss
    of (Just n) -> Number n
       Nothing -> Symbol s

{- |
   (hasSymbol term) is true iff any subterm contains a symbol.
-}
hasSymbol :: Term t -> Bool
hasSymbol (Number n) = False
hasSymbol (Symbol s) = True
hasSymbol (Sequence ts) = any hasSymbol ts
hasSymbol (ACI ts) = any hasSymbol (Set.toList ts)


minTerms :: (Eq t,Ord t)  => Set.Set (Term t) -> Set.Set (Term t)
minTerms terms =
    let termsWithSymbols = Set.filter hasSymbol terms
	in if Set.null termsWithSymbols
	   then Set.empty  -- Problem, wenn der einzige Term keine Symbole mehr enthaelt!! tritt auf bei aciMorphism t1!
	   else let (minTerm:_) = List.sortBy compareTerms (Set.toList termsWithSymbols)
                    termsAreEqual t1 t2 = (compareTerms t1 t2) == EQ
		in Set.filter (termsAreEqual minTerm) termsWithSymbols

minMorphs :: (Eq s,Ord s)  => Term s -> [[s]] -> [[s]]
minMorphs term [] = []
minMorphs term substitutions = 
    if Set.null minimalTerms then substitutions else Set.toList (image termsToSubs minimalTerms)
    where minimalTerms = (minTerms $ dom termsToSubs)
          termsToSubs = Map.fromList (map (\subs -> (replace subs term,subs)) substitutions)
       

{- |
   prox takes an term and returns a list of the minimal symbols from that term (s. 'minTerms')
-}   
prox :: (Eq s,Ord s)  => Term s -> [s]
prox (Number n) = []
prox (Symbol s) = [s]
prox (Sequence ts) = case (filter hasSymbol ts)
		     of (t:_) -> prox t
			_ -> []
prox (ACI ts) = List.nub (concat $ Set.toList (Set.map prox (minTerms ts)))

dist :: (Eq s,Ord s)  => Term s -> [[s]] -> [[s]]
dist term subs = concatMap spread subs
    where spread sub = map (\s -> sub++[s]) (prox (replace sub term))

symbolsOf :: (Ord s)  => Term s -> Set.Set s
symbolsOf (Number n) = Set.empty
symbolsOf (Symbol s) = Set.singleton s
symbolsOf (Sequence ts) = Set.unions (map symbolsOf ts)
symbolsOf (ACI ts) = Set.unions (map symbolsOf (Set.toList ts))

aciMorphism :: (Eq s,Ord s)  => Term s -> [[s]]
aciMorphism term = acim term [[]]
    where symbolsOfTerm = (symbolsOf term)
          substitutionIsIncomplete sub = Set.isProperSubsetOf (Set.fromList sub) symbolsOfTerm
	  acim term subs =
	      if all substitutionIsIncomplete subs
	      then acim term (minMorphs term (dist term subs))
	      else subs

aci :: [Char] -> (Term String, [[String]])
aci input = case (parse aciParser "" input)
	    of Left err -> error "parse error at " -- ++ (show err)
	       Right x -> (x,aciMorphism x)

{-
*ACINormalization> aci "{a2,a1,{b3,a2},{a1,a1}}"
({{"a1"},{"a2","b3"},"a1","a2"},[["a1","a2","b3"]])
*ACINormalization> aci "{a2,a1,{b3,a2},[a1,a1]}"
({{"a2","b3"},["a1","a1"],"a1","a2"},[["a1","a2","b3"]])

*ACINormalization> let (x,(p:_)) = aci "{a2,a1,{b3,a2},[a1,a1]}"
*ACINormalization> replace p x
{{1,2},[0,0],0,1}

*ACINormalization> let (x,[p]) = aci "{{[Q,{a,d}],[Q,{c,d}],[R,{a,c}]},{[Q,{b,d}],[R,{a,b}],[R,{b,c}]}}"
*ACINormalization> x
{{["Q",{"a","d"}],["Q",{"c","d"}],["R",{"a","c"}]},{["Q",{"b","d"}],["R",{"a","b"}],["R",{"b","c"}]}}
*ACINormalization> p
["R","b","c","a","Q","d"]
*ACINormalization> replace p x
{{[0,{1,2}],[0,{1,3}],[4,{1,5}]},{[0,{2,3}],[4,{2,5}],[4,{3,5}]}}

Die ACI Normalisierung, wie sie hier implementiert ist, ist wohl NICHT VOLLSTÄNDIG!!!!
wie das Beispiel zeigt:
*ACINormalization> print $ aci "[{a,b,c},{a,c,d}]"
([{"a","b","c"},{"a","c","d"}],[["c","a","b","d"]])

Denn auch die Subsitution ["a","c","b","d"] würde den Term minimal machen!!!


-}
