{-# OPTIONS -fglasgow-exts #-}
module GMP.CoalitionL where

import qualified Data.Set as Set
import Text.ParserCombinators.Parsec
import GMP.GMPAS
import GMP.ModalLogic
import GMP.Lexer

data CLrules = CLNR Int
             | CLPR Int Int
  deriving Show

data Coeffs = Coeffs [Set.Set Int] [Set.Set Int]
  deriving (Eq, Ord)

instance ModalLogic CL CLrules where
--    orderIns _ = True
    flagML _ = Sqr

    parseIndex = do char '{'
                    let stopParser =  do try(char ',')
                                         return 0
                                  <|> do try(char '}')
                                         return (1::Integer)
                    let xParser s = do n <- natural
                                       let news = Set.insert (fromInteger n) s
                                       q <- stopParser
                                       case q of
                                         0 -> xParser news
                                         _ -> return news
                    let isEmptyParser =  do try(char '}')
                                            return Set.empty
                                     <|> do aux <- xParser Set.empty
                                            return aux
                    res <- isEmptyParser
                    return $ CL res
    
    matchR r = let Coeffs q w = eccContent r
               in if (pairDisjoint q)&&(w/=[])
                  then if (allSubsets q (head w))&&(allMaxEq (head w) (tail w))
                       then [CLPR (length q) (-1 + length w)]
                       else []
                  else if (pairDisjoint w)&&(q==[])
                       then [CLNR (length w)]
                       else []

    guessClause r = case r of
                        _ -> []

-------------------------------------------------------------------------------
{- extract the content of the contracted clause
 - @ param (Mimplies n p) : contracted clause
 - @ return : the grades of equivalentmodal applications in the input param -}
eccContent :: ModClause CL -> Coeffs 
eccContent (Mimplies n p) =
  let getGrade x =
        case x of
          Mapp (Mop (CL i) Square) _ -> i
          _                          -> error "CoalitionL.getGrade"
  in Coeffs (map getGrade n) (map getGrade p)

{- check if the list of sets contains pairwise disjoint sets
 - @ param x : list of sets to be checked for containing disjoint sets
 - @ return : True if the sets are disjoint, false otherwise -}
pairDisjoint :: [Set.Set Int] -> Bool
pairDisjoint x =
  let disjoint e l =
        case l of
          []  -> True
          r:s -> if (Set.difference e r == e) then disjoint e s
                                              else False
  in case x of
       []  -> True
       h:t -> if not(disjoint h t) then False
                                   else pairDisjoint t

{- check if all the sets in a list are subsets of another set
 - @ param l : list of supposably subsets
 - @ param s : supposed superset
 - @ return : True if l contains only subsets of s -}
allSubsets :: (Ord a) => [Set.Set a] -> Set.Set a -> Bool
allSubsets l s =
  case l of 
    []  -> True
    h:t -> if (Set.isSubsetOf h s) then (allSubsets t s)
                                   else False

{- check if all the sets in a list are equal to a superset of a given set
 - @ param s : given set to be subset of the equal sets in the list
 - @ param l : list of sets which should be equal
 - @ return : True if s is a subset of the identical sets in l -}
allMaxEq :: (Ord a) => Set.Set a -> [Set.Set a] -> Bool
allMaxEq s l =
  case l of
    [] -> True
    _  -> let aux = head l
          in if (Set.isSubsetOf s aux)&&and(map (==aux) (tail l))
             then True
             else False
