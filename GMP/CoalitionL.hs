{-# OPTIONS -fglasgow-exts #-}
module GMP.CoalitionL where

import qualified Data.Set as Set
import Text.ParserCombinators.Parsec
import GMP.Lexer
import GMP.ModalLogic
import GMP.GMPAS

data CLrules = CLNR Int
             | CLPR Int Int
  deriving Show

data Coeffs = Coeffs [Set.Set Int] [Set.Set Int]
  deriving (Eq, Ord)

instance ModalLogic CL CLrules where
    processFormula f = 
      let getMaxAgents g m = 
            case g of
              Mapp (Mop (CL _ i) _) _ 
                -> if (i/=(-1)) then i else m
              Junctor f1 _ f2         
                -> max (getMaxAgents f1 m) (getMaxAgents f2 m)
              Neg ff
                -> getMaxAgents ff m
              _ -> m
          resetMaxAgents g m =
            case g of
              Mapp (Mop (CL s i) t) h
                -> if (m==(-1))||((i/=(-1))&&(i/=m))
                   then error "CoalitionL.getMaxAgents"
                   else Mapp (Mop (CL s m) t) h
              Junctor f1 j f2
                -> Junctor (resetMaxAgents f1 m) j (resetMaxAgents f2 m)
              Neg ff
                -> Neg (resetMaxAgents ff m)
              _ -> g
          checkConsistency g =
            case g of
              Mapp (Mop (CL s i) _) _
               -> if (Set.findMax s > i)||(Set.findMin s < 1)||(Set.size s > i)
                  then error "CoalitionL.checkConsistency"
                  else g
              Junctor f1 j f2
               -> Junctor (checkConsistency f1) j (checkConsistency f2)
              Neg ff
               -> Neg (checkConsistency ff)
              _-> g
          aux = resetMaxAgents f (getMaxAgents f (-1))
      in checkConsistency aux

    flagML _ = Sqr

    parseIndex =  do try(char '{')
                     let stopParser =  do try(char ',')
                                          return False
                                   <|> do try(char '}')
                                          return True
                                   <?> "CoalitionL.parseIndex.stop"
                     let shortParser =  do xx <- natural
                                           let n = fromInteger xx
                                           string ".."
                                           yy <- natural
                                           let m = fromInteger yy
                                           return $ Set.fromList [n..m]
                                    <?> "CoalitionL.parseIndex.short"
                     let xParser s =  do aux <- try(shortParser)
                                         let news = Set.union s aux
                                         q <- stopParser
                                         case q of
                                           False -> xParser news
                                           _     -> return news
                                  <|> do n <- natural
                                         let news = Set.insert (fromInteger n) s
                                         q <- stopParser
                                         case q of
                                           False -> xParser news
                                           _     -> return news
                                  <?> "CoalitionL.parseIndex.x"
                     let isEmptyParser =  do try(char '}')
                                             whiteSpace
                                             return Set.empty
                                      <|> do aux <- xParser Set.empty
                                             return aux
                                      <?> "CoalitionL.parseIndex.isEmpty"
                     let maxAgentsParser =  do aux <- try(natural)
                                               let n = fromInteger aux
                                               return n
                                        <|> return (-1::Int)
                                        <?> "CoalitionL.parseIndex.maxAgents"
                     res <- isEmptyParser
                     n <- maxAgentsParser
                     return $ CL res n
              <|> do aux <- natural
                     let n = fromInteger aux
                     let res = Set.fromList [1..n]
                     return $ CL res n
              <?> "CoalitionL.parseIndex"

    matchR r = let Coeffs q w = eccContent r
               in if (pairDisjoint q)&&(w/=[])
                  then if (allSubsets q (head w))&&(allMaxEq (head w) (tail w))
                       then [CLPR (length q) (-1 + length w)]
                       else []
                  else if (pairDisjoint w)&&(q==[])
                       then [CLNR (length w)]
                       else []

    guessClause r = 
      case r of
        CLNR n -> [Pimplies [] [1..n]]
        CLPR n m -> [Pimplies [(m+2)..(m+n+1)] [1..(m+1)]]

-------------------------------------------------------------------------------
{- extract the content of the contracted clause
 - @ param (Mimplies n p) : contracted clause
 - @ return : the grades of equivalentmodal applications in the input param -}
eccContent :: ModClause CL -> Coeffs 
eccContent (Mimplies n p) =
  let getGrade x =
        case x of
          Mapp (Mop (CL g _) Square) _ -> g
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
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
