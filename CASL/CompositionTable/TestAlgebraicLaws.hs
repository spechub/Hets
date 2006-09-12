{- |
Module      :  $Header:/repository/HetCATS/CASL/CompositionTable/TestAlgebraic\
Laws.hs,v 1.0 2006/09/12 23:38:51 2fmossa Exp $
Copyright   :  (c) Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  fmossa@tzi.de
Stability   :  provisional
Portability :  non-portable

Tests for algebrais laws for composition tables

-}
module CASL.CompositionTable.TestAlgebraicLaws where

import CASL.CompositionTable.CompositionTable
import CASL.CompositionTable.ParseSparQ
import Text.ParserCombinators.Parsec
import Common.AnnoState
import List

test_ inp =    let either = runParser parseSparQTable 
			 (emptyAnnos ()) "" inp
	           result =  case (either) of
			      Left x -> "error1"
			      Right y -> "start\n" ++ 
					 (testInvInv y) ++ (testScInv
					 y) ++ (testHoInv y)++
					 (testScHo y) ++ (testScSc1 y)
					 ++ (testHoInv y) ++
					 (testInvSc y) ++ (testInvScCo y) ++ 
					 (testAssociativity y) ++
					 (testIntersect y) ++
					--show y ++
					 "finished" 
	        in result

doTests f = do s <- readFile f
	       putStrLn (test_ s)

testAssociativity :: Table -> String
testAssociativity (Table (Table_Attrs a b baserels) 
		  comptbl convtbl _) = testAssociativity_ convtbl comptbl 
				       baserels baserels baserels  

testAssociativity_ :: Conversetable -> Compositiontable -> [Baserel]
		      -> [Baserel] ->[Baserel] -> String
testAssociativity_ ct t [] _ _ = ""
testAssociativity_ ct t _ [] _  = ""
testAssociativity_ ct t _ _ [] = ""
testAssociativity_ ct t [x] [y] [z] = testAssociativity__ ct t x y z
testAssociativity_ ct t [x] [y] (z:zs) = testAssociativity__ ct t x y z 
				       ++ testAssociativity_ ct t [x]
				       [y] zs
testAssociativity_ ct t [x] (y:ys) (z:zs) = testAssociativity_ ct t [x]
					  [y] (z:zs) ++
					  testAssociativity_ ct t [x] ys
					  (z:zs)
    
testAssociativity_ ct t (x:xs) (y:ys) (z:zs) = testAssociativity_ ct t [x]
					     (y:ys) (z:zs) ++
					     testAssociativity_ ct t xs
					     (y:ys) (z:zs)

testAssociativity__ :: Conversetable -> Compositiontable -> Baserel -> 
		       Baserel -> Baserel -> String
testAssociativity__ ct t a b c = --"\n Rels: " ++ show(a) ++ show(b) ++ "res" ++ 
				 --show (composeRelations t [a] [b])
				 testAssociativity___ a b c
				 (composeRelations t [a]	 
				 (inverseRel ct
				 (composeRelations t (inverseRel ct
				 [b]) [c]))) 
				 (composeRelations t (composeRelations t
				 [a] [b]) [c])

testAssociativity___ :: Baserel -> Baserel -> Baserel -> [Baserel] ->
			[Baserel] -> String
testAssociativity___ a b c xs ys 
		     | isSubset ys xs || isSubset xs ys  = ""
		     | otherwise =  getErrorMessage 
				  "failed weak Associativity:" 
				  (a:b:[c]) xs ys
 
isSubset:: [Baserel] -> [Baserel] -> Bool
isSubset x y = all (`elem` y) x

testInvInv :: Table -> String
testInvInv (Table (Table_Attrs _ _ baserels) _ ct _) = testInvInv_
						     ct baserels
						     

testInvInv_ :: Conversetable -> [Baserel] -> String
testInvInv_ ct [] = ""
testInvInv_ ct (x:xs) = getErrorMessage "failed Inv Inv:" [x]
					(inverseRel ct (inverseRel
					ct [x])) [x]  ++
					testInvInv_ ct xs

testInvSc :: Table -> String
testInvSc (Table (Table_Attrs _ _ baserels) _ ct _) = testInvSc_
						     ct baserels
						     

testInvSc_ :: Conversetable -> [Baserel] -> String
testInvSc_ ct [] = ""
testInvSc_ ct (x:xs) = getErrorMessageSubset "failed Inv Sc:" [x]
					(inverseRel ct (shortcutRel
					ct [x])) (homingRel ct 
					(homingRel ct [x]))  ++
					testInvSc_ ct xs   
			    
testInvScCo :: Table -> String
testInvScCo (Table (Table_Attrs _ _ baserels) t ct _) = testInvScCo_ 
							ct t baserels
							baserels

testInvScCo_ :: Conversetable -> Compositiontable -> [Baserel] 
		-> [Baserel] -> String
testInvScCo_ _ _ [] _ = ""
testInvScCo_ _ _ _ [] = ""	
testInvScCo_ ct t [x] (y:ys) = getErrorMessageSubset "failed Inv Sc Co:" 
			       (x:[y])
			       (inverseRel ct (homingRel ct
			       (composeRelations t [x] [y])))
			       (composeRelations t (inverseRel
			       ct (shortcutRel ct [y])) (homingRel ct [x]))
			       ++ testInvScCo_ ct t [x] ys
 
testInvScCo_ ct t (x:xs) ys = testInvScCo_ ct t [x] ys ++ testInvScCo_
			      ct t xs ys  

testInvScCo2 :: Table -> String
testInvScCo2 (Table (Table_Attrs _ _ baserels) t ct _) = testInvScCo_ 
							ct t baserels baserels
						     

testInvScCo2_ :: Conversetable -> Compositiontable -> [Baserel] 
		-> [Baserel] -> String
testInvScCo2_ _ _ [] _ = ""
testInvScCo2_ _ _ _ [] = ""	
testInvScCo2_ ct t [x] (y:ys) = getErrorMessage "failed Inv Sc Co2:" 
					(x:[y])
					(inverseRel ct (homingRel
					ct (composeRelations t [x]
					[y]))) 
					(composeRelations t (homingRel ct 
					(homingRel ct [y]))
					(homingRel ct [x]))  ++
					testInvScCo2_ ct t [x] ys   
 
testInvScCo2_ ct t (x:xs) ys = testInvScCo2_ ct t [x] ys ++ testInvScCo2_
			      ct t xs ys   

 

testScInv :: Table -> String
testScInv (Table (Table_Attrs _ _ baserels) _ ct _) = testScInv_
						     ct baserels
						     

testScInv_ :: Conversetable -> [Baserel] -> String
testScInv_ ct [] = ""
testScInv_ ct (x:xs) = getErrorMessage "failed Sc Inv:" [x]
					(shortcutRel ct (inverseRel
					ct [x])) (homingRel ct [x])  ++
					testScInv_ ct xs  


 
testScSc1 :: Table -> String
testScSc1 (Table (Table_Attrs _ _ baserels) _ ct _) = testScSc_ ct baserels
						     

testScSc_ :: Conversetable -> [Baserel] -> String
testScSc_ ct [] = ""
testScSc_ ct (x:xs) = getErrorMessageSubset "failed Sc Sc:" [x]
					[x] (shortcutRel ct 
					(shortcutRel ct [x]))  ++
					testScSc_ ct xs  
 

testHoInv :: Table -> String
testHoInv (Table (Table_Attrs _ _ baserels) _ ct _) = testHoInv_
						     ct baserels
						     

testHoInv_ :: Conversetable -> [Baserel] -> String
testHoInv_ ct [] = ""
testHoInv_ ct (x:xs) = getErrorMessage "failed Ho Inv:" [x]
					(homingRel ct (inverseRel
					ct [x])) (shortcutRel ct [x])  ++
					testHoInv_ ct xs  

testHoSc :: Table -> String
testHoSc (Table (Table_Attrs _ _ baserels) _ ct _) = testHoSc_
						     ct baserels
						     

testHoSc_ :: Conversetable -> [Baserel] -> String
testHoSc_ ct [] = ""
testHoSc_ ct (x:xs) = getErrorMessage "failed Ho Sc:" [x]
					(homingRel ct (shortcutRel
					ct [x])) (inverseRel ct 
					(homingRel ct [x]))  ++
					testHoSc_ ct xs  

testScHo :: Table -> String
testScHo (Table (Table_Attrs _ _ baserels) _ ct _) = testScHo_
						     ct baserels
						     

testScHo_ :: Conversetable -> [Baserel] -> String
testScHo_ ct [] = ""
testScHo_ ct (x:xs) = getErrorMessage "failed Ho Inv:" [x]
					(shortcutRel ct (homingRel
					ct [x])) (inverseRel ct [x])  ++
					testHoInv_ ct xs  

testIntersect :: Table -> String
testIntersect (Table (Table_Attrs _ _ baserels) t ct _) = testIntersect_
						     ct t baserels
						     baserels baserels
						     

testIntersect_ :: Conversetable -> Compositiontable -> [Baserel] ->
			      [Baserel] -> [Baserel] -> String
testIntersect_ ct t xs ys [] = ""
testIntersect_ ct t [x] [y] (z:zs) = testIntersect__  ct t x y z
				     (intersect (composeRelations t
				     [x] [y]) [z] ) (intersect 
				     (composeRelations t (inverseRel
				     ct [y]) (homingRel ct
				     [z]))(inverseRel ct (homingRel ct
				     [x]))) ++ testIntersect_ ct t [x]
				     [y] zs 

testIntersect_ ct t [x] (y:ys) zs = testIntersect_ ct t [x] [y] zs ++ 
				    testIntersect_ ct t [x] ys zs
testIntersect_ ct t (x:xs) ys zs = testIntersect_ ct t [x] ys zs ++
				   testIntersect_ ct t xs ys zs 

 

testIntersect__ ::  Conversetable -> Compositiontable -> Baserel ->
		   Baserel -> Baserel -> [Baserel] -> [Baserel] -> String

testIntersect__ ct t a b c [] [] = ""
testIntersect__ ct t a b c [] xs = (getErrorMessage "failed Intersect:"	      
			      (a:b:[c]) [] xs) ++ (getDetailsIntersect
			      ct t a b c) 
testIntersect__ ct t a b c xs [] = (getErrorMessage "failed Intersect:"
			      (a:b:[c]) xs []) ++ (getDetailsIntersect
			      ct t a b c)
testIntersect__ ct t a b c xs ys = "" 
 
getDetailsIntersect:: Conversetable -> Compositiontable -> Baserel ->
		      Baserel -> Baserel -> String
getDetailsIntersect ct t a b c = "a o b:" ++show(composeRelations t [a]
				 [b])++ "\na o b sect c:" ++
				 show(intersect (composeRelations t [a] [b])
				 [c]) ++ "\ninv b:" ++ show(inverseRel ct
				 [b]) ++ "\nhm c:" ++ show(homingRel ct [c])
				 ++ "\ninv b o hm c:" ++
				 show(composeRelations t (inverseRel ct
				 [b]) (homingRel ct [c])) ++"\n hm a:" ++ 
				 show(homingRel ct [a]) ++"\n inv(hm a):"
				 ++ show(inverseRel ct (homingRel ct
				 [a])) ++ 
				 "\n(inv b o hm c) sect inv(hm(a)):" 
				 ++ show(intersect (composeRelations t
				 (inverseRel ct [b])
				 (homingRel ct [c])) (inverseRel ct
				 (homingRel ct [a]))) ++ "\n\n"

getErrorMessage :: String -> [Baserel] -> [Baserel] -> [Baserel] -> String
getErrorMessage msg xs ys zs
		| setEqual ys zs = ""
		| otherwise = msg ++ "\narguments:\n" ++ show xs
			      ++"\nleft hand side:\n" ++ show ys ++
			      "\nright hand side:\n" ++ show zs
			      ++"\n\n" 

getErrorMessageSubset :: String -> [Baserel] -> [Baserel] -> [Baserel] 
			 -> String
getErrorMessageSubset msg xs ys zs
		| isSubset ys zs || isSubset zs ys = ""
		| otherwise = msg ++ "\narguments:\n" ++ show xs
			      ++"\nleft hand side:\n" ++ show ys ++
			      "\nright hand side:\n" ++ show zs ++"\n\n" 


setEqual :: [Baserel] -> [Baserel] -> Bool
setEqual l1 l2 = sort(nub l1) == sort(nub l2)

composeRelations :: Compositiontable -> [Baserel] -> [Baserel] -> [Baserel]
composeRelations a xs ys = 
    nub $ concat [composeBaseRelations a x y | x<-xs, y<-ys]


composeBaseRelations :: Compositiontable -> Baserel -> Baserel ->
			[Baserel]
composeBaseRelations (Compositiontable []) _ _ = []
composeBaseRelations (Compositiontable (x:xs)) rela relb =
			composeBaseRelation_ x rela relb ++ 
			composeBaseRelations (Compositiontable xs) rela relb


composeBaseRelation_ :: Cmptabentry -> Baserel -> Baserel -> [Baserel]
composeBaseRelation_ (Cmptabentry (Cmptabentry_Attrs rel1 rel2) res)
		     rela relb
			  | (rel1 == rela && rel2 == relb) = res
			  | otherwise = [] 

inverseRel :: Conversetable -> [Baserel] -> [Baserel]
inverseRel (Conversetable _) _ = []
inverseRel (Conversetable_Ternary xs _ _) ys = nub $ concat
						  [inverse_ x y |
						  x<-xs, y<-ys ] 

inverse_ :: Contabentry_Ternary -> Baserel -> [Baserel]
inverse_ (Contabentry_Ternary br res) rel 
	 | rel == br = res
	 | otherwise = [] 


homingRel :: Conversetable -> [Baserel] -> [Baserel]
homingRel (Conversetable _) _ = []
homingRel (Conversetable_Ternary _ _ xs) ys = nub $ concat [homing_ x y |
					      x<-xs, y<-ys] 

homing_ :: Contabentry_Ternary -> Baserel -> [Baserel]
homing_ (Contabentry_Ternary br res) rel
	| rel == br = res
	| otherwise = []

shortcutRel :: Conversetable -> [Baserel] -> [Baserel]
shortcutRel (Conversetable _) _ = []
shortcutRel (Conversetable_Ternary _ xs _) ys = nub $ concat [shortcut_ x
						y | x<-xs, y<-ys]

shortcut_ :: Contabentry_Ternary -> Baserel -> [Baserel]
shortcut_ (Contabentry_Ternary br res) rel
	  | rel == br = res
	  | otherwise = []  

