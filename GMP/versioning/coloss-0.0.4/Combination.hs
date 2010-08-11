{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Combination where

import List
import Char
import Ratio

-- ----------------------------------------
-- base logic and compositional types
-- e.g. Comp = composition, Fuse = fusion, Cond = conditional
-- --------------------------------

data BaseLogic = K | KD | C | G | P | HM deriving (Eq,Show)
data BaseCombo = Comp | CoProd | Fuse | Cond deriving (Eq,Show)

-- this is important: needs to be modified by anyone adding
-- a new logic, gives the type of modal operator index
modaltype :: String -> String
modaltype "K" = ""; modaltype "KD" = "";
modaltype "C" = "[Int]"; modaltype "G" = "Int";
modaltype "P" = "Rational";
modaltype "HM" = "Char";

-- a System type corresponds to a functor composition
-- a list of Flat types is a flat gluing

data System = L BaseLogic | Bin BaseCombo System System deriving (Eq,Show)

data Flat = FlatUnary BaseLogic Int Int | FlatBinary BaseCombo Int (Int,Int) deriving (Eq,Show)

-- ----------------------------------------
-- System type -> Flat gluing code
-- we use system to construct a tree, label with depth first search then
-- deconstruct tree to create flat gluing
-- ----------------------------------------


-- represent gluings with one variable only that is left implicit
-- data Glue =  LL BaseLogic | UU BaseLogic Glue | BB BaseCombo Glue Glue deriving (Eq, Show)
data Glue =  S | UU BaseLogic Glue | BB BaseCombo Glue Glue deriving (Eq, Show)

(<.>) :: BaseLogic -> Glue -> Glue; x <.> y = UU x y
infixr 4 <.>
(==>) :: Glue -> Glue -> Glue; x ==> y = BB Cond x y
infixr 1 ==>
(<+>) :: Glue -> Glue -> Glue; x <+> y = BB CoProd x y
infixr 2 <+>
(<*>) :: Glue -> Glue -> Glue; x <*> y = BB Fuse x y
infixr 3 <*>


-- compute the subterms of a gluing. The types of a gluing are then
-- the subterms without the term that defines the gluing itself.
subterms:: Glue -> [Glue]
subterms glue = let
    t S = [S]
    t (UU log glue) = (UU log glue):t(glue)
    t (BB com glu1 glu2) = [BB com glu1 glu2] `union` (t glu1) `union` (t glu2)
  in t glue

-- flatten
flatten :: Glue -> [Flat]
flatten glue =  let
-- auxilary: get index noting that the full term is identified with S
  idx :: Glue -> [Glue] -> Int
  idx elem lst =  case (elemIndex elem lst)  of {
	  Nothing -> idx glue lst;
		Just n  -> n;
  }
  -- keep the list of types around to extract the corresponding numbers
  -- idea: we recurse on the first argument that initilly contains
  -- all types; the second argument is also the list of types and is
  -- passed for reference. Upon each recursive call, the index of a
  -- language equals the position where it is found in the list of
  -- types.
  aux:: [Glue] -> [Glue] -> [Flat]
  aux [] glue = []
  aux ((UU log glue):rest) all =
    (FlatUnary log (idx (UU log glue) all) (idx glue all)):(aux rest all)
  aux ((BB com glu1 glu2):rest) all =
    (FlatBinary com (idx (BB com glu1 glu2) all) (idx glu1 all, idx glu2 all)):(aux rest all)
  aux (S:rest) all = aux (glue:rest) all
	-- recall that S identifies with the whole gluing
  in aux (delete glue (subterms glue))  (delete S (subterms glue))


-- ----------------------------------------
-- render data types based on a flat gluing
-- typical usage: typeflat $ flatglue ((L KD <+> L G) ==> (L C <+> L G))
-- e.g. outputs ["L1 = F1 | .... | Cond1 L2 L5","L2 = F2 | ...",...] 
-- ----------------------------------------

-- output first part of data type definition
inityp :: Int -> String
inityp n = concat $ intersperse ((show n)++" ")  
	["data L","= F","| T","| Atom","Int | Neg","L","| And","L","L","| Or","L","L",""]
	
-- render a flattening as a string
rendflat :: Flat -> String
rendflat (FlatUnary lgc id pid) 
	= (inityp id) ++ "| " ++ (show lgc) ++ (show id) ++ " " ++ stype ++ " L" ++ (show pid)
	where	sopUp = map toUpper (show lgc); stype = modaltype sopUp 
rendflat (FlatBinary op id (n1,n2))
	| (op == Fuse) = (inityp id) ++ "| Pi1_"++ sid ++ " L" ++ s1 ++ " | Pi2_" ++ sid ++ " L" ++ s2
	| otherwise = (inityp id) ++ "| " ++ (show op) ++ (show id) ++" L" ++ s1 ++ " L" ++ s2
	where 	s1 = show n1; s2 = show n2; sid = show id;
	
typeflat :: [Flat] -> [String]; typeflat fls = map rendflat fls


-- ----------------------------------------
-- Some utily functions to extract text between two markers
-- and find & replace text
-- ----------------------------------------

-- extract elements in a list between two markers lists
aftag :: (Eq a) => [a] -> [a] -> [a]; aftag _ [] = []
aftag tag s@(_:cs) | (isPrefixOf tag s) = drop (length tag) s | otherwise = aftag tag cs

bftag :: (Eq a) => [a] -> [a] -> [a]; bftag _ [] = []
bftag tag (c:cs) | (isPrefixOf tag (c:cs)) = [] | otherwise = c:(bftag tag cs)

extract :: (Eq a) => ([a],[a]) -> [a] -> [a]
extract (st,end) ls = bftag end (aftag st ls)

-- find and replace elements in a list
replace :: (Eq a) => ([a],[a]) -> [a] -> [a]; replace _ [] = [];
replace (tag,rep) s@(c:cs)
	| (isPrefixOf tag s) = rep ++ (replace (tag,rep) (drop (length tag) s))
	| otherwise = c:(replace (tag,rep) cs)

-- iteratively find and replace
replacem :: (Eq a) => [([a],[a])] -> [a] -> [a]
replacem [] str =  str
replacem (t:ts) str = replacem ts (replace t str)
 

-- ----------------------------------------
-- code generation
-- given a flat gluing creates a 'mySat.hs' file
-- typical usage:	gen $ flatten ((K <.> S) <*> (KD <.> S))
-- inspects template file gg.tmpl.hs to generate code
-- also uses "gg.head.hs" for top of file, "gg.util.hs" for footer
-- ----------------------------------------


gen :: [Flat] -> IO ()
gen fls =
	do
		let outf = "MySat.hs"
-- 	write header: imports, Logic class, Strip class
		fhead <- readFile "gg.head.hs"
		writeFile outf fhead
--	generate data types
		let dtypes = concat $ intersperse " deriving (Eq,Show)\n" ((typeflat fls)++[""])
		appendFile outf ("\n"++dtypes)
--	get template data
		tmpl <- readFile "gg.tmpl.hs"
--	generate Strip class instances
		let strp = extract ("BEGIN_STRIPPERS","END_STRIPPERS") tmpl
		let strips = concat (genstrip fls strp)
		appendFile outf strips
--	generate Logic class instances, requires 'provable' code & 'onlybox' code
		let lgcstr = extract ("BEGIN_LOGIC","END_LOGIC") tmpl
		let prvstr = extract ("BEGIN_PROVABLES","END_PROVABLES") tmpl
		let boxstr = extract ("BEGIN_ONLYBOXS","END_ONLYBOXS") tmpl
		let logics = concat (genlogic fls (lgcstr,prvstr,boxstr))
		appendFile outf logics
-- generate matching rules
		let matstr = extract ("BEGIN_MATCHINGS","END_MATCHINGS") tmpl
		let matchings = concat (genmatch fls matstr)
		appendFile outf matchings
-- write footer: fully generic software
		ftail <- readFile "gg.util.hs"
		appendFile outf ftail


-- generate Strip class instances
genstrip :: [Flat] -> String -> [String]
genstrip [] _ = []
genstrip ((FlatUnary uop id pid):fs) strps = 
	let	sid = show id; spid = show pid; suop = show uop;
		ustrp = extract ("BEGIN_UNARY_STRIP","END_UNARY_STRIP") strps
		uopind = if (null(modaltype suop)) then "" else " _"  
		repls = [("_FROM_","L"++sid),("_TO_","L"++spid),("_UNOP_",suop++sid++uopind)]
	in	(replacem repls ustrp):(genstrip fs strps)
genstrip ((FlatBinary bop id (c1,c2)):fs) strps = 
	let	sid = show id; sc1 = show c1; sc2 = show c2;
		sbop = show bop; sbopUp = map toUpper sbop;
		bstrp = extract ("BEGIN_"++sbopUp++"_STRIP","END_"++sbopUp++"_STRIP") strps
		repls = [("_FROM_","L"++sid),("_TO1_","L"++sc1),("_TO2_","L"++sc2),("_BINOP_",sbop++sid)]
				++ [("_UNOP1_","Pi1_"++sid),("_UNOP2_","Pi2_"++sid)]
	in	(replacem repls bstrp):(genstrip fs strps)
	
-- generate Logic class instances
genlogic :: [Flat] -> (String,String,String) -> [String]
genlogic [] _ = []
genlogic ((FlatUnary uop id _):fs) strs@(lgcstr,prvstr,boxstr) =
	let	sid = show id; suop = show uop;
		uopind = if (null(modaltype suop)) then "" else " ind"  
		obox = extract ("BEGIN_BASIC_ONLYBOX","END_BASIC_ONLYBOX") boxstr
		robox = replace ("_BOXED_",suop++sid++uopind++" x") obox
		prv = extract ("BEGIN_UNARY_PROVABLE","END_UNARY_PROVABLE") prvstr
		repls = [("_N_",sid),("_PROVABLE_",prv),("_ONLYBOX_",robox)]
	in	(replacem repls lgcstr):(genlogic fs strs)
genlogic ((FlatBinary bop id _):fs) strs@(lgcstr,prvstr,boxstr) =
	let	sid = show id; sbop = show bop;  sbopUp = map toUpper sbop;
		obox = extract ("BEGIN_"++sbopUp++"_ONLYBOX","END_"++sbopUp++"_ONLYBOX") boxstr
		robox = replacem [("_BOXED_",sbop++sid++" x y"),("_ID_",sid)] obox
		prv = extract ("BEGIN_BINARY_PROVABLE","END_BINARY_PROVABLE") prvstr
		repls = [("_N_",sid),("_PROVABLE_",prv),("_ONLYBOX_",robox)]
	in	(replacem repls lgcstr):(genlogic fs strs)

	

-- generate matchings
genmatch :: [Flat] -> String -> [String]
genmatch [] _ = []
genmatch ((FlatUnary uop id pid):fs) matstr =
	let	sid = show id; spid = show pid;
		suop = show uop; suopUp = map toUpper suop;
		mat = extract ("BEGIN_"++suopUp++"_MATCHING","END_"++suopUp++"_MATCHING") matstr
		repls = [("_ID_",sid),("_PID_",spid),("_UNOP_",suop++sid)]
	in	(replacem repls mat):(genmatch fs matstr)
genmatch ((FlatBinary bop id (c1,c2)):fs) matstr =
	let	sid = show id; sc1 = show c1; sc2 = show c2;
		sbop = (show bop); sbopUp = map toUpper sbop;
		mat = extract ("BEGIN_"++sbopUp++"_MATCHING","END_"++sbopUp++"_MATCHING") matstr
		repls = [("_ID_",sid),("_CID1_",sc1),("_CID2_",sc2),("_BINOP_",sbop++sid)]
	in	(replacem repls mat):(genmatch fs matstr)



