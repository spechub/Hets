{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2002-2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
    
   functions to test ids with argument terms for literals of CASL
-}


module CASL.LiteralFuns ( isLiteral
			, isNumber
			, isSignedNumber
			, isString
			, isList
			, isFloat
			, isFrac
			, collectElements
			, basicTerm
			, convCASLChar
			, splitAppl
			) where

-- debugging
-- import Debug.Trace (trace)

import Data.Char (isDigit)

import Common.Id
import CASL.AS_Basic_CASL
import Common.GlobalAnnotations

isLiteral :: GlobalAnnos -> Id -> [TERM f] -> Bool
isLiteral ga i trm =
       or [ isNumber ga i trm 
	  , isString ga i trm
	  , isList   ga i trm
	  , isFloat  ga i trm
	  , isFrac   ga i trm
	  ]

isNumber :: GlobalAnnos -> Id -> [TERM f] -> Bool
isNumber ga i trs = 
    (digitTest i && null trs) 
    || (getLiteralType ga i == Number && all (sameId digitTest i) trs)
    where digitTest ii = 
	      (getLiteralType ga ii == Number) || case ii of
			 Id [t] [] _ 
			     | not $ null tstr -> isDigit $ head $ tstr 
			     | otherwise    -> False
			     where tstr = tokStr t
			 _           -> False

isSignedNumber :: GlobalAnnos -> Id -> [TERM f] -> Bool
isSignedNumber ga i trs = length trs == 1 && 
			  isSign i && isNumber ga ni nt  
			  where (ni,nt) = splitAppl $ head trs

isSign :: Id -> Bool
isSign i = case i of
	   Id [tok] [] _ -> let ts = tokStr tok 
			    in ts == "-" || ts == "+" 
	   _             -> False

isString :: GlobalAnnos -> Id -> [TERM f] -> Bool
isString ga i trs = case getLiteralType ga i of 
		    StringNull -> null trs
		    StringCons _ -> all (sameId stringTest i) trs
		    _ -> False
    where 
	  stringTest ii = case getLiteralType ga ii of 
			  StringNull -> True 
			  _ -> case ii of
			       Id [t] [] _ -> take 1 (tokStr t) == "\'"
			       _           -> False

convCASLChar :: Token -> String
convCASLChar t = case tokStr t of
		 cs | not (null cs) && head cs == '\''
		      && last cs == '\'' -> init $ tail cs
		    | otherwise -> 
			error ("convCASLChar: " ++ cs ++
			       " is not a valid CASL Char")

isList :: GlobalAnnos -> Id -> [TERM f] -> Bool
isList ga i trms = (case getLiteralType ga i of 
		     ListNull _ -> null trms
		     ListCons _ n -> listTest n i trms
		     _ -> False)
    where listTest n1 i1 terms = case getLiteralType ga i1 of 
	      ListNull _ -> n1 == i1 && null terms
	      ListCons _ n2 -> n1 == n2 && length terms == 2 && 
			       let (i2, ts) = splitAppl $ head $ tail terms
				   in listTest n1 i2 ts
	      _ -> False

isFloat :: GlobalAnnos -> Id -> [TERM f] -> Bool
isFloat ga i [l, r] =
    case getLiteralType ga i of 
    Floating -> (isNumber ga li ltrm || isFrac ga li ltrm) 
		&& (isSignedNumber ga ri rtrm || isNumber ga ri rtrm)
    _        -> False
    where (li,ltrm) = splitAppl l
	  (ri,rtrm) = splitAppl r 
isFloat _ _ _ = False

isFrac :: GlobalAnnos -> Id -> [TERM f] -> Bool
isFrac ga i [l, r] = 
    case getLiteralType ga i of 
    Fraction -> isNumber ga li ltrm && isNumber ga ri rtrm
    _        -> False
    where (li,ltrm) = splitAppl l 
	  (ri,rtrm) = splitAppl r
isFrac _ _ _ = False

splitAppl :: TERM f -> (Id,[TERM f])
splitAppl t = case t of
	      Application oi ts _ -> (op_id oi,ts)
	      _ -> error "splitAppl: no Application found"


leftAssCollElems :: Id -> [TERM f] -> [TERM f]
leftAssCollElems i trs = 
     case trs of
	      []    -> error "no elements to collect"
	      [x]   -> [x]
	      [x,y] -> leftAssCollElems i (splitA x) ++ [y]
	      _ys   -> error "too many elements to collect"
    where splitA t = case t of
			  Application oi its _ 
			      | op_id oi == i -> its
			      | otherwise     -> [t]
			  _        -> error "splitA: no Appl found"

collectElements :: (Maybe Id) -> Id -> [TERM f] -> [TERM f]
collectElements mnid i trs = 
    if detect_left_ass i trs 
    then leftAssCollElems i trs
    else collectElementsRight mnid i trs

detect_left_ass :: Id -> [TERM f] -> Bool
detect_left_ass i trs = 
    case trs of
    []    -> True
    [_]   -> False
    [x,_] ->  case x of
	  Application oi _ _ -> op_id oi == i
	  _        -> False	      
    _     -> False

collectElementsRight :: (Maybe Id) -> Id -> [TERM f] -> [TERM f]
collectElementsRight mnid i trs = 
     case trs of
	      []    -> error "no elements to collect"
	      [x]   -> getToken x
	      [x,y] -> x : collectElementsRight mnid i (splitA y)
	      _ys   -> error "too many elements to collect"
    where splitA t = case t of
			  Application oi its _ 
			      | op_id oi == i -> its
			      | otherwise     -> [t]
			  _        -> error "splitA: no Appl found"
	  getToken :: TERM f -> [TERM f]
	  getToken trm = maybe [trm]
			       (\ nid -> case trm of
				     Application oid [] _ 
					 | op_id oid == nid -> []
					 | otherwise -> 
					     error "null element not found"
				     _ -> error "no Application found") 
			       mnid

basicTerm :: TERM f -> Maybe Token
basicTerm trm = case trm of
		Application oi [] _ -> 
		    case op_id oi of
		    Id [tok] [] _ -> Just tok
		    _    -> error "wrong Id for getToken"
		Application _oi _ats _ -> Nothing
		_   -> error "wrong TERM for basicTerm" 

{-	  rec _cid _nid []   = False
	  rec _cid nid [t]   = case t of
			       Application o its _
				   | op_id o == nid -> True
				   | otherwise      -> False
			       _     -> False
	  rec cid nid (trm:trms) = case trm of
			       Application o its _
				   | op_id o == cid -> 
				       case its of
				       (_c_t:str_ts@(_str_t:[])) -> 
					   rec cid nid str_ts
				       _ -> False
			       _ -> False
-}

sameId :: (Id -> Bool) -> Id -> TERM f -> Bool
sameId test i t = case t of
			 Application o its _ 
			     | op_id o == i && 
			       not (null its) -> all (sameId test i) its
			     | null its -> test $ op_id o -- digits i.e.
			     | otherwise    -> False
			 Simple_id _ -> True
			 _           -> False

op_id :: OP_SYMB -> Id
op_id op = case op of 
	   Qual_op_name _ _ _ -> 
	       error "cannot lierally Print Qual_id" 
	   Op_name x          -> x

