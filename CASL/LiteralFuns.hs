
{- HetCATS/CASL/Print_AS_Basic.hs
   $Id$
   Authors: Klaus Lüttich
   Year:    2002
   
   Functions to test Ids [TERM]s for literals of CASL

   todo:
   
-}


module CASL.LiteralFuns ( CASL.LiteralFuns.isLiteral
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
import Common.GlobalAnnotationsFunctions (isLiteral, getLiteralType, nullStr)


isLiteral :: GlobalAnnos -> Id -> [TERM] -> Bool
isLiteral ga i trm =
    if Common.GlobalAnnotationsFunctions.isLiteral (literal_map ga) i 
    then or [ isNumber ga i trm 
	    , isString ga i trm
	    , isList   ga i trm
	    , isFloat  ga i trm
	    , isFrac   ga i trm
	    ]
    else False

{-print_Literal :: (forall a .PrettyPrint a => GlobalAnnos -> a -> Doc) ->  
		 (Doc -> Doc) -> -- ^ a function that surrounds 
				 -- the given Doc with appropiate 
				 -- parens
		 (Doc -> Doc -> Doc) -> -- ^ a beside with space 
					-- like <+> or <\+>
		 ([Doc] -> Doc) -> -- ^ a list concat with space and 
				   -- fill the line policy  like
				   -- fsep or fsep_latex
		 (forall b . PrettyPrint b => 
		          GlobalAnnos -> [b] -> Doc) -> 
		          -- ^ a function that prints a nice 
			  -- comma seperated list like commaT 
			  -- or commaT_latex
		 GlobalAnnos -> Id -> [TERM] -> Doc
print_Literal pf parens_fun 
	      beside_fun fsep_fun commaT_fun 
	      ga li ts 
    | isNumber li ts = hcat $ map (pf ga) $ toksNumber li
    | isString li ts = pf ga $ (\s -> let r = '"':(s ++ "\"") in seq r r) $ 
		       concatMap convCASLChar $ toksString li
{-    | isList   li ts = case list_lit (literal_annos ga) of
		       Nothing -> error "something impossible happend: a list id is recognized but no literal information is found"
		       Just (b_id,_,_) -> pf ga tok_list ts
-}
{- -> condPrint_Mixfix pf parens_fun 		
  beside_fun fsep_fun 
  commaT_fun 
  ga li ts -- TODO:
    | otherwise = condPrint_Mixfix pf parens_fun 
		                   beside_fun fsep_fun commaT_fun 
				   ga li ts
    where literalType = getLiteralType lmap li 
-} -- -} 

isNumber :: GlobalAnnos -> Id -> [TERM] -> Bool
isNumber ga i trs = 
    digitTest i || (getLiteralType (literal_map ga) i == Number && 
		    all (sameId digitTest i) trs)
    where digitTest ii = case ii of
			 Id [t] [] _ -> isDigit $ head $ tokStr t
			 _           -> False

isSignedNumber :: GlobalAnnos -> Id -> [TERM] -> Bool
isSignedNumber ga i trs = isSign i && isNumber ga ni nt  
			  where (ni,nt) = splitAppl t_trs
				[t_trs] = trs

isSign :: Id -> Bool
isSign i = case i of
	   Id [tok] [] _ -> let ts = tokStr tok 
			    in ts == "-" || ts == "+" 
	   _             -> False

isString :: GlobalAnnos -> Id -> [TERM] -> Bool
isString ga i trs = literalType == StringNull || 
		    (literalType == StringCons &&
		     all (sameId stringTest i) trs)
    where {- nullStr = case string_lit $ literal_annos ga of
		    Just (n,_) -> n
		    Nothing    -> error "isString: nullStr not found"-}
	  literalType = getLiteralType (literal_map ga) i
	  stringTest ii = ii == (nullStr ga) ||
			 case ii of
			 Id [t] [] _ -> head (tokStr t) == '\''
			 _           -> False

convCASLChar :: Token -> String
convCASLChar t = case tokStr t of
		 cs | head cs == '\''
		      && last cs == '\'' -> init $ tail cs
		    | otherwise -> 
			error ("convCASLChar: " ++ cs ++
			       " is not a valid CASL Char")

isList :: GlobalAnnos -> Id -> [TERM] -> Bool
isList ga i trms = getLiteralType' i == ListNull || 
		   (getLiteralType' i == ListCons &&
		    listTest i trms)
    where getLiteralType' = getLiteralType (literal_map ga)
	  listTest i1 [] = getLiteralType' i1 == ListNull
	  listTest i1 (_:y:[]) = getLiteralType' i1 == ListCons
				&& (applTest && listTest i' ts')
	      where (applTest,i',ts') = 
			case y of
			Application o ts [] -> (True,op_id o,ts)
			_  -> (False,Id [] [] [], [])
	  listTest _ _ = error "wrong call of listTest"

isFloat :: GlobalAnnos -> Id -> [TERM] -> Bool
isFloat ga i trms = getLiteralType (literal_map ga) i == Floating 
		    && (isNumber ga li ltrm || isFrac ga li ltrm) 
		    && (isSignedNumber ga ri rtrm || isNumber ga ri rtrm)
    where (li,ltrm) = left
	  (ri,rtrm) = right
	  (left,right) = case trms of
			 []    -> error "isFloat: no terms found"
			 [_]   -> error "isFloat: too few terms found"
			 [l,r] -> (splitAppl l, splitAppl r)
			 _     -> error "isFloat: too many terms found"

isFrac :: GlobalAnnos -> Id -> [TERM] -> Bool
isFrac ga i trms = getLiteralType (literal_map ga) i == Fraction &&
		   isNumber ga li ltrm && isNumber ga ri rtrm
    where (li,ltrm) = left
	  (ri,rtrm) = right
	  (left,right) = case trms of
			 []    -> error "isFrac: no terms found"
			 [_]   -> error "isFrac: too few terms found"
			 [l,r] -> (splitAppl l, splitAppl r)
			 _     -> error "isFrac: too many terms found"

splitAppl :: TERM -> (Id,[TERM])
splitAppl t = case t of
	      Application oi ts _ -> (op_id oi,ts)
	      _ -> error "splitAppl: no Application found"

collectElements :: (Maybe Id) -> Id -> [TERM] -> [TERM]
collectElements mnid i trs = 
     case trs of
	      []    -> error "no elements to collect"
	      [x]   -> getToken x
	      [x,y] -> x : collectElements mnid i (splitA i y)
	      _ys   -> error "too many elements to collect"
    where splitA ii t = case t of
			  Application oi its _ 
			      | op_id oi == ii -> its
			      | otherwise      -> [t]
			  _        -> error "splitA: no Appl found"
	  getToken :: TERM -> [TERM]
	  getToken trm = case mnid of 
			 Nothing -> [trm]
			 Just nid -> case trm of
				     Application oid [] _ 
					 | op_id oid == nid -> []
					 | otherwise -> 
					     error "null element not found"
				     _ -> error "no Application found"

basicTerm :: TERM -> Maybe Token
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

sameId :: (Id -> Bool) -> Id -> TERM -> Bool
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

