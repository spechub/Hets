-- needs: -ifgl:haterm-1.0/src -package util -package data -fglasgow-exts -fallow-overlapping-instances

{- HetCATS/aterm_conv/ATC_sml_cats.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   This module exports functions, that can convert an sml-CATS ATerm
   into the Haskell abstract syntax tree. So it contains all the
   necessary instances of ATermConvertible and a heuritic function
   that calculates the new lists of Pos out of Region tuples.

   the templates for the instances are automatically derived by
   DrIFT. But there were made many hand written changes.

   todo:
     - p_flag from pos-TERM is not considered jet!
-}

module ATC_sml_cats (from_sml_ATerm,read_sml_ATerm) where

-- for debugging only
--import IOExts (trace)

import List (isPrefixOf)

import ATermLib

import Utils

import Id
import AS_Annotation

import AS_Basic_CASL

import Logic_CASL
import Grothendieck

import AS_Structured
import AS_Architecture
import AS_Library

-- the following module provides the ability to parse the "unparsed-anno"
import Parsec (parse,setPosition)
import ParsecPos (newPos)
import qualified Anno_Parser (annotations,parse_anno)
import CaslLanguage

from_sml_ATerm :: ATermTable -> LIB_DEFN
read_sml_ATerm :: FilePath -> IO LIB_DEFN

from_sml_ATerm = fromATerm
read_sml_ATerm fn = readFile fn >>= return . fromATermString 

----- instances of Id.hs ------------------------------------------------
instance ATermConvertible Token where
    toATerm _ _ = error "*** toATerm for \"Token\" not implemented"
    fromATerm att =
        case aterm of
            (AAppl "token" [ aa ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = nullPos
                in (Token aa' ab')
            (AAppl "place" [])  ->
                let
                aa' = Id.place
                ab' = nullPos
                in (Token aa' ab')
	    _ -> fromATermError "Token" aterm
        where
            aterm = findATerm att (map (getATermSp att) pat_list)
            pat_list = [(AAppl "token" [ ]),(AAppl "place" [ ]) ]

instance ATermConvertible Id where
    toATerm _ _ = error "*** toATerm for \"Id\" not implemented"
    fromATerm att =
        case aterm of
            (AAppl "compound-id" [ aa,ab ])  -> -- TOKEN_OR_MIXFIX,[ID]
                let
                aa' = fromATermTokenTup (getATermByIndexSp1 aa att)
                ab' = fromATerm (getATermByIndexSp1 ab att)
                ac' = []
                in (Id aa' ab' ac')
	    (AAppl "simple-id" [ aa ]) ->
		let 
		aa' = fromATermTokenTup (getATermByIndexSp1 aa att)
		ab' = []
		ac' = []
                in (Id aa' ab' ac')
	    _ -> fromATermError "Id" aterm
        where
            aterm = findATerm att (map (getATermSp att) pat_list)
            pat_list = [(AAppl "compound-id" [ ]),(AAppl "simple-id" [ ]) ]
-------------------------------------------------------------------------
fromATermTokenTup :: ATermTable -> [Token]
fromATermTokenTup att = 
    case aterm of
       (AAppl "tuple" [tops,_,_]) ->
	   fromATerm (getATermByIndexSp1 tops att)
       _         -> fromATermError "Token" aterm
    where aterm = getATerm att

----- instances of AS_Annotation.hs -------------------------------------
instance ATermConvertible Annotation where
    toATerm _ _ = error "*** toATerm for \"Annotation\" not implemented"
    fromATerm att =
        case aterm of
            (AAppl "comment-line" [ aa ])  ->
                let
                aa' = chomp $ fromATerm (getATermByIndexSp1 aa att)
                ab' = pos_l
                in (Comment_line aa' ab')
            (AAppl "comment" [ aa ])  ->
                let
                aa' = lines (fromATerm (getATermByIndexSp1 aa att))
                ab' = pos_l
                in (Comment_group aa' ab')
            (AAppl "unparsed-anno" [ aa ])  ->
		parse_anno pos_l 
		   (fromATerm (getATermByIndexSp1 aa att))
            (AAppl "annote-line" [ aa,ab ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = fromATerm (getATermByIndexSp1 ab att)
                ac' = pos_l
                in (Annote_line aa' ab' ac')
            (AAppl "annote-group" [ aa,ab ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = fromATerm (getATermByIndexSp1 ab att)
                ac' = pos_l
                in (Annote_group aa' ab' ac')
            (AAppl "display-anno" [ aa,ab ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = parse_disp_anno aa' pos_l 
		           (chomp $ fromATerm (getATermByIndexSp1 ab att))
                in ab'
            (AAppl "string-anno" [ aa,ab ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = fromATerm (getATermByIndexSp1 ab att)
                ac' = pos_l
                in (String_anno aa' ab' ac')
            (AAppl "list-anno" [ aa,ab,ac ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = fromATerm (getATermByIndexSp1 ab att)
                ac' = fromATerm (getATermByIndexSp1 ac att)
                ad' = pos_l
                in (List_anno aa' ab' ac' ad')
            (AAppl "number-anno" [ aa ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = pos_l
                in (Number_anno aa' ab')
            (AAppl "floating-anno" [ aa,ab ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = fromATerm (getATermByIndexSp1 ab att)
                ac' = pos_l
                in (Float_anno aa' ab' ac')
            (AAppl "prec-anno" [ aa,ab,ac ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = fromATerm (getATermByIndexSp1 ab att)
                ac' = fromATerm (getATermByIndexSp1 ac att)
                ad' = pos_l
                in (Prec_anno aa' ab' ac' ad')
            (AAppl "lassoc-anno" [ aa ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = pos_l
                in (Lassoc_anno aa' ab')
            (AAppl "rassoc-anno" [ aa ])  ->
                let
                aa' = fromATerm (getATermByIndexSp1 aa att)
                ab' = pos_l
                in (Rassoc_anno aa' ab')
            (AAppl "label-anno" [ aa ])  ->
                let
                aa' = 
		   lines (showId (fromATerm (getATermByIndexSp1 aa att)) "")
                ab' = pos_l
                in (Label aa' ab')
            (AAppl "implies" [])  ->
                let
                aa' = pos_l
                in (Implies aa')
            (AAppl "definitional" [])  ->
                let
                aa' = pos_l
                in (Definitional aa')
            (AAppl "conservative" [])  ->
                let
                aa' = pos_l
                in (Conservative aa')
	    (AAppl "mono" []) ->
		Monomorph pos_l
	    _ -> fromATermError "Annotation" aterm
        where
            aterm = findATerm att' (map (getATermSp att') pat_list)
            pat_list = [(AAppl "comment-line" [ ]) 
		       ,(AAppl "comment" [ ])
		       ,(AAppl "unparsed-anno" [ ]) 
		       ,(AAppl "annote-line" [ ]) 
                       ,(AAppl "annote-group" [ ]) 
		       ,(AAppl "display-anno" [ ]) 
                       ,(AAppl "string-anno" [ ]) 
		       ,(AAppl "list-anno" [ ]) 
                       ,(AAppl "number-anno" [ ]) 
		       ,(AAppl "floating-anno" [ ]) 
                       ,(AAppl "prec-anno" [ ]) 
		       ,(AAppl "lassoc-anno" [ ]) 
                       ,(AAppl "rassoc-anno" [ ]) 
		       ,(AAppl "label-anno" [ ])
                       ,(AAppl "implies" [ ]) 
		       ,(AAppl "definitional" [ ]) 
                       ,(AAppl "conservative" [ ]) 
		       ,(AAppl "mono" []) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-ANNO" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

--- Well the following instance has to tie together things, that don't
--- belong to each other. Because I can't declare instances for
--- certain "Annoted types"
instance (ATermConvertible a) => ATermConvertible (Annoted a) where
    toATerm _ _ = error "*** toATerm for \"(Annoted a)\" not implemented"
    fromATerm att =
        case aterm of
         (AAppl con as)  ->
	     (case con of
	       -- Basic Items (including sig_items)
	        "pos-BASIC-ITEMS" -> 
	              let (bi,las) = fromATermAnnotedBasic_Items att
	              in Annoted bi [] las []
	       -- L_.* constuctors from SML 
	        "tuple"           -> Annoted (fromATerm (getATermByIndexSp1 
						        (head as) 
						        att))
	                                     []
	                                     []
				             (toAnnoList (last as) att)
	        _      -> -- "No appropiate constructor for Annoted found"
 			Annoted (fromATerm att)
			            []
				    []
				    []
	     )
	 _ -> fromATermError "Annoted a" aterm
        where
            aterm = getATerm att
 
---- functions to convert annoted stuff ---------------------------------
-- all these functions are called by instance ATermConvertible Annoted a

fromATermAnnotedBasic_Items :: forall a . ATermConvertible a => 
			       ATermTable -> (a,[Annotation])
fromATermAnnotedBasic_Items att = 
    if isSig_items then
       ((fromATerm att),[])
    else ((fromATerm att),annoList)  
    where isSig_items = 
	      case aterm of
	      AAppl _ as -> -- pos-BASIC-ITEMS
	            case getATerm $ getATermByIndexSp1 (last as) att of
		    AAppl "sig-items" _ -> True
		    _                   -> False
	      _ -> fromATermError "{SIG,BASIC}_items" aterm
	  aterm = getATerm att
 	  annoList = case getATerm att of
		     AAppl _ as -> getAnnoList (last as) att
		     _          -> error "Wrong ATerm structure: BASIC_ITEMS"
{-	  att' = let (AAppl _ as) = getATerm att -- pos-BASIC-ITEMS
		     (AAppl _ as') = getATerm $  -- sig-items
				     getATermByIndexSp1 (head as) att
	         in getATermByIndexSp1 (head as') att -}

{-fromATermAnnotedSig_Items :: ATermTable -> [SIG_ITEMS]
fromATermAnnotedSig_Items att =
-- Sig Items have an anno list which now is attached to
-- the first item
		  Just "s-items" -> 
		      let aterm' = getATerm (getATermByIndexSp1 (head as) att)
			       as'    = case aterm' of AAppl _ as -> as
	          in Annoted (fromATerm att)
			     []
			     []
			     (getAnnoList (last as) att)
-}



-- getAnnoList and toAnnoList are only working with an AIndex as first
-- argument is given. If getAnnoList is called every AAppl that starts
-- with "pos-" is crossed without consideration. toAnnoList just calls
-- the [Annotation] conversion directly.

getAnnoList :: ATerm -> ATermTable -> [Annotation]
getAnnoList ai att = case at of
		     AAppl c as | isPrefixOf "pos-" c -> 
				    getAnnoList (last as) att
		     AAppl _ as -> toAnnoList (last as) att
		     _          -> error "wrong storage or missed 'pos-' contructor" 
    where at = getATerm (getATermByIndexSp1 ai att)

toAnnoList :: ATerm -> ATermTable -> [Annotation]
toAnnoList ai att = fromATerm $ getATermByIndexSp1 ai att

-------------------------------------------------------------------------

parse_anno :: [Pos] -> String -> Annotation
parse_anno pos_l inp =
    case (parse (set_pos Anno_Parser.annotations) "" inp) of
       Left err   -> error ("internal parse error at " ++ (show err))
       Right [x]  -> x
    where set_pos p = do setPosition sp
			 whiteSpace
			 p
	  sp = newPos "ATermConversion from SML" (fst pos) (snd pos)
	  pos = head pos_l

parse_disp_anno :: Id -> [Pos] -> String -> Annotation
parse_disp_anno i pos_l inp =
    case (Anno_Parser.parse_anno (Annote_group "display" [inp'] pos_l) sp) of
       Left err   -> error ("internal parse error at " ++ (show err))
       --Right [] -> error $ "No displayanno: " ++ inp' 
       Right x  -> x -- trace ("parsed display anno:" ++ show x) x
       --Right xs   -> error $ "More than one displayanno" ++ show xs
    where sp = newPos "ATermConversion from SML" (fst pos) (snd pos)
	  pos = head pos_l
	  inp' = (showId i "") ++ (' ':inp)

----- instances of AS_Basic_CASL.hs -------------------------------------
instance ATermConvertible BASIC_SPEC where
    toATerm _ _ = error "*** toATerm for \"BASIC_SPEC\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "basic-spec" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (AS_Basic_CASL.Basic_spec aa')
	    _ -> fromATermError "BASIC_SPEC" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "basic-spec" [ ]) ]
	    att' =
		case getATerm att of
		(AAppl "pos-BASIC-SPEC" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

instance ATermConvertible BASIC_ITEMS where
    toATerm _ _ = error "*** toATerm for \"BASIC_ITEMS\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "sig-items" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (Sig_items aa')
	    (AAppl "free-datatype" [ aa,_ ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Free_datatype aa' ab')
	    (AAppl "sort-gen" [ aa,_ ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Sort_gen aa' ab')
	    (AAppl "var-items" [ aa,_ ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Var_items aa' ab')
	    (AAppl "local-var-axioms" [ aa,ab,_ ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Local_var_axioms aa' ab' ac')
	    (AAppl "axiom-items" [ aa,_ ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Axiom_items aa' ab')	    
	    _ -> fromATermError "BASIC_ITEMS" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "sig-items" [ ]) ,
			(AAppl "free-datatype" [ ]) ,
			(AAppl "sort-gen" [ ]) ,
			(AAppl "var-items" [ ]) ,
			(AAppl "local-var-axioms" [ ]) ,
			(AAppl "axiom-items" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-BASIC-ITEMS" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible SIG_ITEMS where
    toATerm _ _ = error "*** toATerm for \"SIG_ITEMS\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "sort-items" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		as  = fromATerm (getATermByIndexSp1 ab att)
       		aa'' = (addLAnnoList as $ head aa'):(tail aa')
		ab' = pos_l
		in (Sort_items aa'' ab')
	    (AAppl "op-items" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		as  = fromATerm (getATermByIndexSp1 ab att)
		aa'' = (addLAnnoList as $ head aa'):(tail aa')
		ab' = pos_l
		in (Op_items aa'' ab')
	    (AAppl "pred-items" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		as  = fromATerm (getATermByIndexSp1 ab att)
		aa'' = (addLAnnoList as $ head aa'):(tail aa')
		ab' = pos_l
		in (Pred_items aa'' ab')
	    (AAppl "datatype-items" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		as  = fromATerm (getATermByIndexSp1 ab att)
		aa'' = (addLAnnoList as $ head aa'):(tail aa')
		ab' = pos_l
		in (Datatype_items aa'' ab')
	    _ -> fromATermError "SIG_ITEMS" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "sort-items" [ ]) ,(AAppl "op-items" [ ]) ,
			(AAppl "pred-items" [ ]) ,
			(AAppl "datatype-items" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-SIG-ITEMS" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible SORT_ITEM where
    toATerm _ _ = error "*** toATerm for \"SORT_ITEM\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "sort-decl" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Sort_decl aa' ab')
	    (AAppl "subsort-decl" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Subsort_decl aa' ab' ac')
	    (AAppl "subsort-defn" [ aa,ab,ac,ad,ae ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATermSIMPLE_ID (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		ad' = fromATerm (getATermByIndexSp1 ad att)
		as  = toAnnoList ae att
		ad''= addRAnnoList as ad'
		ae' = pos_l
		in (Subsort_defn aa' ab' ac' ad'' ae')
	    (AAppl "iso-decl" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Iso_decl aa' ab')
	    _ -> fromATermError "SORT_ITEM" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "sort-decl" [ ]) ,(AAppl "subsort-decl" [ ]) ,
			(AAppl "subsort-defn" [ ]) ,(AAppl "iso-decl" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-SORT-ITEM" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible OP_ITEM where
    toATerm _ _ = error "*** toATerm for \"OP_ITEM\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "op-decl" [ aa,ab,ac ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		ad' = pos_l
		in (Op_decl aa' ab' ac' ad')
	    (AAppl "op-defn" [ aa,ab,ac,ad ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		as  = fromATerm (getATermByIndexSp1 ad att)
		ac''= addRAnnoList as ac'
		ad' = pos_l
		in (Op_defn aa' ab' ac'' ad')
	    _ -> fromATermError "OP_ITEM" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "op-decl" [ ]) ,(AAppl "op-defn" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-OP-ITEM" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible OP_TYPE where
    toATerm _ _ = error "*** toATerm for \"OP_TYPE\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "total-op-type" [ aa,ab ])  ->
		let
		(aa',ps) = fromATermSORTS (getATermByIndexSp1 aa att)
		ab'      = fromATerm (getATermByIndexSp1 ab att)
		ac'      = insertPos ps pos_l
		in (Total_op_type aa' ab' ac')
	    (AAppl "partial-op-type" [ aa,ab ])  ->
		let
		(aa',ps) = fromATermSORTS (getATermByIndexSp1 aa att)
		ab'      = fromATerm (getATermByIndexSp1 ab att)
		ac'      = insertPos ps pos_l
		in (Partial_op_type aa' ab' ac')
	    _ -> fromATermError "OP_TYPE" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "total-op-type" [ ]) ,
			(AAppl "partial-op-type" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-OP-TYPE" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

---- a helper for the SML-datatype SORTS -------------------------------
fromATermSORTS :: ATermTable -> ([SORT],[Pos])
fromATermSORTS att = 
	case aterm of
	    (AAppl "sorts" [ aa ])  ->
		(fromATerm (getATermByIndexSp1 aa att),pos_l)		
	    _ -> fromATermError "([SORT],[Pos])" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-SORTS" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

------------------------------------------------------------------------

instance ATermConvertible OP_HEAD where
    toATerm _ _ = error "*** toATerm for \"OP_HEAD\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "total-op-head" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Total_op_head aa' ab' ac')
	    (AAppl "partial-op-head" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Partial_op_head aa' ab' ac')
	    _ -> fromATermError "OP_HEAD" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "total-op-head" [ ]) ,
			(AAppl "partial-op-head" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-OP-HEAD" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible ARG_DECL where
    toATerm _ _ = error "*** toATerm for \"ARG_DECL\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "arg-decl" [ AAppl "tuple" [aa,ab] ])  ->
		let
		aa' = fromATermVARs (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Arg_decl aa' ab' ac')
	    _ -> fromATermError "ARG_DECL" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "arg-decl" [AAppl "tuple" []]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-ARG-DECL" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible OP_ATTR where
    toATerm _ _ = error "*** toATerm for \"OP_ATTR\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "associative" [ ])  ->
		let
		in Assoc_op_attr
	    (AAppl "commutative" [ ])  ->
		let
		in Comm_op_attr
	    (AAppl "idempotent" [ ])  ->
		let
		in Idem_op_attr
	    (AAppl "unit-op-attr" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (Unit_op_attr aa')
	    _ -> fromATermError "OP_ATTR" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "associative" [ ]) ,
			(AAppl "commutative" [ ]) ,
			(AAppl "idempotent" [ ]) ,
			(AAppl "unit-op-attr" [ ]) ]
	    att' =
		case getATerm att of
		(AAppl "pos-OP-ATTR" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

instance ATermConvertible PRED_ITEM where
    toATerm _ _ = error "*** toATerm for \"PRED_ITEM\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "pred-decl" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Pred_decl aa' ab' ac')
	    (AAppl "pred-defn" [ aa,ab,ac,_ ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		ad' = pos_l
		in (Pred_defn aa' ab' ac' ad')
	    _ -> fromATermError "PRED_ITEM" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "pred-decl" [ ]) ,(AAppl "pred-defn" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-PRED-ITEM" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible PRED_TYPE where
    toATerm _ _ = error "*** toATerm for \"PRED_TYPE\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "pred-type" [ aa ])  ->
		let
		(aa',ps) = fromATermSORTS (getATermByIndexSp1 aa att)
		ab'      = insertPos ps pos_l
		in (Pred_type aa' ab')
	    _ -> fromATermError "PRED_TYPE" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "pred-type" []
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-PRED-TYPE" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible PRED_HEAD where
    toATerm _ _ = error "*** toATerm for \"PRED_HEAD\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "pred-head" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Pred_head aa' ab')
	    _ -> fromATermError "PRED_HEAD" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "pred-head" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-PRED-HEAD" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible DATATYPE_DECL where
    toATerm _ _ = error "*** toATerm for \"DATATYPE_DECL\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "datatype-decl" [ aa,ab,ac ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		as  = fromATerm (getATermByIndexSp1 ac att)
		ab''= (addLAnnoList as $ head ab'):(tail ab')
		ac' = pos_l
		in (Datatype_decl aa' ab'' ac')
	    _ -> fromATermError "DATATYPE_DECL" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "datatype-decl" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-DATATYPE-DECL" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible ALTERNATIVE where
    toATerm _ _ = error "*** toATerm for \"ALTERNATIVE\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "total-construct" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Total_construct aa' ab' ac')
	    (AAppl "partial-construct" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Partial_construct aa' ab' ac')
	    (AAppl "subsort" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Subsorts aa' ab')
	    _ -> fromATermError "ALTERNATIVE" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "total-construct" [ ]) ,
			(AAppl "partial-construct" [ ]) ,
			(AAppl "subsort" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-ALTERNATIVE" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible COMPONENTS where
    toATerm _ _ = error "*** toATerm for \"COMPONENTS\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "total-select" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Total_select aa' ab' ac')
	    (AAppl "partial-select" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Partial_select aa' ab' ac')
	    (AAppl "sort-component" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (Sort aa')
	    _ -> fromATermError "COMPONENTS" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "total-select" [ ]) ,
			(AAppl "partial-select" [ ]) ,
			(AAppl "sort-component" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-COMPONENTS" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible VAR_DECL where
    toATerm _ _ = error "*** toATerm for \"VAR_DECL\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "tuple" [ aa,ab ])  ->
		let
		aa' = fromATermVARs (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		in (Var_decl aa' ab' [])
	    _ -> fromATermError "VAR_DECL" aterm
	where
	    Just aterm = getATermSp att $ AAppl "tuple" [ ]

instance ATermConvertible FORMULA where
    toATerm _ _ = error "*** toATerm for \"FORMULA\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "quantification" [ aa,ab,ac ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		pq  = getPos (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		ad' = insertPos pq pos_l
		in (Quantification aa' ab' ac' ad')
	    (AAppl "conjunction" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Conjunction aa' ab')
	    (AAppl "disjunction" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Disjunction aa' ab')
	    (AAppl "implication" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Implication aa' ab' ac')
	    (AAppl "equivalence" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Equivalence aa' ab' ac')
	    (AAppl "negation" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Negation aa' ab')
            -- the following things are from SML-type ATOM 
	    AAppl "atom" [AAppl "ttrue" []]  ->
		let
		aa' = pos_l
		in (True_atom aa')
	    AAppl "atom" [AAppl "ffalse" []]  ->
		let
		aa' = pos_l
		in (False_atom aa')
	    AAppl "atom" [AAppl "predication" [ aa,ab ]]  ->
		let
		aa'      = fromATerm (getATermByIndexSp1 aa att)
		(ab',ps) = fromATermTERMS (getATermByIndexSp1 ab att)
		ac'      = insertPos ps pos_l
		in (Predication aa' ab' ac')
	    AAppl "atom" [AAppl "definedness" [ aa ]]  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Definedness aa' ab')
	    AAppl "atom" [AAppl "existl-equation" [ aa,ab ]]  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Existl_equation aa' ab' ac')
	    AAppl "atom" [AAppl "strong-equation" [ aa,ab ]]  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Strong_equation aa' ab' ac')
	    AAppl "atom" [AAppl "membership" [ aa,ab ]]  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Membership aa' ab' ac')
	    _ -> fromATermError "FORMULA" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "quantification" [ ]) ,
			(AAppl "conjunction" [ ]) ,
			(AAppl "disjunction" [ ]) ,
			(AAppl "implication" [ ]) ,
			(AAppl "equivalence" [ ]) ,
			(AAppl "negation" [ ]) ,
			-- the ATOM datatype form SML below
			AAppl "atom" [AAppl "ttrue" [ ]] ,
			AAppl "atom" [AAppl "ffalse" [ ]] ,
			AAppl "atom" [AAppl "predication" [ ]] ,
			AAppl "atom" [AAppl "definedness" [ ]] ,
			AAppl "atom" [AAppl "existl-equation" [ ]] ,
			AAppl "atom" [AAppl "strong-equation" [ ]] ,
			AAppl "atom" [AAppl "membership" [ ]]]
	    (pos_l,g_flag,att') = skipPosFlag "pos-FORMULA" att

---- a helper for the SML-datatype TERMS -------------------------------
fromATermTERMS :: ATermTable -> ([TERM],[Pos])
fromATermTERMS att = 
    case aterm of
	     (AAppl "terms" [ aa ])  ->
		 (fromATerm (getATermByIndexSp1 aa att),pos_l)		
	     _ -> fromATermError "([TERM],[Pos])" aterm
    where aterm = getATerm att'
	  (pos_l,att') =
	      case getATerm att of
	      (AAppl "pos-TERMS" [reg_i,item_i]) ->
		       (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
	      _  -> ([],att)

---- a helper for SIMPLE_IDs --------------------------------------------

fromATermSIMPLE_ID :: ATermTable -> SIMPLE_ID
fromATermSIMPLE_ID att = 
    case aterm of
      (AAppl "tuple" [ si, _ ]) -> -- snd element is 'None' 
                                  -- (CASL.grm:((WORDS,None)))
          let s = fromATerm $ getATermByIndexSp1 si att
	  in Token s (0,0)
      _ -> fromATermError "SIMPLE_ID" aterm
    where aterm = getATerm att

---- a helper for [VAR] -------------------------------------------------
fromATermVARs :: ATermTable -> [VAR]
fromATermVARs att = map fromATermSIMPLE_ID att_list
    where att_list = case getATerm att of
		     AList l -> map getAtt l
		     _       -> fromATermError "[VAR]" $ getATerm att
	  getAtt ai = getATermByIndexSp1 ai att

-------------------------------------------------------------------------

instance ATermConvertible QUANTIFIER where
    toATerm _ _ = error "*** toATerm for \"QUANTIFIER\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "forall" [ ])  ->
		let
		in Universal
	    (AAppl "exists" [ ])  ->
		let
		in Existential
	    (AAppl "exists-uniquely" [ ])  ->
		let
		in Unique_existential
	    _ -> fromATermError "QUANTIFIER" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "forall" [ ]) ,(AAppl "exists" [ ]) ,
			(AAppl "exists-uniquely" [ ]) ]
	    att' =
		case getATerm att of
		(AAppl "pos-QUANTIFIER" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

instance ATermConvertible PRED_SYMB where
    toATerm _ _ = error "*** toATerm for \"PRED_SYMB\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "pred-symb" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in case getATerm $ getATermByIndexSp1 ab att of
		   AAppl "None" [] -> 
		       (Pred_name aa')
		   AAppl "Some" [ aab ] -> 
		     let aab' = fromATerm (getATermByIndexSp1 aab att)
			 ac' = pos_l
		     in (Qual_pred_name aa' aab' ac')
		   _ -> fromATermError "Option" aterm
	    _ -> fromATermError "PRED_SYMB" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "pred-symb" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-PRED-SYMB" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible TERM where
    toATerm _ _ = error "*** toATerm for \"TERM\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "var-or-const" [ aa ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		in (Simple_id aa')
	    (AAppl "qual-var" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Qual_var aa' ab' ac')
	    (AAppl "application" [ aa,ab ])  ->
		let
		aa'      = fromATerm (getATermByIndexSp1 aa att)
		(ab',ps) = fromATermTERMS (getATermByIndexSp1 ab att)
		ac'      = insertPos ps pos_l
		in (Application aa' ab' ac')
	    (AAppl "sorted-term" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Sorted_term aa' ab' ac')
	    (AAppl "cast" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Cast aa' ab' ac')
	    (AAppl "conditional" [ aa,ab,ac ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		ad' = pos_l
		in (Conditional aa' ab' ac' ad')
	    _ -> fromATermError "TERM" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "var-or-const" [ ]) ,(AAppl "qual-var" [ ]) ,
			(AAppl "application" [ ]) ,(AAppl "sorted-term" [ ]) ,
			(AAppl "cast" [ ]) ,(AAppl "conditional" [ ]) ]
	    (pos_l,p_flag,att') = skipPosFlag "pos-TERM" att

instance ATermConvertible OP_SYMB where
    toATerm _ _ = error "*** toATerm for \"OP_SYMB\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "op-symb" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in case getATerm $ getATermByIndexSp1 ab att of
		   AAppl "None" [] -> 
		       (Op_name aa')
		   AAppl "Some" [ aab ] -> 
		     let aab' = fromATerm (getATermByIndexSp1 aab att)
			 ac' = pos_l
		     in (Qual_op_name aa' aab' ac')
		   _ -> fromATermError "Option" aterm
	    _ -> fromATermError "OP_SYMB" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "op-symb" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-OP-SYMB" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible SYMB_ITEMS where
    toATerm _ _ = error "*** toATerm for \"SYMB_ITEMS\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "symb-items" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Symb_items aa' ab' ac')
	    _ -> fromATermError "SYMB_ITEMS" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "symb-items" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-SYMB-ITEMS" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible SYMB_MAP_ITEMS where
    toATerm _ _ = error "*** toATerm for \"SYMB_MAP_ITEMS\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "symb-map-items" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Symb_map_items aa' ab' ac')
	    _ -> fromATermError "SYMB_MAP_ITEMS" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "symb-map-items" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-SYMB-MAP-ITEMS" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible SYMB_KIND where
    toATerm _ _ = error "*** toATerm for \"SYMB_KIND\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "implicitk" [ ])  ->
		Implicit
	    (AAppl "sortsk" [ ])  ->
		Sorts_kind
	    (AAppl "opsk" [ ])  ->
		Ops_kind
	    (AAppl "predsk" [ ])  ->
		Preds_kind
	    _ -> fromATermError "SYMB_KIND" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "implicitk" [ ]) ,(AAppl "sortsk" [ ]) ,
			(AAppl "opsk" [ ]) ,(AAppl "predsk" [ ]) ]
	    att' =
		case getATerm att of
		(AAppl "pos-SYMB-KIND" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

instance ATermConvertible SYMB where
    toATerm _ _ = error "*** toATerm for \"SYMB\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "symb-id" [ aa ])  ->
		let
		i  = fromATerm (getATermByIndexSp1 aa att)
		aa' = setFstPos pos_l i
		in (Symb_id aa')
	    (AAppl "qual-id" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Qual_id aa' ab' ac')
	    _ -> fromATermError "SYMB" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "symb-id" [ ]) ,(AAppl "qual-id" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-SYMB" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible TYPE where
    toATerm _ _ = error "*** toATerm for \"TYPE\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "op-symb-type" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (O_type aa')
	    (AAppl "pred-symb-type" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (P_type aa')
	    _ -> fromATermError "TYPE" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "op-symb-type" [ ]) ,
			(AAppl "pred-symb-type" [ ]) ]
	    att' =
		case getATerm att of
		(AAppl "pos-TYPE" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

instance ATermConvertible SYMB_OR_MAP where
    toATerm _ _ = error "*** toATerm for \"SYMB_OR_MAP\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "symb" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (Symb aa')
	    (AAppl "symb-or-map" [ aa ])  ->
		let
		(aa',ab') = fromATermSYMB_MAP (getATermByIndexSp1 aa att)
		ac' = pos_l
		in (Symb_map aa' ab' ac')
	    _ -> fromATermError "SYMB_OR_MAP" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "symb" [ ]) ,(AAppl "symb-or-map" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-SYMB-OR-MAP" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

---- a helper for SYMB_MAP from SML -------------------------------------

fromATermSYMB_MAP :: ATermTable -> (SYMB,SYMB)
fromATermSYMB_MAP att =
	case aterm of
	    (AAppl "symb-map" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		in (aa',ab')
	    _ -> fromATermError "(SYMB,SYMB)" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "symb-map" [ ]
	    att' =
		case getATerm att of
		(AAppl "pos-SYMB-MAP" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

-------------------------------------------------------------------------

----- instances of AS_Structured.hs -------------------------------------
instance ATermConvertible SPEC where
    toATerm _ _ = error "*** toATerm for \"SPEC\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "basic" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		aa'' = G_basic_spec CASL aa'
		in group (AS_Structured.Basic_spec aa'') group_flag
	    (AAppl "translation" [ aa,ab,_ ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		in group (Translation aa' ab') group_flag
	    (AAppl "reduction" [ aa,ab,_ ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		in group (Reduction aa' ab') group_flag
	    (AAppl "union-spec" [ aa ])  ->
		let
		aa' :: [(Annoted SPEC,[Annotation])]
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in group (Union (toAnnotedList aa') ab') group_flag
	    (AAppl "extension" [ aa ])  ->
		let
		aa' :: [(Annoted SPEC,[Annotation])]
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in group (Extension (toAnnotedList aa') ab') group_flag
	    (AAppl "free-spec" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		aa''= addLAnnoList (toAnnoList ab att) aa'
		ab' = pos_l
		in group (Free_spec aa'' ab') group_flag
	    (AAppl "local-spec" [ aa,ab,ac,ad ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		sp1 = addLAnnoList (toAnnoList ab att) aa'
		ac' = fromATerm (getATermByIndexSp1 ac att)
		sp2 = addLAnnoList (toAnnoList ad att) ac'
		in group (Local_spec sp1 sp2 pos_l) group_flag
	    (AAppl "closed-spec" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		aa''= addLAnnoList (toAnnoList ab att) aa'
		ab' = pos_l
		in group (Closed_spec aa'' ab') group_flag
	    (AAppl "spec-inst" [ aa,ab ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		in (Spec_inst aa' ab')
	    _ -> fromATermError "SPEC" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "basic" [ ]) ,(AAppl "translation" [ ]) ,
			(AAppl "reduction" [ ]) ,(AAppl "union-spec" [ ]) ,
			(AAppl "extension" [ ]) ,(AAppl "free-spec" [ ]) ,
			(AAppl "local-spec" [ ]) ,(AAppl "closed-spec" [ ]) ,
			(AAppl "spec-inst" [ ]) ]
	    group s gf = if gf then (Group s' pos_l) else s
		where s' = Annoted s [] [] []
	    (pos_l,group_flag,att') = skipPosFlag "pos-SPEC" att

--- a helper function for [(Annoted a, [Annotation])] --------------------

toAnnotedList :: forall a . [(Annoted a,[Annotation])] -> [Annoted a]
toAnnotedList xs = map merge xs
    where merge (ai,as) = ai { l_annos = (l_annos ai) ++ as}

--------------------------------------------------------------------------

instance ATermConvertible RENAMING where
    toATerm _ _ = error "*** toATerm for \"RENAMING\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "renaming" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		aa''= if null aa' then [] 
		      else [G_symb_map $ G_symb_map_items_list CASL aa']
		ab' = pos_l
		in (Renaming aa'' ab')
	    _ -> fromATermError "RENAMING" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "renaming" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-RENAMING" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible RESTRICTION where
    toATerm _ _ = error "*** toATerm for \"RESTRICTION\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "hide" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		aa''= if null aa' then [] 
		      else [G_symb_list $ G_symb_items_list CASL aa']
		ab' = pos_l
		in (Hidden aa'' ab')
	    (AAppl "reveal" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		aa''= G_symb_map_items_list CASL aa'
		ab' = pos_l
		in (Revealed aa'' ab')
	    _ -> fromATermError "RESTRICTION" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "hide" [ ]) ,(AAppl "reveal" [ ])]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-RESTRICTION" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

{- !!! This will be done by the instance of LIB_ITEM !!!

instance ATermConvertible SPEC_DEFN where
    toATerm att0 (Spec_defn aa ab ac ad) =
	let (att1,aa') = toATerm att0 aa
	    (att2,ab') = toATerm att1 ab
	    (att3,ac') = toATerm att2 ac
	    (att4,ad') = toATerm att3 ad
	    lat = [ aa',ab',ac',ad' ]
	in addATermSp (AAppl "spec-defn"  lat)  att4
    fromATerm att =
	case aterm of
	    (AAppl "spec-defn" [ aa,ab,ac,ad ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		ad' = pos_l
		in (Spec_defn aa' ab' ac' ad')
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "spec-defn" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-SPEC-DEFN" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)
-}

instance ATermConvertible GENERICITY where
    toATerm _ _ = error "*** toATerm for \"GENERICITY\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "genericity" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Genericity aa' ab' ac')
	    _ -> fromATermError "GENERICITY" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "genericity" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-GENERICITY" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible PARAMS where
    toATerm _ _ = error "*** toATerm for \"PARAMS\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "params" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (Params aa')
	    _ -> fromATermError "PARAMS" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "params" [ ]
	    att' =
		case getATerm att of
		(AAppl "pos-PARAMS" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

instance ATermConvertible IMPORTED where
    toATerm _ _ = error "*** toATerm for \"IMPORTED\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "imports" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (Imported aa')
	    _ -> fromATermError "IMPORTED" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "imports" [ ]
	    att' =
		case getATerm att of
		(AAppl "pos-IMPORTS" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

instance ATermConvertible FIT_ARG where
    toATerm _ _ = error "*** toATerm for \"FIT_ARG\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "fit-spec" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ab''= G_symb_map_items_list CASL ab'
		ac' = pos_l
		in (Fit_spec aa' ab'' ac')
	    (AAppl "fit-view" [ aa,ab ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Fit_view aa' ab' ac' [])
	    _ -> fromATermError "FIT_ARG" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "fit-spec" [ ]) ,(AAppl "fit-view" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-FIT-ARG" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)
{- !!! This conversion is covered by the instance of LIB_ITEM !!!

instance ATermConvertible VIEW_DEFN where
    toATerm att0 (View_defn aa ab ac ad ae) =
	let (att1,aa') = toATerm att0 aa
	    (att2,ab') = toATerm att1 ab
	    (att3,ac') = toATerm att2 ac
	    (att4,ad') = toATerm att3 ad
	    (att5,ae') = toATerm att4 ae
	    lat = [ aa',ab',ac',ad',ae' ]
	in addATermSp (AAppl "view-defn"  lat)  att5
    fromATerm att =
	case aterm of
	    (AAppl "view-defn" [ aa,ab,ac,ad,ae ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		ad' = fromATerm (getATermByIndexSp1 ad att)
		ae' = pos_l
		in (View_defn aa' ab' ac' ad' ae')
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "view-defn" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-VIEW-DEFN" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)
-}

instance ATermConvertible VIEW_TYPE where
    toATerm _ _ = error "*** toATerm for \"VIEW_TYPE\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "view-type" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (View_type aa' ab' ac')
	    _ -> fromATermError "VIEW_TYPE" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "view-type" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-VIEW-TYPE" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

-------------------------------------------------------------------------

----- instances of AS_Architecture.hs -----------------------------------
{- !!! This conversion is covered by the instance of LIB_ITEM !!!

instance ATermConvertible ARCH_SPEC_DEFN where
    toATerm att0 (Arch_spec_defn aa ab ac) =
	let (att1,aa') = toATerm att0 aa
	    (att2,ab') = toATerm att1 ab
	    (att3,ac') = toATerm att2 ac
	    lat = [ aa',ab',ac' ]
	in addATermSp (AAppl "arch-spec-defn"  lat)  att3
    fromATerm att =
	case aterm of
	    (AAppl "arch-spec-defn" [ aa,ab,ac ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Arch_spec_defn aa' ab' ac')
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "arch-spec-defn" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-ARCH-SPEC-DEFN" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

-}

instance ATermConvertible ARCH_SPEC where
    toATerm _ _ = error "*** toATerm for \"ARCH_SPEC\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "basic-arch-spec" [ aa,ab,ac ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATermRESULT_UNIT (getATermByIndexSp1 ab att)
		as  = toAnnoList ac att
		aa''= (addLAnnoList as $ head aa'):tail aa'
		ac' = pos_l
		in (Basic_arch_spec aa'' ab' ac')
	    (AAppl "named-arch-spec" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (Arch_spec_name aa')
	    _ -> fromATermError "ARCH_SPEC" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "basic-arch-spec" [ ]) ,
			(AAppl "named-arch-spec" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-ARCH-SPEC" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

--------------------------------------------------------------------------
fromATermRESULT_UNIT :: ATermTable -> (Annoted UNIT_EXPRESSION)
fromATermRESULT_UNIT att = 
	case aterm of
	    (AAppl "result-unit" [ aa,ab ])  ->
		let
--		aa' :: UNIT_EXPRESSION
		aa' = fromATerm (getATermByIndexSp1 aa att)
		as  = toAnnoList ab att
		in (Annoted aa' [] as [])
	    _ -> fromATermError "RESULT-UNIT" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "result-unit" [ ]
	    att' =
		case getATerm att of
		(AAppl "pos-RESULT-UNIT" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

--------------------------------------------------------------------------


instance ATermConvertible UNIT_DECL_DEFN where
    toATerm _ _ = error "*** toATerm for \"UNIT_DECL_DEFN\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "unit-decl-case" [ udl ])  ->
		let att1 = getATermByIndexSp1 udl att
		    (ps,att2) = case getATerm att1 of
				  (AAppl "pos-UNIT-DECL" [reg_i,item_i]) ->
				      (fromATerm_reg reg_i att,
				       getATermByIndexSp1 item_i att1)
				  _  -> ([],att1)
		    aterm2 = getATerm att2
		in case aterm2 of
		   AAppl "unit-decl" [aa,ab,ac] -> 
		      let aa'  = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
			  ab'  = fromATerm (getATermByIndexSp1 ab att)
			  ac'  = fromATermUNIT_IMPORTS $ 
			                 getATermByIndexSp1 ac att
			  ad'  = ps
		      in (Unit_decl aa' ab' ac' ad')
		   _ -> fromATermError "UNIT_DECL" aterm2
	    (AAppl "unit-defn-case" [ udn ])  ->
		fromATermUNIT_DEFN $ getATermByIndexSp1 udn att
	    (AAppl "pos-UNIT-DEFN" _) ->
		fromATermUNIT_DEFN att
	    (AAppl "unit-defn" _) ->
		fromATermUNIT_DEFN att
	    _ -> fromATermError "UNIT-DECL-DEFN" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [AAppl "unit-decl-case" [],
			AAppl "unit-defn-case" [],
		        AAppl "pos-UNIT-DEFN" [],
		        AAppl "unit-defn" []]
	    att' =
		case getATerm att of
		(AAppl "pos-UNIT-DECL-DEFN" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

---- a helper for the SML-datatype UNIT_IMPORTS ------------------------

fromATermUNIT_IMPORTS :: ATermTable -> [Annoted UNIT_TERM]
fromATermUNIT_IMPORTS att = 
    case aterm of
	     (AAppl "unit-imports" [ aa ])  ->
		 fromATerm $ getATermByIndexSp1 aa att
	     _ -> fromATermError "UNIT_IMPORTS" aterm
    where aterm = getATerm att'
	  att' =
	      case getATerm att of
	      (AAppl "pos-UNIT-IMPORTS" [_,item_i]) ->
		  getATermByIndexSp1 item_i att
	      _  -> att

-------------------------------------------------------------------------
fromATermUNIT_DEFN :: ATermTable -> UNIT_DECL_DEFN
fromATermUNIT_DEFN att =
    case aterm of
    AAppl "unit-defn" [aa,ab] -> 
	let aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
	    ab' = fromATerm (getATermByIndexSp1 ab att)
	    ac' = ps
        in (Unit_defn aa' ab' ac')
    _ -> fromATermError "UNIT_DEFN" aterm
    where aterm = getATerm att'
	  (ps,att') =
	      case getATerm att of
	      (AAppl "pos-UNIT-DEFN" [reg_i,item_i]) ->
		  (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
	      _  -> ([],att)
-------------------------------------------------------------------------

{- !!! This conversion is covered by the instance of LIB_ITEM !!!

instance ATermConvertible UNIT_SPEC_DEFN where
    toATerm att0 (Unit_spec_defn aa ab ac) =
	let (att1,aa') = toATerm att0 aa
	    (att2,ab') = toATerm att1 ab
	    (att3,ac') = toATerm att2 ac
	    lat = [ aa',ab',ac' ]
	in addATermSp (AAppl "unit-spec-defn"  lat)  att3
    fromATerm att =
	case aterm of
	    (AAppl "unit-spec-defn" [ aa,ab,ac ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Unit_spec_defn aa' ab' ac')
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "unit-spec-defn" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-UNIT-SPEC-DEFN" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)
-}

instance ATermConvertible UNIT_SPEC where
    toATerm _ _ = error "*** toATerm for \"UNIT_SPEC\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "unit-type-case" [ aa ])  ->
		let
		(aa',ab') = fromATermUNIT_TYPE $ getATermByIndexSp1 aa att
		ac' = pos_l
		in (Unit_type aa' ab' ac')
	    (AAppl "spec-name-case" [ aa ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		in (Spec_name aa')
	    (AAppl "arch-spec-case" [ aa,ab ])  ->
		let
		aa'   = fromATerm (getATermByIndexSp1 aa att)
		ps    = toAnnoList ab att
		aa''  = addLAnnoList ps aa'
		ab'   = pos_l
		aa''' = case aa'' of
		        (Annoted (Basic_arch_spec _ _ _) _ _ _) ->
			    Annoted (Group_arch_spec aa'' ab') [] [][] 
			_ -> aa''
		in (Arch_unit_spec aa''' ab')
	    (AAppl "closed" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Closed_unit_spec aa' ab')
	    _ -> fromATermError "UNIT_SPEC" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "unit-type-case" [ ]) ,
			(AAppl "spec-name-case" [ ]) ,
			(AAppl "arch-spec-case" [ ]) ,
			(AAppl "closed" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-UNIT-SPEC" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

---- a helper for the SML-datatype UNIT_TYPE ----------------------------

fromATermUNIT_TYPE :: ATermTable -> ([Annoted SPEC],(Annoted SPEC))
fromATermUNIT_TYPE att = 
    case aterm of
	     (AAppl "unit-type" [ aa,ab ])  ->
		 (fromATerm $ getATermByIndexSp1 aa att,
		  fromATerm $ getATermByIndexSp1 ab att)
	     _ -> fromATermError "UNIT_TYPE" aterm
    where aterm = getATerm att'
	  att' =
	      case getATerm att of
	      (AAppl "pos-UNIT-TYPE" [_,item_i]) ->
		  getATermByIndexSp1 item_i att
	      _  -> att

-------------------------------------------------------------------------

instance ATermConvertible UNIT_EXPRESSION where
    toATerm _ _ = error "*** toATerm for \"UNIT_EXPRESSION\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "unit-expression" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Unit_expression aa' ab' ac')
	    _ -> fromATermError "UNIT_EXPRESSION" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "unit-expression" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-UNIT-EXPRESSION" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible UNIT_BINDING where
    toATerm _ _ = error "*** toATerm for \"UNIT_BINDING\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "unit-binding" [ aa,ab ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Unit_binding aa' ab' ac')
	    _ -> fromATermError "UNIT_BINDING" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "unit-binding" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-UNIT-BINDING" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible UNIT_TERM where
    toATerm _ _ = error "*** toATerm for \"UNIT_TERM\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "unit-reduction" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		in group (Unit_reduction aa' ab') group_flag
	    (AAppl "unit-translation" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		in group (Unit_translation aa' ab') group_flag
	    (AAppl "amalgamation" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in group (Amalgamation aa' ab') group_flag
	    (AAppl "local-unit" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in group (Local_unit aa' ab' ac') group_flag
	    (AAppl "unit-appl" [ aa,ab ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in group (Unit_appl aa' ab' ac') group_flag
	    _ -> fromATermError "UNIT_TERM" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "unit-reduction" [ ]) ,
			(AAppl "unit-translation" [ ]) ,
			(AAppl "amalgamation" [ ]) ,
			(AAppl "local-unit" [ ]) ,
			(AAppl "unit-appl" [ ]) ]
	    group ut gf = if gf then (Group_unit_term ut' pos_l) else ut
		where ut' = Annoted ut [] [] []
	    (pos_l,group_flag,att') = skipPosFlag "pos-UNIT-TERM" att

instance ATermConvertible FIT_ARG_UNIT where
    toATerm _ _ = error "*** toATerm for \"FIT_ARG_UNIT\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "fit-arg-unit" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ab''= G_symb_map_items_list CASL ab'
		ac' = pos_l
		in (Fit_arg_unit aa' ab'' ac')
	    _ -> fromATermError "FIT_ARG_UNIT" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "fit-arg-unit" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-FIT-ARG-UNIT" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)
-------------------------------------------------------------------------

----- instances of AS_LIbrary.hs ----------------------------------------
instance ATermConvertible LIB_DEFN where
    toATerm _ _ = error "*** toATerm for \"LIB_DEFN\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "lib-defn" [ aa,ab,ad ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		ad' = fromATerm (getATermByIndexSp1 ad att)
		in (Lib_defn aa' ab' ac' ad')
	    _ -> fromATermError "LIB_DEFN" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "lib-defn" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-LIB-DEFN" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible LIB_ITEM where
    toATerm _ _ = error "*** toATerm for \"LIB_ITEM\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "spec-defn" [ aa,ab,ac,ad ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		as  = toAnnoList ad att
		ac''= addLAnnoList as ac'
		ad' = pos_l
		in AS_Library.Spec_defn aa' ab' ac'' ad'
	    (AAppl "view-defn" [ aa,ab,ac,ad,_ ])  ->
		let  -- the annotation list is lost !!!!
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = fromATerm (getATermByIndexSp1 ac att)
		ad' = fromATerm (getATermByIndexSp1 ad att)
		ad''= if null ad' then [] 
		      else [G_symb_map $ G_symb_map_items_list CASL ad']
{-		as  = toAnnoList ae att
		ac''= addLAnnoList as ac'-}
		ae' = pos_l
		in (AS_Library.View_defn aa' ab' ac' ad'' ae')
	    (AAppl "arch-spec-defn" [ aa,ab,_ ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (AS_Library.Arch_spec_defn aa' ab' ac')
	    (AAppl "unit-spec-defn" [ aa,ab,_ ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (AS_Library.Unit_spec_defn aa' ab' ac')
	    (AAppl "download-items" [ aa,ab,_ ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (AS_Library.Download_items aa' ab' ac')
	    _ -> fromATermError "LIB_ITEM" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "spec-defn" [ ]) ,
			(AAppl "view-defn" [ ]) ,
			(AAppl "arch-spec-defn" [ ]) ,
			(AAppl "unit-spec-defn" [ ]) ,
			(AAppl "download-items" [ ]) ]
	    (pos_l,att') = skipPos "pos-LIB-ITEM" att

---- helpers to skip nested "pos-"-constructors -----------------------
skipPos :: String -> ATermTable -> ([Pos],ATermTable)
skipPos mcon at   = 
     case getATerm at of
	      AAppl con [reg_i,item_i] | mcon == con ->
		  if pCon then skipPos mcon at'
		  else (fromATerm_reg (reg_i) at, at')
		      where pCon = case getATerm at' of
				   AAppl con' _ | mcon == con' -> True
				   _                           -> False
			    at'  = getATermByIndexSp1 item_i at
	      _  -> ([],at)

skipPosFlag :: String -> ATermTable -> ([Pos],Bool,ATermTable)
skipPosFlag mcon att   = 		
    case getATerm att of
    AAppl con [reg_i,b_i,item_i] | mcon == con ->
          if pCon then let (r_pos_l,r_b,r_at') = skipPosFlag mcon at'
		       in (pos_l,r_b || b,r_at')
	  else (pos_l,b,at')
	      where pCon  = case getATerm at' of
			    AAppl con' _ | mcon == con' -> True
			    _                           -> False
		    at'   = getATermByIndexSp1 item_i att
		    pos_l = fromATerm_reg reg_i att
		    b     = fromATerm $ getATermByIndexSp1 b_i att
    _  -> ([],False,att)

-----------------------------------------------------------------------

instance ATermConvertible ITEM_NAME_OR_MAP where
    toATerm _ _ = error "*** toATerm for \"ITEM_NAME_OR_MAP\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "item-name" [ aa ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		in (Item_name aa')
	    (AAppl "item-name-map" [ aa,ab ])  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndexSp1 aa att)
		ab' = fromATermSIMPLE_ID (getATermByIndexSp1 ab att)
		ac' = pos_l
		in (Item_name_map aa' ab' ac')
	    _ -> fromATermError "ITEM_NAME_OR_MAP" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "item-name" [ ]) ,
			(AAppl "item-name-map" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-ITEM-NAME-OR-MAP" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible LIB_NAME where
    toATerm _ _ = error "*** toATerm for \"LIB_NAME\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "versioned-lib" [ aa,ab ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = fromATerm (getATermByIndexSp1 ab att)
		in (Lib_version aa' ab')
	    (AAppl "lib" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		in (Lib_id aa')
	    _ -> fromATermError "LIB_NAME" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "versioned-lib" [ ]) ,(AAppl "lib" [ ]) ]
	    att' =
		case getATerm att of
		(AAppl "pos-LIB-NAME" [_,item_i]) ->
		    getATermByIndexSp1 item_i att
		_  -> att

instance ATermConvertible LIB_ID where
    toATerm _ _ = error "*** toATerm for \"LIB_ID\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "url" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Direct_link aa' ab')
	    (AAppl "path-name" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Indirect_link aa' ab')
	    _ -> fromATermError "LIB_NAME" aterm
	where
	    aterm = findATerm att' (map (getATermSp att') pat_list)
	    pat_list = [(AAppl "url" [ ]) ,
			(AAppl "path-name" [ ]) ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-LIB-ID" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)

instance ATermConvertible VERSION_NUMBER where
    toATerm _ _ = error "*** toATerm for \"VERSION_NUMBER\" not implemented"
    fromATerm att =
	case aterm of
	    (AAppl "version" [ aa ])  ->
		let
		aa' = fromATerm (getATermByIndexSp1 aa att)
		ab' = pos_l
		in (Version_number aa' ab')
	    _ -> fromATermError "VERSION_NUMBER" aterm
	where
	    Just aterm = getATermSp att' $ AAppl "version" [ ]
	    (pos_l,att') =
		case getATerm att of
		(AAppl "pos-VERSION" [reg_i,item_i]) ->
		    (fromATerm_reg reg_i att,getATermByIndexSp1 item_i att)
		_  -> ([],att)
-------------------------------------------------------------------------

-- some helpers for Annoted things --------------------------------------
addLAnnoList :: forall a . [Annotation] -> Annoted a -> Annoted a
addLAnnoList as ani = ani {l_annos = as ++ (l_annos ani) }

addRAnnoList :: forall a . [Annotation] -> Annoted a -> Annoted a
addRAnnoList as ani = ani {r_annos = (r_annos ani) ++ as } 

--- some helpers for Regions and Positions ------------------------------
getPos :: ATermTable -> [Pos]
getPos att = case getATerm att of
		AAppl _ (x:_) -> fromATerm_reg x att
		_       -> []


insertIM :: [a] -> [a] -> [a]
insertIM ips ops | even $ length ops = let hl = (length ops) `div` 2
					   (fp,lp) = splitAt hl ops
				       in fp ++ ips ++ lp
		 | otherwise = error 
			       "wrong call: length of snd list must be even"
insertPos = insertIM

setFstPos :: [Pos] -> Id -> Id
setFstPos (p:_) i = case i of
		       Id tops ids pos_l ->
			   Id (setFstPos' tops) ids pos_l
    where setFstPos' tops | null tops = []
			  | otherwise = (ftop):(tail tops)
	      where ftop = (head tops) { tokPos = p }
setFstPos _ _ = error "wrong call: setFstPos"

-------------------------------------------------------------------------
