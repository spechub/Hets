{-# OPTIONS -fallow-overlapping-instances #-}
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

import Data.List (isPrefixOf)

import Common.ATerm.Lib

import Common.Utils

import Common.Id
import Common.AS_Annotation

import CASL.AS_Basic_CASL

import CASL.Logic_CASL
import Logic.Grothendieck

import Syntax.AS_Structured
import Syntax.AS_Architecture
import Syntax.AS_Library

-- the following module provides the ability to parse the "unparsed-anno"
import Common.Lib.Parsec (parse,setPosition)
import Common.Lib.Parsec.Pos (newPos)
import qualified Common.Anno_Parser (annotations,parse_anno)
import Common.Lexer(skip)

from_sml_ATerm :: ATermTable -> LIB_DEFN
read_sml_ATerm :: FilePath -> IO LIB_DEFN

from_sml_ATerm = fromShATerm
read_sml_ATerm fn = readFile fn >>= return . fromATermString 

----- instances of Id.hs ------------------------------------------------
instance ATermConvertible Token where
    toATerm _ = error "*** toATerm for \"Token\" not implemented"
    fromATerm = error "*** fromATerm for \"Token\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"Token\" not implemented"
    fromShATerm att =
        case aterm of
            (ShAAppl "token" [ aa ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = nullPos
                in (Token aa' ab')
            (ShAAppl "place" [] _)  ->
                let
                aa' = Common.Id.place
                ab' = nullPos
                in (Token aa' ab')
	    _ -> fromShATermError "Token" aterm
        where
            aterm = getATerm att

instance ATermConvertible Id where
    toATerm _ = error "*** toATerm for \"Id\" not implemented"
    fromATerm _ = error "*** fromATerm for \"Id\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"Id\" not implemented"
    fromShATerm att =
        case aterm of
            (ShAAppl "compound-id" [ aa,ab ] _)  -> -- TOKEN_OR_MIXFIX,[ID]
                let
                aa' = fromATermTokenTup (getATermByIndex1 aa att)
                ab' = fromShATerm (getATermByIndex1 ab att)
                ac' = []
                in (Id aa' ab' ac')
	    (ShAAppl "simple-id" [ aa ] _) ->
		let 
		aa' = fromATermTokenTup (getATermByIndex1 aa att)
		ab' = []
		ac' = []
                in (Id aa' ab' ac')
	    _ -> fromShATermError "Id" aterm
        where
            aterm = getATerm att

-------------------------------------------------------------------------
fromATermTokenTup :: ATermTable -> [Token]
fromATermTokenTup att = 
    case aterm of
       (ShAAppl "" [tops,_,_] _) ->
	   fromShATerm (getATermByIndex1 tops att)
       _         -> fromShATermError "Token" aterm
    where aterm = getATerm att

----- instances of AS_Annotation.hs -------------------------------------
instance ATermConvertible Annotation where
    toATerm _ = error "*** toATerm for \"Annotation\" not implemented"
    fromATerm _ = error "*** fromATerm for \"Annotation\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"Annotation\" not implemented"
    fromShATerm att =
        case aterm of
            (ShAAppl "comment-line" [ aa ] _)  ->
                let
                aa' = chomp $ fromShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Comment_line aa' ab')
            (ShAAppl "comment" [ aa ] _)  ->
                let
                aa' = lines (fromShATerm (getATermByIndex1 aa att))
                ab' = pos_l
                in (Comment_group aa' ab')
            (ShAAppl "unparsed-anno" [ aa ] _)  ->
		parse_anno pos_l 
		   (fromShATerm (getATermByIndex1 aa att))
            (ShAAppl "annote-line" [ aa,ab ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = fromShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Annote_line aa' ab' ac')
            (ShAAppl "annote-group" [ aa,ab ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = fromShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Annote_group aa' ab' ac')
            (ShAAppl "display-anno" [ aa,ab ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = parse_disp_anno aa' pos_l 
		           (chomp $ fromShATerm (getATermByIndex1 ab att))
                in ab'
            (ShAAppl "string-anno" [ aa,ab ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = fromShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (String_anno aa' ab' ac')
            (ShAAppl "list-anno" [ aa,ab,ac ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = fromShATerm (getATermByIndex1 ab att)
                ac' = fromShATerm (getATermByIndex1 ac att)
                ad' = pos_l
                in (List_anno aa' ab' ac' ad')
            (ShAAppl "number-anno" [ aa ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Number_anno aa' ab')
            (ShAAppl "floating-anno" [ aa,ab ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = fromShATerm (getATermByIndex1 ab att)
                ac' = pos_l
                in (Float_anno aa' ab' ac')
            (ShAAppl "prec-anno" [ aa,ab,ac ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = fromShATerm (getATermByIndex1 ab att)
                ac' = fromShATerm (getATermByIndex1 ac att)
                ad' = pos_l
                in (Prec_anno aa' ab' ac' ad')
            (ShAAppl "lassoc-anno" [ aa ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Lassoc_anno aa' ab')
            (ShAAppl "rassoc-anno" [ aa ] _)  ->
                let
                aa' = fromShATerm (getATermByIndex1 aa att)
                ab' = pos_l
                in (Rassoc_anno aa' ab')
            (ShAAppl "label-anno" [ aa ] _)  ->
                let
                aa' = 
		   lines (showId (fromShATerm (getATermByIndex1 aa att)) "")
                ab' = pos_l
                in (Label aa' ab')
            (ShAAppl "implies" [] _)  ->
                let
                aa' = pos_l
                in (Implies aa')
            (ShAAppl "definitional" [] _)  ->
                let
                aa' = pos_l
                in (Definitional aa')
            (ShAAppl "conservative" [] _)  ->
                let
                aa' = pos_l
                in (Conservative aa')
	    (ShAAppl "mono" [] _) ->
		Monomorph pos_l
	    _ -> fromShATermError "Annotation" aterm
        where
            aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-ANNO" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

--- Well the following instance has to tie together things, that don't
--- belong to each other. Because I can't declare instances for
--- certain "Annoted types"
instance (ATermConvertible a) => ATermConvertible (Annoted a) where
    toATerm _ = error "*** toATerm for \"(Annoted a)\" not implemented"
    fromATerm _ = error "*** fromATerm for \"(Annoted a)\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"(Annoted a)\" not implemented"
    fromShATerm att =
        case aterm of
         (ShAAppl con as _)  ->
	     (case con of
	       -- Basic Items (including sig_items)
	        "pos-BASIC-ITEMS" -> 
	              let (bi,las) = fromATermAnnotedBasic_Items att
	              in Annoted bi [] las []
	       -- L_.* constuctors from SML 
	        ""           -> Annoted (fromShATerm (getATermByIndex1 
						        (head as) 
						        att))
	                                     []
	                                     []
				             (toAnnoList (last as) att)
	        _      -> -- "No appropiate constructor for Annoted found"
 			Annoted (fromShATerm att)
			            []
				    []
				    []
	     )
	 _ -> fromShATermError "Annoted a" aterm
        where
            aterm = getATerm att
 
---- functions to convert annoted stuff ---------------------------------
-- all these functions are called by instance ATermConvertible Annoted a

fromATermAnnotedBasic_Items :: forall a . ATermConvertible a => 
			       ATermTable -> (a,[Annotation])
fromATermAnnotedBasic_Items att = 
    if isSig_items then
       ((fromShATerm att),[])
    else ((fromShATerm att),annoList)  
    where isSig_items = 
	      case aterm of
	      (ShAAppl _ as _)-> -- pos-BASIC-ITEMS
	            case getATerm $ getATermByIndex1 (last as) att of
		    (ShAAppl "sig-items" _ _) -> True
		    _                         -> False
	      _ -> fromShATermError "{SIG,BASIC}_items" aterm
	  aterm = getATerm att
 	  annoList = case getATerm att of
		     (ShAAppl _ as _) -> getAnnoList (last as) att
		     _                -> error "Wrong ATerm structure: BASIC_ITEMS"
{-	  att' = let (ShAAppl _ as _) = getATerm att -- pos-BASIC-ITEMS
		     (ShAAppl _ as' _) = getATerm $  -- sig-items
				     getATermByIndex1 (head as) att
	         in getATermByIndex1 (head as') att -}

{-fromATermAnnotedSig_Items :: ATermTable -> [SIG_ITEMS]
fromATermAnnotedSig_Items att =
-- Sig Items have an anno list which now is attached to
-- the first item
		  Just "s-items" -> 
		      let aterm' = getATerm (getATermByIndex1 (head as) att)
			       as'    = case aterm' of ShAAppl _ as _ -> as
	          in Annoted (fromShATerm att)
			     []
			     []
			     (getAnnoList (last as) att)
-}



-- getAnnoList and toAnnoList are only working with an AIndex as first
-- argument is given. If getAnnoList is called every ShAAppl that starts _
-- with "pos-" is crossed without consideration. toAnnoList just calls
-- the [Annotation] conversion directly.

getAnnoList :: Int -> ATermTable -> [Annotation]
getAnnoList ai att = case at of
		     ShAAppl c as _ | isPrefixOf "pos-" c -> 
				    getAnnoList (last as) att
		     ShAAppl _ as _ -> toAnnoList (last as) att
		     _          -> error "wrong storage or missed 'pos-' contructor" 
    where at = getATerm (getATermByIndex1 ai att)

toAnnoList :: Int -> ATermTable -> [Annotation]
toAnnoList ai att = fromShATerm $ getATermByIndex1 ai att

-------------------------------------------------------------------------

parse_anno :: [Pos] -> String -> Annotation
parse_anno pos_l inp =
    case (parse (set_pos Common.Anno_Parser.annotations) "" inp) of
       Left err   -> error ("internal parse error at " ++ (show err))
       Right [x]  -> x
       Right _    -> error ("something strange happend to \"" ++
			     inp ++ "\" during ATerm Conversion")
    where set_pos p = do setPosition sp
			 skip
			 p
	  sp = pos -- newPos "ATermConversion from SML" (fst pos) (snd pos)
	  pos = head pos_l

parse_disp_anno :: Id -> [Pos] -> String -> Annotation
parse_disp_anno i pos_l inp =
    case (Common.Anno_Parser.parse_anno (Annote_group "display" [inp'] pos_l) sp) of
       Left err   -> error ("internal parse error at " ++ (show err))
       --Right [] -> error $ "No displayanno: " ++ inp' 
       Right x  -> x -- trace ("parsed display anno:" ++ show x) x
       --Right xs   -> error $ "More than one displayanno" ++ show xs
    where sp = pos -- newPos "ATermConversion from SML" (fst pos) (snd pos)
	  pos = head pos_l
	  inp' = (showId i "") ++ (' ':s_inp)
	  s_inp = case reverse inp of
		  rin | "%)" `isPrefixOf` rin -> reverse $ drop 2 rin
		      | otherwise -> inp

----- instances of AS_Basic_CASL.hs -------------------------------------
instance ATermConvertible BASIC_SPEC where
    toATerm _ = error "*** toATerm for \"BASIC_SPEC\" not implemented"
    fromATerm _ = error "*** fromATerm for \"BASIC_SPEC\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"BASIC_SPEC\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "basic-spec" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (CASL.AS_Basic_CASL.Basic_spec aa')
	    _ -> fromShATermError "BASIC_SPEC" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-BASIC-SPEC" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

instance ATermConvertible BASIC_ITEMS where
    toATerm _ = error "*** toATerm for \"BASIC_ITEMS\" not implemented"
    fromATerm _ = error "*** fromATerm for \"BASIC_ITEMS\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"BASIC_ITEMS\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "sig-items" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (Sig_items aa')
	    (ShAAppl "free-datatype" [ aa,_ ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Free_datatype aa' ab')
	    (ShAAppl "sort-gen" [ aa,_ ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Sort_gen aa' ab')
	    (ShAAppl "var-items" [ aa,_ ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Var_items aa' ab')
	    (ShAAppl "local-var-axioms" [ aa,ab,_ ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Local_var_axioms aa' ab' ac')
	    (ShAAppl "axiom-items" [ aa,_ ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Axiom_items aa' ab')	    
	    _ -> fromShATermError "BASIC_ITEMS" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-BASIC-ITEMS" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible SIG_ITEMS where
    toATerm _ = error "*** toATerm for \"SIG_ITEMS\" not implemented"
    fromATerm _ = error "*** fromATerm for \"SIG_ITEMS\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"SIG_ITEMS\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "sort-items" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		as  = fromShATerm (getATermByIndex1 ab att)
       		aa'' = (addLAnnoList as $ head aa'):(tail aa')
		ab' = pos_l
		in (Sort_items aa'' ab')
	    (ShAAppl "op-items" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		as  = fromShATerm (getATermByIndex1 ab att)
		aa'' = (addLAnnoList as $ head aa'):(tail aa')
		ab' = pos_l
		in (Op_items aa'' ab')
	    (ShAAppl "pred-items" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		as  = fromShATerm (getATermByIndex1 ab att)
		aa'' = (addLAnnoList as $ head aa'):(tail aa')
		ab' = pos_l
		in (Pred_items aa'' ab')
	    (ShAAppl "datatype-items" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		as  = fromShATerm (getATermByIndex1 ab att)
		aa'' = (addLAnnoList as $ head aa'):(tail aa')
		ab' = pos_l
		in (Datatype_items aa'' ab')
	    _ -> fromShATermError "SIG_ITEMS" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-SIG-ITEMS" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible SORT_ITEM where
    toATerm _ = error "*** toATerm for \"SORT_ITEM\" not implemented"
    fromATerm _ = error "*** fromATerm for \"SORT_ITEM\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"SORT_ITEM\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "sort-decl" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Sort_decl aa' ab')
	    (ShAAppl "subsort-decl" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Subsort_decl aa' ab' ac')
	    (ShAAppl "subsort-defn" [ aa,ab,ac,ad,ae ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromATermSIMPLE_ID (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		ad' = fromShATerm (getATermByIndex1 ad att)
		as  = toAnnoList ae att
		ad''= addRAnnoList as ad'
		ae' = pos_l
		in (Subsort_defn aa' ab' ac' ad'' ae')
	    (ShAAppl "iso-decl" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Iso_decl aa' ab')
	    _ -> fromShATermError "SORT_ITEM" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-SORT-ITEM" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible OP_ITEM where
    toATerm _ = error "*** toATerm for \"OP_ITEM\" not implemented"
    fromATerm _ = error "*** fromATerm for \"OP_ITEM\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"OP_ITEM\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "op-decl" [ aa,ab,ac ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		ad' = pos_l
		in (Op_decl aa' ab' ac' ad')
	    (ShAAppl "op-defn" [ aa,ab,ac,ad ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		as  = fromShATerm (getATermByIndex1 ad att)
		ac''= addRAnnoList as ac'
		ad' = pos_l
		in (Op_defn aa' ab' ac'' ad')
	    _ -> fromShATermError "OP_ITEM" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-OP-ITEM" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible OP_TYPE where
    toATerm _ = error "*** toATerm for \"OP_TYPE\" not implemented"
    fromATerm _ = error "*** fromATerm for \"OP_TYPE\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"OP_TYPE\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "total-op-type" [ aa,ab ] _)  ->
		let
		(aa',ps) = fromATermSORTS (getATermByIndex1 aa att)
		ab'      = fromShATerm (getATermByIndex1 ab att)
		ac'      = insertPos ps pos_l
		in (Total_op_type aa' ab' ac')
	    (ShAAppl "partial-op-type" [ aa,ab ] _)  ->
		let
		(aa',ps) = fromATermSORTS (getATermByIndex1 aa att)
		ab'      = fromShATerm (getATermByIndex1 ab att)
		ac'      = insertPos ps pos_l
		in (Partial_op_type aa' ab' ac')
	    _ -> fromShATermError "OP_TYPE" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-OP-TYPE" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

---- a helper for the SML-datatype SORTS -------------------------------
fromATermSORTS :: ATermTable -> ([SORT],[Pos])
fromATermSORTS att = 
	case aterm of
	    (ShAAppl "sorts" [ aa ] _)  ->
		(fromShATerm (getATermByIndex1 aa att),pos_l)		
	    _ -> fromShATermError "([SORT],[Pos])" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-SORTS" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

------------------------------------------------------------------------

instance ATermConvertible OP_HEAD where
    toATerm _ = error "*** toATerm for \"OP_HEAD\" not implemented"
    fromATerm _ = error "*** fromATerm for \"OP_HEAD\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"OP_HEAD\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "total-op-head" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Total_op_head aa' ab' ac')
	    (ShAAppl "partial-op-head" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Partial_op_head aa' ab' ac')
	    _ -> fromShATermError "OP_HEAD" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-OP-HEAD" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible ARG_DECL where
    toATerm _ = error "*** toATerm for \"ARG_DECL\" not implemented"
    fromATerm _ = error "*** fromATerm for \"ARG_DECL\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"ARG_DECL\" not implemented"
    fromShATerm att =
	case aterm of
--  (ShAAppl "arg-decl" [ ShAAppl "" [aa,ab] _ ] _)  ->
        (ShAAppl "" [aa,ab] _)  ->
		let
		aa' = fromATermVARs (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Arg_decl aa' ab' ac')
	_                       -> fromShATermError "ARG_DECL" aterm
	where

--	    Just aterm = getATermSp att' $ ShAAppl "arg-decl" [ShAAppl "" [] _] _
            aterm = case getATerm att' of
		    ShAAppl "arg-decl" [i] _ ->
			    snd $ getATermByIndex i att 
                    x         -> fromShATermError "arg-decl" x
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-ARG-DECL" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible OP_ATTR where
    toATerm _ = error "*** toATerm for \"OP_ATTR\" not implemented"
    fromATerm _ = error "*** fromATerm for \"OP_ATTR\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"OP_ATTR\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "associative" [ ] _)  ->
		let
		in Assoc_op_attr
	    (ShAAppl "commutative" [ ] _)  ->
		let
		in Comm_op_attr
	    (ShAAppl "idempotent" [ ] _)  ->
		let
		in Idem_op_attr
	    (ShAAppl "unit-op-attr" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (Unit_op_attr aa')
	    _ -> fromShATermError "OP_ATTR" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-OP-ATTR" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

instance ATermConvertible PRED_ITEM where
    toATerm _ = error "*** toATerm for \"PRED_ITEM\" not implemented"
    fromATerm _ = error "*** fromATerm for \"PRED_ITEM\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"PRED_ITEM\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "pred-decl" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Pred_decl aa' ab' ac')
	    (ShAAppl "pred-defn" [ aa,ab,ac,_ ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		ad' = pos_l
		in (Pred_defn aa' ab' ac' ad')
	    _ -> fromShATermError "PRED_ITEM" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-PRED-ITEM" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible PRED_TYPE where
    toATerm _ = error "*** toATerm for \"PRED_TYPE\" not implemented"
    fromATerm _ = error "*** fromATerm for \"PRED_TYPE\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"PRED_TYPE\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "pred-type" [ aa ] _)  ->
		let
		(aa',ps) = fromATermSORTS (getATermByIndex1 aa att)
		ab'      = insertPos ps pos_l
		in (Pred_type aa' ab')
	    _ -> fromShATermError "PRED_TYPE" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-PRED-TYPE" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible PRED_HEAD where
    toATerm _ = error "*** toATerm for \"PRED_HEAD\" not implemented"
    fromATerm _ = error "*** fromATerm for \"PRED_HEAD\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"PRED_HEAD\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "pred-head" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Pred_head aa' ab')
	    _ -> fromShATermError "PRED_HEAD" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-PRED-HEAD" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible DATATYPE_DECL where
    toATerm _ = error "*** toATerm for \"DATATYPE_DECL\" not implemented"
    fromATerm _ = error "*** fromATerm for \"DATATYPE_DECL\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"DATATYPE_DECL\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "datatype-decl" [ aa,ab,ac ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		as  = fromShATerm (getATermByIndex1 ac att)
		ab''= (addLAnnoList as $ head ab'):(tail ab')
		ac' = pos_l
		in (Datatype_decl aa' ab'' ac')
	    _ -> fromShATermError "DATATYPE_DECL" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-DATATYPE-DECL" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible ALTERNATIVE where
    toATerm _ = error "*** toATerm for \"ALTERNATIVE\" not implemented"
    fromATerm _ = error "*** fromATerm for \"ALTERNATIVE\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"ALTERNATIVE\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "total-construct" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Total_construct aa' ab' ac')
	    (ShAAppl "partial-construct" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Partial_construct aa' ab' ac')
	    (ShAAppl "subsort" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Subsorts aa' ab')
	    _ -> fromShATermError "ALTERNATIVE" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-ALTERNATIVE" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible COMPONENTS where
    toATerm _ = error "*** toATerm for \"COMPONENTS\" not implemented"
    fromATerm _ = error "*** fromATerm for \"COMPONENTS\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"COMPONENTS\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "total-select" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Total_select aa' ab' ac')
	    (ShAAppl "partial-select" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Partial_select aa' ab' ac')
	    (ShAAppl "sort-component" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (Sort aa')
	    _ -> fromShATermError "COMPONENTS" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-COMPONENTS" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible VAR_DECL where
    toATerm _ = error "*** toATerm for \"VAR_DECL\" not implemented"
    fromATerm _ = error "*** fromATerm for \"VAR_DECL\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"VAR_DECL\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "" [ aa,ab ] _)  ->
		let
		aa' = fromATermVARs (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		in (Var_decl aa' ab' [])
	    _ -> fromShATermError "VAR_DECL" aterm
	where
	    aterm = getATerm att

instance ATermConvertible FORMULA where
    toATerm _ = error "*** toATerm for \"FORMULA\" not implemented"
    fromATerm _ = error "*** fromATerm for \"FORMULA\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"FORMULA\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "quantification" [ aa,ab,ac ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		pq  = getPos (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		ad' = insertPos pq pos_l
		in (Quantification aa' ab' ac' ad')
	    (ShAAppl "conjunction" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Conjunction aa' ab')
	    (ShAAppl "disjunction" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Disjunction aa' ab')
	    (ShAAppl "implication" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Implication aa' ab' ac')
	    (ShAAppl "equivalence" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Equivalence aa' ab' ac')
	    (ShAAppl "negation" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Negation aa' ab')
            -- the following things are from SML-type ATOM 
            (ShAAppl "atom" [i] _) -> 
              case snd (getATermByIndex i att') of 
	       (ShAAppl "ttrue" [] _) ->
		 let
		 aa' = pos_l
		 in (True_atom aa')
	       (ShAAppl "ffalse" [] _) ->
		 let
		 aa' = pos_l
		 in (False_atom aa')
	       (ShAAppl "predication" [ aa,ab ] _) ->
		 let
		 aa'      = fromShATerm (getATermByIndex1 aa att)
		 (ab',ps) = fromATermTERMS (getATermByIndex1 ab att)
		 ac'      = insertPos ps pos_l
		 in (Predication aa' ab' ac')
	       (ShAAppl "definedness" [ aa ] _) ->
		 let
		 aa' = fromShATerm (getATermByIndex1 aa att)
		 ab' = pos_l
		 in (Definedness aa' ab')
	       (ShAAppl "existl-equation" [ aa,ab ] _) ->
		 let
		 aa' = fromShATerm (getATermByIndex1 aa att)
		 ab' = fromShATerm (getATermByIndex1 ab att)
		 ac' = pos_l
		 in (Existl_equation aa' ab' ac')
	       (ShAAppl "strong-equation" [ aa,ab ] _) ->
		 let
		 aa' = fromShATerm (getATermByIndex1 aa att)
		 ab' = fromShATerm (getATermByIndex1 ab att)
		 ac' = pos_l
		 in (Strong_equation aa' ab' ac')
	       (ShAAppl "membership" [ aa,ab ] _) ->
		 let
		 aa' = fromShATerm (getATermByIndex1 aa att)
		 ab' = fromShATerm (getATermByIndex1 ab att)
		 ac' = pos_l
		 in (Membership aa' ab' ac')
               _ -> fromShATermError "FORMULA" aterm
	    _ -> fromShATermError "FORMULA" aterm
	where
	    aterm = getATerm att'
	    (pos_l,_g_flag,att') = skipPosFlag "pos-FORMULA" att

---- a helper for the SML-datatype TERMS -------------------------------
fromATermTERMS :: ATermTable -> ([TERM],[Pos])
fromATermTERMS att = 
    case aterm of
	     (ShAAppl "terms" [ aa ] _)  ->
		 (fromShATerm (getATermByIndex1 aa att),pos_l)		
	     _ -> fromShATermError "([TERM],[Pos])" aterm
    where aterm = getATerm att'
	  (pos_l,att') =
	      case getATerm att of
	      (ShAAppl "pos-TERMS" [reg_i,item_i] _) ->
		       (posFromRegion reg_i att,getATermByIndex1 item_i att)
	      _  -> ([],att)

---- a helper for SIMPLE_IDs --------------------------------------------

fromATermSIMPLE_ID :: ATermTable -> SIMPLE_ID
fromATermSIMPLE_ID att = 
    case aterm of
      (ShAAppl "" [ si, _ ] _) -> -- snd element is 'None' 
                                  -- (CASL.grm:((WORDS,None)))
          let s = fromShATerm $ getATermByIndex1 si att
	  in Token s nullPos
      _ -> fromShATermError "SIMPLE_ID" aterm
    where aterm = getATerm att

---- a helper for [VAR] -------------------------------------------------
fromATermVARs :: ATermTable -> [VAR]
fromATermVARs att = map fromATermSIMPLE_ID att_list
    where att_list = case getATerm att of
		     ShAList l _-> map getAtt l
		     _          -> fromShATermError "[VAR]" $ getATerm att
	  getAtt ai = getATermByIndex1 ai att

-------------------------------------------------------------------------

instance ATermConvertible QUANTIFIER where
    toATerm _ = error "*** toATerm for \"QUANTIFIER\" not implemented"
    fromATerm _ = error "*** fromATerm for \"QUANTIFIER\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"QUANTIFIER\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "forall" [ ] _)  ->
		let
		in Universal
	    (ShAAppl "exists" [ ] _)  ->
		let
		in Existential
	    (ShAAppl "exists-uniquely" [ ] _)  ->
		let
		in Unique_existential
	    _ -> fromShATermError "QUANTIFIER" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-QUANTIFIER" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

instance ATermConvertible PRED_SYMB where
    toATerm _ = error "*** toATerm for \"PRED_SYMB\" not implemented"
    fromATerm _ = error "*** fromATerm for \"PRED_SYMB\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"PRED_SYMB\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "pred-symb" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in case getATerm $ getATermByIndex1 ab att of
		   ShAAppl "None" [] _ -> 
		       (Pred_name aa')
		   ShAAppl "Some" [ aab ] _ -> 
		     let aab' = fromShATerm (getATermByIndex1 aab att)
			 ac' = pos_l
		     in (Qual_pred_name aa' aab' ac')
		   _ -> fromShATermError "Option" aterm
	    _ -> fromShATermError "PRED_SYMB" aterm
	where
	    aterm = getATerm att' 
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-PRED-SYMB" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible TERM where
    toATerm _ = error "*** toATerm for \"TERM\" not implemented"
    fromATerm _ = error "*** fromATerm for \"TERM\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"TERM\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "var-or-const" [ aa ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		in (Simple_id aa')
	    (ShAAppl "qual-var" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Qual_var aa' ab' ac')
	    (ShAAppl "application" [ aa,ab ] _)  ->
		let
		aa'      = fromShATerm (getATermByIndex1 aa att)
		(ab',ps) = fromATermTERMS (getATermByIndex1 ab att)
		ac'      = insertPos ps pos_l
		in (Application aa' ab' ac')
	    (ShAAppl "sorted-term" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Sorted_term aa' ab' ac')
	    (ShAAppl "cast" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Cast aa' ab' ac')
	    (ShAAppl "conditional" [ aa,ab,ac ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		ad' = pos_l
		in (Conditional aa' ab' ac' ad')
	    _ -> fromShATermError "TERM" aterm
	where
	    aterm = getATerm att'
	    (pos_l,_p_flag,att') = skipPosFlag "pos-TERM" att

instance ATermConvertible OP_SYMB where
    toATerm _ = error "*** toATerm for \"OP_SYMB\" not implemented"
    fromATerm _ = error "*** fromATerm for \"OP_SYMB\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"OP_SYMB\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "op-symb" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in case getATerm $ getATermByIndex1 ab att of
		   ShAAppl "None" [] _ -> 
		       (Op_name aa')
		   ShAAppl "Some" [ aab ] _ -> 
		     let aab' = fromShATerm (getATermByIndex1 aab att)
			 ac' = pos_l
		     in (Qual_op_name aa' aab' ac')
		   _ -> fromShATermError "Option" aterm
	    _ -> fromShATermError "OP_SYMB" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-OP-SYMB" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible SYMB_ITEMS where
    toATerm _ = error "*** toATerm for \"SYMB_ITEMS\" not implemented"
    fromATerm _ = error "*** fromATerm for \"SYMB_ITEMS\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"SYMB_ITEMS\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "symb-items" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Symb_items aa' ab' ac')
	    _ -> fromShATermError "SYMB_ITEMS" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-SYMB-ITEMS" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible SYMB_MAP_ITEMS where
    toATerm _ = error "*** toATerm for \"SYMB_MAP_ITEMS\" not implemented"
    fromATerm _ = error "*** fromATerm for \"SYMB_MAP_ITEMS\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"SYMB_MAP_ITEMS\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "symb-map-items" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Symb_map_items aa' ab' ac')
	    _ -> fromShATermError "SYMB_MAP_ITEMS" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-SYMB-MAP-ITEMS" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible SYMB_KIND where
    toATerm _ = error "*** toATerm for \"SYMB_KIND\" not implemented"
    fromATerm _ = error "*** fromATerm for \"SYMB_KIND\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"SYMB_KIND\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "implicitk" [ ] _)  ->
		Implicit
	    (ShAAppl "sortsk" [ ] _)  ->
		Sorts_kind
	    (ShAAppl "opsk" [ ] _)  ->
		Ops_kind
	    (ShAAppl "predsk" [ ] _)  ->
		Preds_kind
	    _ -> fromShATermError "SYMB_KIND" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-SYMB-KIND" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

instance ATermConvertible SYMB where
    toATerm _ = error "*** toATerm for \"SYMB\" not implemented"
    fromATerm _ = error "*** fromATerm for \"SYMB\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"SYMB\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "symb-id" [ aa ] _)  ->
		let
		i  = fromShATerm (getATermByIndex1 aa att)
		aa' = setFstPos pos_l i
		in (Symb_id aa')
	    (ShAAppl "qual-id" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Qual_id aa' ab' ac')
	    _ -> fromShATermError "SYMB" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-SYMB" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible TYPE where
    toATerm _ = error "*** toATerm for \"TYPE\" not implemented"
    fromATerm _ = error "*** fromATerm for \"TYPE\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"TYPE\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "op-symb-type" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (O_type aa')
	    (ShAAppl "pred-symb-type" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (P_type aa')
	    _ -> fromShATermError "TYPE" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-TYPE" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

instance ATermConvertible SYMB_OR_MAP where
    toATerm _ = error "*** toATerm for \"SYMB_OR_MAP\" not implemented"
    fromATerm _ = error "*** fromATerm for \"SYMB_OR_MAP\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"SYMB_OR_MAP\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "symb" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (Symb aa')
	    (ShAAppl "symb-or-map" [ aa ] _)  ->
		let
		(aa',ab') = fromATermSYMB_MAP (getATermByIndex1 aa att)
		ac' = pos_l
		in (Symb_map aa' ab' ac')
	    _ -> fromShATermError "SYMB_OR_MAP" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-SYMB-OR-MAP" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

---- a helper for SYMB_MAP from SML -------------------------------------

fromATermSYMB_MAP :: ATermTable -> (SYMB,SYMB)
fromATermSYMB_MAP att =
	case aterm of
	    (ShAAppl "symb-map" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		in (aa',ab')
	    _ -> fromShATermError "(SYMB,SYMB)" aterm
	where
	    aterm = getATerm att' 
	    att' =
		case getATerm att of
		(ShAAppl "pos-SYMB-MAP" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

-------------------------------------------------------------------------

----- instances of AS_Structured.hs -------------------------------------
instance ATermConvertible SPEC where
    toATerm _ = error "*** toATerm for \"SPEC\" not implemented"
    fromATerm _ = error "*** fromATerm for \"SPEC\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"SPEC\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "basic" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		aa'' = G_basic_spec CASL aa'
		in group (Syntax.AS_Structured.Basic_spec aa'') group_flag
	    (ShAAppl "translation" [ aa,ab,_ ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		in group (Translation aa' ab') group_flag
	    (ShAAppl "reduction" [ aa,ab,_ ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		in group (Reduction aa' ab') group_flag
	    (ShAAppl "union-spec" [ aa ] _)  ->
		let
		aa' :: [(Annoted SPEC,[Annotation])]
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in group (Union (toAnnotedList aa') ab') group_flag
	    (ShAAppl "extension" [ aa ] _)  ->
		let
		aa' :: [(Annoted SPEC,[Annotation])]
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in group (Extension (toAnnotedList aa') ab') group_flag
	    (ShAAppl "free-spec" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		aa''= addLAnnoList (toAnnoList ab att) aa'
		ab' = pos_l
		in group (Free_spec aa'' ab') group_flag
	    (ShAAppl "local-spec" [ aa,ab,ac,ad ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		sp1 = addLAnnoList (toAnnoList ab att) aa'
		ac' = fromShATerm (getATermByIndex1 ac att)
		sp2 = addLAnnoList (toAnnoList ad att) ac'
		in group (Local_spec sp1 sp2 pos_l) group_flag
	    (ShAAppl "closed-spec" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		aa''= addLAnnoList (toAnnoList ab att) aa'
		ab' = pos_l
		in group (Closed_spec aa'' ab') group_flag
	    (ShAAppl "spec-inst" [ aa,ab ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		in (Spec_inst aa' ab' [nullPos])
	    _ -> fromShATermError "SPEC" aterm
	where
	    aterm = getATerm att'
	    group s gf = if gf then (Group s' pos_l) else s
		where s' = Annoted s [] [] []
	    (pos_l,group_flag,att') = skipPosFlag "pos-SPEC" att

--- a helper function for [(Annoted a, [Annotation])] --------------------

toAnnotedList :: forall a . [(Annoted a,[Annotation])] -> [Annoted a]
toAnnotedList xs = map merge xs
    where merge (ai,as) = ai { l_annos = (l_annos ai) ++ as}

--------------------------------------------------------------------------

instance ATermConvertible RENAMING where
    toATerm _ = error "*** toATerm for \"RENAMING\" not implemented"
    fromATerm _ = error "*** fromATerm for \"RENAMING\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"RENAMING\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "renaming" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		aa''= if null aa' then [] 
		      else [G_symb_map $ G_symb_map_items_list CASL aa']
		ab' = pos_l
		in (Renaming aa'' ab')
	    _ -> fromShATermError "RENAMING" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-RENAMING" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible RESTRICTION where
    toATerm _ = error "*** toATerm for \"RESTRICTION\" not implemented"
    fromATerm _ = error "*** fromATerm for \"RESTRICTION\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"RESTRICTION\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "hide" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		aa''= if null aa' then [] 
		      else [G_symb_list $ G_symb_items_list CASL aa']
		ab' = pos_l
		in (Hidden aa'' ab')
	    (ShAAppl "reveal" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		aa''= G_symb_map_items_list CASL aa'
		ab' = pos_l
		in (Revealed aa'' ab')
	    _ -> fromShATermError "RESTRICTION" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-RESTRICTION" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
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
    fromShATerm att =
	case aterm of
	    (ShAAppl "spec-defn" [ aa,ab,ac,ad ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		ad' = pos_l
		in (Spec_defn aa' ab' ac' ad')
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-SPEC-DEFN" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)
-}

instance ATermConvertible GENERICITY where
    toATerm _ = error "*** toATerm for \"GENERICITY\" not implemented"
    fromATerm _ = error "*** fromATerm for \"GENERICITY\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"GENERICITY\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "genericity" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Genericity aa' ab' ac')
	    _ -> fromShATermError "GENERICITY" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-GENERICITY" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible PARAMS where
    toATerm _ = error "*** toATerm for \"PARAMS\" not implemented"
    fromATerm _ = error "*** fromATerm for \"PARAMS\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"PARAMS\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "params" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (Params aa')
	    _ -> fromShATermError "PARAMS" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-PARAMS" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

instance ATermConvertible IMPORTED where
    toATerm _ = error "*** toATerm for \"IMPORTED\" not implemented"
    fromATerm _ = error "*** fromATerm for \"IMPORTED\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"IMPORTED\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "imports" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (Imported aa')
	    _ -> fromShATermError "IMPORTED" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-IMPORTS" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

instance ATermConvertible FIT_ARG where
    toATerm _ = error "*** toATerm for \"FIT_ARG\" not implemented"
    fromATerm _ = error "*** fromATerm for \"FIT_ARG\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"FIT_ARG\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "fit-spec" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ab''= G_symb_map_items_list CASL ab'
		ac' = pos_l
		in (Fit_spec aa' ab'' ac')
	    (ShAAppl "fit-view" [ aa,ab ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Fit_view aa' ab' ac' [])
	    _ -> fromShATermError "FIT_ARG" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-FIT-ARG" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
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
    fromShATerm att =
	case aterm of
	    (ShAAppl "view-defn" [ aa,ab,ac,ad,ae ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		ad' = fromShATerm (getATermByIndex1 ad att)
		ae' = pos_l
		in (View_defn aa' ab' ac' ad' ae')
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-VIEW-DEFN" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)
-}

instance ATermConvertible VIEW_TYPE where
    toATerm _ = error "*** toATerm for \"VIEW_TYPE\" not implemented"
    fromATerm _ = error "*** fromATerm for \"VIEW_TYPE\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"VIEW_TYPE\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "view-type" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (View_type aa' ab' ac')
	    _ -> fromShATermError "VIEW_TYPE" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-VIEW-TYPE" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
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
	in addATermSp (ShAAppl "arch-spec-defn" lat _)  att3
    fromShATerm att =
	case aterm of
	    (ShAAppl "arch-spec-defn" [ aa,ab,ac ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Arch_spec_defn aa' ab' ac')
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-ARCH-SPEC-DEFN" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

-}

instance ATermConvertible ARCH_SPEC where
    toATerm _ = error "*** toATerm for \"ARCH_SPEC\" not implemented"
    fromATerm _ = error "*** fromATerm for \"ARCH_SPEC\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"ARCH_SPEC\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "basic-arch-spec" [ aa,ab,ac ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromATermRESULT_UNIT (getATermByIndex1 ab att)
		as  = toAnnoList ac att
		aa''= (addLAnnoList as $ head aa'):tail aa'
		ac' = pos_l
		in (Basic_arch_spec aa'' ab' ac')
	    (ShAAppl "named-arch-spec" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (Arch_spec_name aa')
	    _ -> fromShATermError "ARCH_SPEC" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-ARCH-SPEC" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

--------------------------------------------------------------------------
fromATermRESULT_UNIT :: ATermTable -> (Annoted UNIT_EXPRESSION)
fromATermRESULT_UNIT att = 
	case aterm of
	    (ShAAppl "result-unit" [ aa,ab ] _)  ->
		let
--		aa' :: UNIT_EXPRESSION
		aa' = fromShATerm (getATermByIndex1 aa att)
		as  = toAnnoList ab att
		in (Annoted aa' [] as [])
	    _ -> fromShATermError "RESULT-UNIT" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-RESULT-UNIT" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

--------------------------------------------------------------------------


instance ATermConvertible UNIT_DECL_DEFN where
    toATerm _ = error "*** toATerm for \"UNIT_DECL_DEFN\" not implemented"
    fromATerm _ = error "*** fromATerm for \"UNIT_DECL_DEFN\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"UNIT_DECL_DEFN\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "unit-decl-case" [ udl ] _)  ->
		let att1 = getATermByIndex1 udl att
		    (ps,att2) = case getATerm att1 of
				  (ShAAppl "pos-UNIT-DECL" [reg_i,item_i] _) ->
				      (posFromRegion reg_i att,
				       getATermByIndex1 item_i att1)
				  _  -> ([],att1)
		    aterm2 = getATerm att2
		in case aterm2 of
		   ShAAppl "unit-decl" [aa,ab,ac] _ -> 
		      let aa'  = fromATermSIMPLE_ID (getATermByIndex1 aa att)
			  ab'  = fromShATerm (getATermByIndex1 ab att)
			  ac'  = fromATermUNIT_IMPORTS $ 
			                 getATermByIndex1 ac att
			  ad'  = ps
		      in (Unit_decl aa' ab' ac' ad')
		   _ -> fromShATermError "UNIT_DECL" aterm2
	    (ShAAppl "unit-defn-case" [ udn ] _)  ->
		fromATermUNIT_DEFN $ getATermByIndex1 udn att
	    (ShAAppl "pos-UNIT-DEFN" _ _) ->
		fromATermUNIT_DEFN att
	    (ShAAppl "unit-defn" _ _) ->
		fromATermUNIT_DEFN att
	    _ -> fromShATermError "UNIT-DECL-DEFN" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-UNIT-DECL-DEFN" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

---- a helper for the SML-datatype UNIT_IMPORTS ------------------------

fromATermUNIT_IMPORTS :: ATermTable -> [Annoted UNIT_TERM]
fromATermUNIT_IMPORTS att = 
    case aterm of
	     (ShAAppl "unit-imports" [ aa ] _)  ->
		 fromShATerm $ getATermByIndex1 aa att
	     _ -> fromShATermError "UNIT_IMPORTS" aterm
    where aterm = getATerm att'
	  att' =
	      case getATerm att of
	      (ShAAppl "pos-UNIT-IMPORTS" [_,item_i] _) ->
		  getATermByIndex1 item_i att
	      _  -> att

-------------------------------------------------------------------------
fromATermUNIT_DEFN :: ATermTable -> UNIT_DECL_DEFN
fromATermUNIT_DEFN att =
    case aterm of
    ShAAppl "unit-defn" [aa,ab] _ -> 
	let aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
	    ab' = fromShATerm (getATermByIndex1 ab att)
	    ac' = ps
        in (Unit_defn aa' ab' ac')
    _ -> fromShATermError "UNIT_DEFN" aterm
    where aterm = getATerm att'
	  (ps,att') =
	      case getATerm att of
	      (ShAAppl "pos-UNIT-DEFN" [reg_i,item_i] _) ->
		  (posFromRegion reg_i att,getATermByIndex1 item_i att)
	      _  -> ([],att)
-------------------------------------------------------------------------

{- !!! This conversion is covered by the instance of LIB_ITEM !!!

instance ATermConvertible UNIT_SPEC_DEFN where
    toATerm att0 (Unit_spec_defn aa ab ac) =
	let (att1,aa') = toATerm att0 aa
	    (att2,ab') = toATerm att1 ab
	    (att3,ac') = toATerm att2 ac
	    lat = [ aa',ab',ac' ]
	in addATermSp (ShAAppl "unit-spec-defn" lat _)  att3
    fromShATerm att =
	case aterm of
	    (ShAAppl "unit-spec-defn" [ aa,ab,ac ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Unit_spec_defn aa' ab' ac')
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-UNIT-SPEC-DEFN" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)
-}

instance ATermConvertible UNIT_SPEC where
    toATerm _ = error "*** toATerm for \"UNIT_SPEC\" not implemented"
    fromATerm _ = error "*** fromATerm for \"UNIT_SPEC\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"UNIT_SPEC\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "unit-type-case" [ aa ] _)  ->
		let
		(aa',ab') = fromATermUNIT_TYPE $ getATermByIndex1 aa att
		ac' = pos_l
		in (Unit_type aa' ab' ac')
	    (ShAAppl "spec-name-case" [ aa ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		in (Spec_name aa')
	    (ShAAppl "arch-spec-case" [ aa,ab ] _)  ->
		let
		aa'   = fromShATerm (getATermByIndex1 aa att)
		ps    = toAnnoList ab att
		aa''  = addLAnnoList ps aa'
		ab'   = pos_l
		aa''' = case aa'' of
		        (Annoted (Basic_arch_spec _ _ _) _ _ _) ->
			    Annoted (Group_arch_spec aa'' ab') [] [][] 
			_ -> aa''
		in (Arch_unit_spec aa''' ab')
	    (ShAAppl "closed" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Closed_unit_spec aa' ab')
	    _ -> fromShATermError "UNIT_SPEC" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-UNIT-SPEC" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

---- a helper for the SML-datatype UNIT_TYPE ----------------------------

fromATermUNIT_TYPE :: ATermTable -> ([Annoted SPEC],(Annoted SPEC))
fromATermUNIT_TYPE att = 
    case aterm of
	     (ShAAppl "unit-type" [ aa,ab ] _)  ->
		 (fromShATerm $ getATermByIndex1 aa att,
		  fromShATerm $ getATermByIndex1 ab att)
	     _ -> fromShATermError "UNIT_TYPE" aterm
    where aterm = getATerm att'
	  att' =
	      case getATerm att of
	      (ShAAppl "pos-UNIT-TYPE" [_,item_i] _) ->
		  getATermByIndex1 item_i att
	      _  -> att

-------------------------------------------------------------------------

instance ATermConvertible UNIT_EXPRESSION where
    toATerm _ = error "*** toATerm for \"UNIT_EXPRESSION\" not implemented"
    fromATerm _ = error "*** fromATerm for \"UNIT_EXPRESSION\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"UNIT_EXPRESSION\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "unit-expression" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Unit_expression aa' ab' ac')
	    _ -> fromShATermError "UNIT_EXPRESSION" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-UNIT-EXPRESSION" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible UNIT_BINDING where
    toATerm _ = error "*** toATerm for \"UNIT_BINDING\" not implemented"
    fromATerm _ = error "*** fromATerm for \"UNIT_BINDING\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"UNIT_BINDING\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "unit-binding" [ aa,ab ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Unit_binding aa' ab' ac')
	    _ -> fromShATermError "UNIT_BINDING" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-UNIT-BINDING" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible UNIT_TERM where
    toATerm _ = error "*** toATerm for \"UNIT_TERM\" not implemented"
    fromATerm _ = error "*** fromATerm for \"UNIT_TERM\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"UNIT_TERM\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "unit-reduction" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		in group (Unit_reduction aa' ab') group_flag
	    (ShAAppl "unit-translation" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		in group (Unit_translation aa' ab') group_flag
	    (ShAAppl "amalgamation" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in group (Amalgamation aa' ab') group_flag
	    (ShAAppl "local-unit" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in group (Local_unit aa' ab' ac') group_flag
	    (ShAAppl "unit-appl" [ aa,ab ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in group (Unit_appl aa' ab' ac') group_flag
	    _ -> fromShATermError "UNIT_TERM" aterm
	where
	    aterm = getATerm att'
	    group ut gf = if gf then (Group_unit_term ut' pos_l) else ut
		where ut' = Annoted ut [] [] []
	    (pos_l,group_flag,att') = skipPosFlag "pos-UNIT-TERM" att

instance ATermConvertible FIT_ARG_UNIT where
    toATerm _ = error "*** toATerm for \"FIT_ARG_UNIT\" not implemented"
    fromATerm _ = error "*** fromATerm for \"FIT_ARG_UNIT\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"FIT_ARG_UNIT\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "fit-arg-unit" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ab''= G_symb_map_items_list CASL ab'
		ac' = pos_l
		in (Fit_arg_unit aa' ab'' ac')
	    _ -> fromShATermError "FIT_ARG_UNIT" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-FIT-ARG-UNIT" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)
-------------------------------------------------------------------------

----- instances of AS_LIbrary.hs ----------------------------------------
instance ATermConvertible LIB_DEFN where
    toATerm _ = error "*** toATerm for \"LIB_DEFN\" not implemented"
    fromATerm _ = error "*** fromATerm for \"LIB_DEFN\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"LIB_DEFN\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "lib-defn" [ aa,ab,ad ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		ad' = fromShATerm (getATermByIndex1 ad att)
		in (Lib_defn aa' ab' ac' ad')
	    _ -> fromShATermError "LIB_DEFN" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-LIB-DEFN" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible LIB_ITEM where
    toATerm _ = error "*** toATerm for \"LIB_ITEM\" not implemented"
    fromATerm _ = error "*** fromATerm for \"LIB_ITEM\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"LIB_ITEM\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "spec-defn" [ aa,ab,ac,ad ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		as  = toAnnoList ad att
		ac''= addLAnnoList as ac'
		ad' = pos_l
		in Syntax.AS_Library.Spec_defn aa' ab' ac'' ad'
	    (ShAAppl "view-defn" [ aa,ab,ac,ad,_ ] _)  ->
		let  -- the annotation list is lost !!!!
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = fromShATerm (getATermByIndex1 ac att)
		ad' = fromShATerm (getATermByIndex1 ad att)
		ad''= if null ad' then [] 
		      else [G_symb_map $ G_symb_map_items_list CASL ad']
{-		as  = toAnnoList ae att
		ac''= addLAnnoList as ac'-}
		ae' = pos_l
		in (Syntax.AS_Library.View_defn aa' ab' ac' ad'' ae')
	    (ShAAppl "arch-spec-defn" [ aa,ab,_ ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Syntax.AS_Library.Arch_spec_defn aa' ab' ac')
	    (ShAAppl "unit-spec-defn" [ aa,ab,_ ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Syntax.AS_Library.Unit_spec_defn aa' ab' ac')
	    (ShAAppl "download-items" [ aa,ab,_ ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		ac' = pos_l
		in (Syntax.AS_Library.Download_items aa' ab' ac')
	    _ -> fromShATermError "LIB_ITEM" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') = skipPos "pos-LIB-ITEM" att

---- helpers to skip nested "pos-"-constructors -----------------------
skipPos :: String -> ATermTable -> ([Pos],ATermTable)
skipPos mcon at   = 
     case getATerm at of
	      ShAAppl con [reg_i,item_i] _ | mcon == con ->
		  if pCon then skipPos mcon at'
		  else (posFromRegion (reg_i) at, at')
		      where pCon = case getATerm at' of
				   ShAAppl con' _ _ | mcon == con' -> True
				   _                               -> False
			    at'  = getATermByIndex1 item_i at
	      _  -> ([],at)

skipPosFlag :: String -> ATermTable -> ([Pos],Bool,ATermTable)
skipPosFlag mcon att   = 		
    case getATerm att of
    ShAAppl con [reg_i,b_i,item_i] _ | mcon == con ->
          if pCon then let (_r_pos_l,r_b,r_at') = skipPosFlag mcon at'
		       in (pos_l,r_b || b,r_at')
	  else (pos_l,b,at')
	      where pCon  = case getATerm at' of
			    ShAAppl con' _ _ | mcon == con' -> True
			    _                           -> False
		    at'   = getATermByIndex1 item_i att
		    pos_l = posFromRegion reg_i att
		    b     = fromShATerm $ getATermByIndex1 b_i att
    _  -> ([],False,att)

-----------------------------------------------------------------------

instance ATermConvertible ITEM_NAME_OR_MAP where
    toATerm _ = error "*** toATerm for \"ITEM_NAME_OR_MAP\" not implemented"
    fromATerm _ = error "*** fromATerm for \"ITEM_NAME_OR_MAP\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"ITEM_NAME_OR_MAP\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "item-name" [ aa ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		in (Item_name aa')
	    (ShAAppl "item-name-map" [ aa,ab ] _)  ->
		let
		aa' = fromATermSIMPLE_ID (getATermByIndex1 aa att)
		ab' = fromATermSIMPLE_ID (getATermByIndex1 ab att)
		ac' = pos_l
		in (Item_name_map aa' ab' ac')
	    _ -> fromShATermError "ITEM_NAME_OR_MAP" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-ITEM-NAME-OR-MAP" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible LIB_NAME where
    toATerm _ = error "*** toATerm for \"LIB_NAME\" not implemented"
    fromATerm _ = error "*** fromATerm for \"LIB_NAME\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"LIB_NAME\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "versioned-lib" [ aa,ab ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = fromShATerm (getATermByIndex1 ab att)
		in (Lib_version aa' ab')
	    (ShAAppl "lib" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		in (Lib_id aa')
	    _ -> fromShATermError "LIB_NAME" aterm
	where
	    aterm = getATerm att'
	    att' =
		case getATerm att of
		(ShAAppl "pos-LIB-NAME" [_,item_i] _) ->
		    getATermByIndex1 item_i att
		_  -> att

instance ATermConvertible LIB_ID where
    toATerm _ = error "*** toATerm for \"LIB_ID\" not implemented"
    fromATerm _ = error "*** fromATerm for \"LIB_ID\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"LIB_ID\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "url" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Direct_link aa' ab')
	    (ShAAppl "path-name" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Indirect_link aa' ab')
	    _ -> fromShATermError "LIB_NAME" aterm
	where
	    aterm = getATerm att'
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-LIB-ID" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)

instance ATermConvertible VERSION_NUMBER where
    toATerm _ = error "*** toATerm for \"VERSION_NUMBER\" not implemented"
    fromATerm _ = error "*** fromATerm for \"VERSION_NUMBER\" not implemented"
    toShATerm _ _ = error "*** toShATerm for \"VERSION_NUMBER\" not implemented"
    fromShATerm att =
	case aterm of
	    (ShAAppl "version" [ aa ] _)  ->
		let
		aa' = fromShATerm (getATermByIndex1 aa att)
		ab' = pos_l
		in (Version_number aa' ab')
	    _ -> fromShATermError "VERSION_NUMBER" aterm
	where
	    aterm = getATerm att' 
	    (pos_l,att') =
		case getATerm att of
		(ShAAppl "pos-VERSION" [reg_i,item_i] _) ->
		    (posFromRegion reg_i att,getATermByIndex1 item_i att)
		_  -> ([],att)
-------------------------------------------------------------------------

-- some helpers for Annoted things --------------------------------------
addLAnnoList :: forall a . [Annotation] -> Annoted a -> Annoted a
addLAnnoList as ani = ani {l_annos = as ++ (l_annos ani) }

addRAnnoList :: forall a . [Annotation] -> Annoted a -> Annoted a
addRAnnoList as ani = ani {r_annos = (r_annos ani) ++ as } 

--- some helpers for Regions and Positions ------------------------------

posFromRegion :: Int -> ATermTable -> [Pos]
posFromRegion reg at = map ( \ (l, c) -> newPos "" l c ) 
		       $ fromATerm_reg reg at 

getPos :: ATermTable -> [Pos]
getPos att = case getATerm att of
		ShAAppl _ (x:_) _ -> posFromRegion x att
		_       -> []

-- converts an aterm region information to [Pos]
fromATerm_reg :: Int -> ATermTable -> [(Int,Int)]
fromATerm_reg reg_i at = [fst r,snd r] 
    where r :: ((Int,Int),(Int,Int)) -- Id.hs Region
	  r = fromShATerm r_at
	  r_at = getATermByIndex1 reg_i at

insertIM, insertPos :: [a] -> [a] -> [a]
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
