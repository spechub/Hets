{- |
Module      :  $Header$
Copyright   :  (c) Felix Reckers and Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

-}

module ATC.Grothendieck where

import Logic.Grothendieck
import Common.ATerm.Lib
import Common.Result
import Comorphisms.LogicGraph
import Logic.Logic
import qualified Common.Lib.Set as Set

instance ShATermConvertible G_basic_spec where
     toShATerm att0 (G_basic_spec lid basic_spec) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 basic_spec of { (att2,i2) ->
           addATerm (ShAAppl "G_basic_spec" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_basic_spec" [i1,i2] _) ->
		case fromShATerm (getATermByIndex1 i1 att) of { i1' ->
                case (getATermByIndex1 i2 att) of { att' ->
                case lookupLogic_in_LG 
		      ("ShATermConvertible G_basic_spec:") i1'  of {
		    Logic lid -> 
			G_basic_spec lid (fromShATerm att')}}} 
	    u     -> fromShATermError "G_basic_spec" u
         where
         aterm = getATerm att

instance ShATermConvertible G_sign where
     toShATerm att0 (G_sign lid sign) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 sign of { (att2,i2) ->
           addATerm (ShAAppl "G_sign" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_sign" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ShATermConvertible G_sign:") i1' 
                in case l of
                    Logic lid -> (G_sign lid (fromShATerm att'))
	    u     -> fromShATermError "G_sign" u
         where
         aterm = getATerm att

instance ShATermConvertible G_ext_sign where
     toShATerm att0 (G_ext_sign lid sign _) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 sign of { (att2,i2) ->
           addATerm (ShAAppl "G_ext_sign" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_ext_sign" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ShATermConvertible G_ext_sign:") i1' 
                in case l of
                    Logic lid -> (G_ext_sign lid (fromShATerm att') Set.empty)
	    u     -> fromShATermError "G_ext_sign" u
         where
         aterm = getATerm att

instance ShATermConvertible G_sign_list where
     toShATerm att0 (G_sign_list lid signs) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 signs of { (att2,i2) ->
           addATerm (ShAAppl "G_sign_list" [i1,i2] []) att2}}
     fromShATerm att =
         case aterm of
	    (ShAAppl "G_sign_list" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ShATermConvertible G_sign_list:") i1' 
                in case l of
                    Logic lid -> (G_sign_list lid (fromShATerm att'))
	    u     -> fromShATermError "G_sign" u
         where
         aterm = getATerm att

instance ShATermConvertible G_symbol where
     toShATerm att0 (G_symbol lid symbol) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 symbol of { (att2,i2) ->
           addATerm (ShAAppl "G_symbol" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_symbol" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ShATermConvertible G_symbol:") i1' 
                in case l of 
                    Logic lid -> (G_symbol lid (fromShATerm att'))
	    u     -> fromShATermError "G_symbol" u
         where
         aterm = getATerm att 

instance ShATermConvertible G_symb_items_list where
     toShATerm att0 (G_symb_items_list lid symb_items) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 symb_items of { (att2,i2) ->
           addATerm (ShAAppl "G_symb_items_list" [i1,i2] []) att2 }}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_symb_items_list" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ShATermConvertible G_symb_items_list:") i1' 
                in case l of
                    Logic lid -> (G_symb_items_list lid (fromShATerm att'))
	    u     -> fromShATermError "G_symb_items_list" u
         where
         aterm = getATerm att

instance ShATermConvertible G_symb_map_items_list where
     toShATerm att0 (G_symb_map_items_list lid symb_map_items) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 symb_map_items of { (att2,i2) ->
           addATerm (ShAAppl "G_symb_map_items_list" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_symb_map_items_list" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ShATermConvertible G_symb_map_items_list:") i1' 
                in case l of
                    Logic lid -> (G_symb_map_items_list lid (fromShATerm att'))
	    u     -> fromShATermError "G_symb_map_items_list" u
         where
         aterm = getATerm att

instance ShATermConvertible G_diagram where
     toShATerm att0 (G_diagram lid diagram) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 diagram of { (att2,i2) ->
           addATerm (ShAAppl "G_diagram" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_diagram" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ShATermConvertible G_diagram:") i1' 
                in case l of
                    Logic lid -> (G_diagram lid (fromShATerm att'))
	    u     -> fromShATermError "G_diagram" u
         where
         aterm = getATerm att

instance ShATermConvertible G_sublogics where
     toShATerm att0 (G_sublogics lid sublogics) = 
	 case toShATerm att0 (language_name lid)  of { (att1,i1) ->
         case toShATerm att1 sublogics of { (att2,i2) ->
           addATerm (ShAAppl "G_sublogics" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_sublogics" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG 
                          ("ShATermConvertible G_sublogics:") i1' 
                in case l of 
                    Logic lid -> 
                     (G_sublogics lid (fromShATerm att'))
	    u     -> fromShATermError "G_sublogics" u
         where
         aterm = getATerm att 

instance ShATermConvertible G_morphism where
     toShATerm att0 (G_morphism lid morphism) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 morphism of { (att2,i2) ->
           addATerm (ShAAppl "G_morphism" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_morphism" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ShATermConvertible G_morphism:") i1' 
                in case l of 
                    Logic lid -> (G_morphism lid (fromShATerm att'))
	    u     -> fromShATermError "G_morphism" u
         where
         aterm = getATerm att

instance ShATermConvertible AnyComorphism where
     toShATerm att0 (Comorphism cid) = 
	 case toShATerm att0 (language_name cid) of { (att1,i1) ->
           addATerm (ShAAppl "Comorphism" [i1] []) att1}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "Comorphism" [i1] _) -> 
		let i1' = fromShATerm (getATermByIndex1 i1 att) 
                in propagateErrors 
                    $ lookupComorphism_in_LG i1'
	    u     -> fromShATermError "Comorphism" u
         where
         aterm = getATerm att

instance ShATermConvertible GMorphism where
     toShATerm att0 (GMorphism cid sign1 morphism2) = 
	 case toShATerm att0 (language_name cid) of { (att1,i1) ->
         case toShATerm att1 sign1 of { (att2,i2) ->
         case toShATerm att2 morphism2 of { (att3,i3) ->
           addATerm (ShAAppl "GMorphism" [i1,i2,i3] []) att3}}}
     fromShATerm att = 
           case aterm of
	    (ShAAppl "GMorphism" [i1,i2,i3] _) ->
	 	let i1'  = fromShATerm (getATermByIndex1 i1 att)
                    c  =  propagateErrors $ lookupComorphism_in_LG i1'
                    att' = getATermByIndex1 i2 att
                    att'' = getATermByIndex1 i3 att
                in case c of
		     Comorphism cid ->
                       (GMorphism cid (fromShATerm att') 
                                      (fromShATerm att'') )
	    u     -> fromShATermError "GMorphism" u
         where
         aterm = getATerm att

instance ShATermConvertible Grothendieck where
     toShATerm att0 Grothendieck = 
	 addATerm (ShAAppl "Grothendieck" [] []) att0
     fromShATerm att = case aterm of
                      (ShAAppl "Grothendieck" [] _) -> Grothendieck
		      u     -> fromShATermError "Grothendiek" u
                     where aterm = getATerm att

instance ShATermConvertible AnyLogic where
     toShATerm att0 (Logic lid) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
           addATerm (ShAAppl "Logic" [i1] []) att1}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "Logic" [i1] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                in lookupLogic_in_LG ("ShATermConvertible AnyLogic:") i1'
	    u     -> fromShATermError "AnyLogic" u
         where
         aterm = getATerm att
