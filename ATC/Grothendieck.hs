{- |
Module      :  $Header$
Copyright   :  (c) Felix Reckers and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

module ATC.Grothendieck where

import Logic.Grothendieck
import Common.ATerm.Lib
import Common.Result
import Comorphisms.LogicGraph
import Logic.Logic
import ATC.Comorphism
import ATC.Named
import Logic.Logic
import Logic.Comorphism
import ATC.Graph
import qualified Common.Lib.Set as Set

instance ATermConvertible G_basic_spec where
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
		      ("ATermConvertible G_basic_spec:") i1'  of {
		    Logic lid -> 
			G_basic_spec lid (fromShATerm_basic_spec lid att')}}} 
	    u     -> fromShATermError "G_basic_spec" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_basic_spec\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_basic_spec\""

instance ATermConvertible G_sentence where
     toShATerm att0 (G_sentence lid sentence) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 sentence of { (att2,i2) ->
           addATerm (ShAAppl "G_sentence" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_sentence" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
		    l = lookupLogic_in_LG ("ATerm_Convertible G_sentence:") i1' 
                in case l of
                    Logic lid -> (G_sentence lid (fromShATerm_sentence lid att'))
	    u     -> fromShATermError "G_sentence" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_sentence\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_sentence\""

instance ATermConvertible G_l_sentence_list where
     toShATerm att0 (G_l_sentence lid n_sentence) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 n_sentence of { (att2,i2) ->
            addATerm (ShAAppl "G_l_sentence" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_l_sentence" [i1,i2] _) ->
	       case fromShATerm (getATermByIndex1 i1 att) of { i1' ->
               case getATermByIndex1 i2 att of { att' ->
               case lookupLogic_in_LG 
                        ("ATermConvertible G_l_sentence_list") i1'  of {
                    Logic lid -> (G_l_sentence lid (fromShATerm_l_sentence_list lid att'))}}}
	    u     -> fromShATermError "G_l_sentence" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_l_sentence\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_l_sentence\""

instance ATermConvertible G_sign where
     toShATerm att0 (G_sign lid sign) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 sign of { (att2,i2) ->
           addATerm (ShAAppl "G_sign" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_sign" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_sign:") i1' 
                in case l of
                    Logic lid -> (G_sign lid (fromShATerm_sign lid att'))
	    u     -> fromShATermError "G_sign" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_sign\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_sign\""

instance ATermConvertible G_ext_sign where
     toShATerm att0 (G_ext_sign lid sign _) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 sign of { (att2,i2) ->
           addATerm (ShAAppl "G_ext_sign" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_ext_sign" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_ext_sign:") i1' 
                in case l of
                    Logic lid -> (G_ext_sign lid (fromShATerm_sign lid att') Set.empty)
	    u     -> fromShATermError "G_ext_sign" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_ext_sign\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_ext_sign\""

instance ATermConvertible G_sign_list where
     toShATerm att0 (G_sign_list lid signs) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 signs of { (att2,i2) ->
           addATerm (ShAAppl "G_sign_list" [i1,i2] []) att2}}
     fromShATerm att =
         case aterm of
	    (ShAAppl "G_sign_list" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_sign_list:") i1' 
                in case l of
                    Logic lid -> (G_sign_list lid (fromShATerm_sign_list lid att'))
	    u     -> fromShATermError "G_sign" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_sign_list\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_sign_list\""

instance ATermConvertible G_symbol where
     toShATerm att0 (G_symbol lid symbol) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 symbol of { (att2,i2) ->
           addATerm (ShAAppl "G_symbol" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_symbol" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_symbol:") i1' 
                in case l of 
                    Logic lid -> (G_symbol lid (fromShATerm_symbol lid att'))
	    u     -> fromShATermError "G_symbol" u
         where
         aterm = getATerm att 
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_symbol\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_symbol\""

instance ATermConvertible G_symb_items_list where
     toShATerm att0 (G_symb_items_list lid symb_items) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 symb_items of { (att2,i2) ->
           addATerm (ShAAppl "G_symb_items_list" [i1,i2] []) att2 }}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_symb_items_list" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_symb_items_list:") i1' 
                in case l of
                    Logic lid -> (G_symb_items_list lid (fromShATerm_symb_items_list lid att'))
	    u     -> fromShATermError "G_symb_items_list" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_symb_items_list\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_symb_items_list\""

instance ATermConvertible G_symb_map_items_list where
     toShATerm att0 (G_symb_map_items_list lid symb_map_items) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 symb_map_items of { (att2,i2) ->
           addATerm (ShAAppl "G_symb_map_items_list" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_symb_map_items_list" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_symb_map_items_list:") i1' 
                in case l of
                    Logic lid -> (G_symb_map_items_list lid (fromShATerm_symb_map_items_list lid att'))
	    u     -> fromShATermError "G_symb_map_items_list" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_symb_map_items_list\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_symb_map_items_list\""

instance ATermConvertible G_diagram where
     toShATerm att0 (G_diagram lid diagram) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 diagram of { (att2,i2) ->
           addATerm (ShAAppl "G_diagram" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_diagram" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_diagram:") i1' 
                in case l of
                    Logic lid -> (G_diagram lid (fromShATerm_diagram lid att'))
	    u     -> fromShATermError "G_diagram" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_diagram\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_diagram\""

instance ATermConvertible G_sublogics where
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
                          ("ATermConvertible G_sublogics:") i1' 
                in case l of 
                    Logic lid -> 
                     (G_sublogics lid (fromShATerm_sublogics lid att'))
	    u     -> fromShATermError "G_sublogics" u
         where
         aterm = getATerm att 
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_sublogic\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_sublogics\""

instance ATermConvertible G_morphism where
     toShATerm att0 (G_morphism lid morphism) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 morphism of { (att2,i2) ->
           addATerm (ShAAppl "G_morphism" [i1,i2] []) att2}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_morphism" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_morphism:") i1' 
                in case l of 
                    Logic lid -> (G_morphism lid (fromShATerm_morphism lid att'))
	    u     -> fromShATermError "G_morphism" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"G_morphism\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"G_morphism\""

---------------------------------------------------------------

instance ATermConvertible AnyComorphism where
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
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Comorphism\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Comorphism\""

instance ATermConvertible GMorphism where
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
                       (GMorphism cid (fromShATerm_sign1 cid att') 
                                      (fromShATerm_morphism2 cid att'') )
	    u     -> fromShATermError "GMorphism" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"GMorphism\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"GMorphism\""

instance ATermConvertible Grothendieck where
     toShATerm att0 Grothendieck = 
	 addATerm (ShAAppl "Grothendieck" [] []) att0
     fromShATerm att = case aterm of
                      (ShAAppl "Grothendieck" [] _) -> Grothendieck
		      u     -> fromShATermError "Grothendiek" u
                     where aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Grothendieck\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Grothendieck\""


instance ATermConvertible AnyLogic where
     toShATerm att0 (Logic lid) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
           addATerm (ShAAppl "Logic" [i1] []) att1}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "Logic" [i1] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                in lookupLogic_in_LG ("ATermConvertible AnyLogic:") i1'
	    u     -> fromShATermError "AnyLogic" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"AnyLogic\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"AnyLogic\""






