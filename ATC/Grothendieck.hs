{-
   File: ATC/Grothendieck.hs
   ShATermConvertible instances for the datatypes in Logic/Grothendieck.hs
   Author: Felix Reckers
   Year: 2003
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

instance ATermConvertible G_basic_spec where
     toShATerm att0 (G_basic_spec lid basic_spec) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 basic_spec
         in addATerm (ShAAppl "G_basic_spec" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_basic_spec" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = (getATermByIndex1 i2 att)
		    l = lookupLogic_in_LG ("ATermConvertible G_basic_spec:") i1' 
                in case l of
		    Logic lid -> 
			G_basic_spec lid (fromShATerm_basic_spec lid att') 
         where
         aterm = getATerm att

instance ATermConvertible G_sentence where
     toShATerm att0 (G_sentence lid sentence) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 sentence
         in addATerm (ShAAppl "G_sentence" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_sentence" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
		    l = lookupLogic_in_LG ("ATerm_Convertible G_sentence:") i1' 
                in case l of
                    Logic lid -> (G_sentence lid (fromShATerm_sentence lid att'))
         where
         aterm = getATerm att

instance ATermConvertible G_l_sentence_list where
     toShATerm att0 (G_l_sentence lid n_sentence) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 n_sentence
         in addATerm (ShAAppl "G_l_sentence" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_l_sentence" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
		    l = lookupLogic_in_LG ("ATermConvertible G_l_sentence_list") i1' 
                in case l of
                    Logic lid -> (G_l_sentence lid (fromShATerm_l_sentence_list lid att'))
         where
         aterm = getATerm att

instance ATermConvertible G_sign where
     toShATerm att0 (G_sign lid sign) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 sign
         in addATerm (ShAAppl "G_sign" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_sign" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_sign:") i1' 
                in case l of
                    Logic lid -> (G_sign lid (fromShATerm_sign lid att'))
         where
         aterm = getATerm att

instance ATermConvertible G_sign_list where
     toShATerm att0 (G_sign_list lid signs) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 signs
         in addATerm (ShAAppl "G_sign_list" [i1,i2] []) att2
     fromShATerm att =
         case aterm of
	    (ShAAppl "G_sign_list" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_sign_list:") i1' 
                in case l of
                    Logic lid -> (G_sign_list lid (fromShATerm_sign_list lid att'))
         where
         aterm = getATerm att

instance ATermConvertible G_symbol where
     toShATerm att0 (G_symbol lid symbol) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 symbol
         in addATerm (ShAAppl "G_symbol" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_symbol" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_symbol:") i1' 
                in case l of 
                    Logic lid -> (G_symbol lid (fromShATerm_symbol lid att'))
         where
         aterm = getATerm att 

instance ATermConvertible G_symb_items_list where
     toShATerm att0 (G_symb_items_list lid symb_items) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 symb_items
         in addATerm (ShAAppl "G_symb_items_list" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_symb_items_list" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_symb_items_list:") i1' 
                in case l of
                    Logic lid -> (G_symb_items_list lid (fromShATerm_symb_items_list lid att'))
         where
         aterm = getATerm att

instance ATermConvertible G_symb_map_items_list where
     toShATerm att0 (G_symb_map_items_list lid symb_map_items) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 symb_map_items
         in addATerm (ShAAppl "G_symb_map_items_list" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_symb_map_items_list" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_symb_map_items_list:") i1' 
                in case l of
                    Logic lid -> (G_symb_map_items_list lid (fromShATerm_symb_map_items_list lid att'))
         where
         aterm = getATerm att

instance ATermConvertible G_diagram where
     toShATerm att0 (G_diagram lid diagram) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 diagram
         in addATerm (ShAAppl "G_diagram" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_diagram" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_diagram:") i1' 
                in case l of
                    Logic lid -> (G_diagram lid (fromShATerm_diagram lid att'))
         where
         aterm = getATerm att


instance ATermConvertible G_sublogics where
     toShATerm att0 (G_sublogics lid sublogics) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 sublogics
         in addATerm (ShAAppl "G_sublogics" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_sublogics" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_sublogics:") i1' 
                in case l of 
                    Logic lid -> (G_sublogics lid (fromShATerm_sublogics lid att'))
         where
         aterm = getATerm att 

instance ATermConvertible G_morphism where
     toShATerm att0 (G_morphism lid morphism) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
             (att2,i2) = toShATerm att1 morphism
         in addATerm (ShAAppl "G_morphism" [i1,i2] []) att2
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_morphism" [i1,i2] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    l = lookupLogic_in_LG ("ATermConvertible G_morphism:") i1' 
                in case l of 
                    Logic lid -> (G_morphism lid (fromShATerm_morphism lid att'))
         where
         aterm = getATerm att

---------------------------------------------------------------

instance ATermConvertible AnyComorphism where
     toShATerm att0 (Comorphism cid) = 
	 let (att1,i1) = toShATerm att0 (language_name cid)
         in addATerm (ShAAppl "Comorphism" [i1] []) att1
     fromShATerm att = 
         case aterm of
	    (ShAAppl "Comorphism" [i1] _) -> 
		let i1' = fromShATerm (getATermByIndex1 i1 att) 
                in propagateErrors 
                    $ lookupComorphism_in_LG i1'
         where
         aterm = getATerm att

instance ATermConvertible GMorphism where
     toShATerm att0 (GMorphism cid sign1 morphism2) = 
	 let (att1,i1) = toShATerm att0 (language_name cid)
             (att2,i2) = toShATerm att1 sign1 
             (att3,i3) = toShATerm att2 morphism2
         in addATerm (ShAAppl "GMorphism" [i1,i2,i3] []) att3
     fromShATerm att = 
           case aterm of
	    (ShAAppl "GMorphism" [i1,i2,i3] _) ->
	 	let i1'  = fromShATerm (getATermByIndex1 i1 att)
                    c  =  propagateErrors $ lookupComorphism_in_LG i1'
                    att' = getATermByIndex1 i2 att
                    att'' = getATermByIndex1 i3 att
                in case c of
		     Comorphism cid ->
                       (GMorphism cid (fromShATerm_sign1 cid att') (fromShATerm_morphism2 cid att'') )
         where
         aterm = getATerm att

instance ATermConvertible Grothendieck where
     toShATerm att0 Grothendieck = addATerm (ShAAppl "Grothendieck" [] []) att0
     fromShATerm att = case aterm of
                      (ShAAppl "Grothendieck" [] _) -> Grothendieck
                     where aterm = getATerm att


instance ATermConvertible AnyLogic where
     toShATerm att0 (Logic lid) = 
	 let (att1,i1) = toShATerm att0 (language_name lid)
         in addATerm (ShAAppl "Logic" [i1] []) att1
     fromShATerm att = 
         case aterm of
	    (ShAAppl "Logic" [i1] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                in lookupLogic_in_LG ("ATermConvertible AnyLogic:") i1'
         where
         aterm = getATerm att






