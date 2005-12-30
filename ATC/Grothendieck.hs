{- |
Module      :  $Header$
Copyright   :  (c) Felix Reckers and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (existential types)

'ShATermConvertible' instances for data types from "Logic.Grothendieck"
-}

module ATC.Grothendieck where

import Logic.Grothendieck
import Common.ATerm.Lib
import Common.DynamicUtils
import Common.Result
import Comorphisms.LogicList
import Comorphisms.LogicGraph
import Logic.Logic
import qualified Common.Lib.Set as Set

_tc_G_basic_specTc :: TyCon
_tc_G_basic_specTc = mkTyCon "G_basic_spec"
instance Typeable G_basic_spec where
    typeOf _ = mkTyConApp _tc_G_basic_specTc []

_tc_G_ext_signTc :: TyCon
_tc_G_ext_signTc = mkTyCon "G_ext_sign"
instance Typeable G_ext_sign where
    typeOf _ = mkTyConApp _tc_G_ext_signTc []

_tc_G_sign_listTc :: TyCon
_tc_G_sign_listTc = mkTyCon "G_sign_list"
instance Typeable G_sign_list where
    typeOf _ = mkTyConApp _tc_G_sign_listTc []

_tc_G_symbolTc :: TyCon
_tc_G_symbolTc = mkTyCon "G_symbol"
instance Typeable G_symbol where
    typeOf _ = mkTyConApp _tc_G_symbolTc []

_tc_G_symb_items_listTc :: TyCon
_tc_G_symb_items_listTc = mkTyCon "G_symb_items_list"
instance Typeable G_symb_items_list where
    typeOf _ = mkTyConApp _tc_G_symb_items_listTc []

_tc_G_symb_map_items_listTc :: TyCon
_tc_G_symb_map_items_listTc = mkTyCon "G_symb_map_items_list"
instance Typeable G_symb_map_items_list where
    typeOf _ = mkTyConApp _tc_G_symb_map_items_listTc []

_tc_G_diagramTc :: TyCon
_tc_G_diagramTc = mkTyCon "G_diagram"
instance Typeable G_diagram where
    typeOf _ = mkTyConApp _tc_G_diagramTc []

_tc_GMorphismTc :: TyCon
_tc_GMorphismTc = mkTyCon "GMorphism"
instance Typeable GMorphism where
    typeOf _ = mkTyConApp _tc_GMorphismTc []

_tc_G_morphismTc :: TyCon
_tc_G_morphismTc = mkTyCon "G_morphism"
instance Typeable G_morphism where
    typeOf _ = mkTyConApp _tc_G_morphismTc []

_tc_GrothendieckTc :: TyCon
_tc_GrothendieckTc = mkTyCon "Grothendieck"
instance Typeable Grothendieck where
    typeOf _ = mkTyConApp _tc_GrothendieckTc []

atcLogicLookup :: String -> String -> AnyLogic
atcLogicLookup s = lookupLogic_in_LG $ "ShATermConvertible " ++ s ++ ":"

instance ShATermConvertible G_basic_spec where
     toShATerm att0 (G_basic_spec lid basic_spec) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 basic_spec of { (att2,i2) ->
           addATerm (ShAAppl "G_basic_spec" [i1,i2] []) att2}}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_basic_spec" [i1,i2] _ ->
                case fromShATerm (getATermByIndex1 i1 att) of { i1' ->
                case (getATermByIndex1 i2 att) of { att' ->
                case atcLogicLookup "G_basic_spec" i1'  of {
                    Logic lid ->
                        G_basic_spec lid (fromShATerm att')}}}
            u -> fromShATermError "G_basic_spec" u

instance ShATermConvertible G_sign where
     toShATerm att0 (G_sign lid sign) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 sign of { (att2,i2) ->
           addATerm (ShAAppl "G_sign" [i1,i2] []) att2}}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_sign" [i1,i2] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                in case atcLogicLookup "G_sign" i1' of
                    Logic lid -> G_sign lid (fromShATerm att')
            u -> fromShATermError "G_sign" u

instance ShATermConvertible G_ext_sign where
     toShATerm att0 (G_ext_sign lid sign _) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 sign of { (att2,i2) ->
           addATerm (ShAAppl "G_ext_sign" [i1,i2] []) att2}}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_ext_sign" [i1,i2] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                in case atcLogicLookup "G_ext_sign"
                   i1' of
                    Logic lid -> G_ext_sign lid (fromShATerm att') Set.empty
            u -> fromShATermError "G_ext_sign" u

instance ShATermConvertible G_sign_list where
     toShATerm att0 (G_sign_list lid signs) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 signs of { (att2,i2) ->
           addATerm (ShAAppl "G_sign_list" [i1,i2] []) att2}}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_sign_list" [i1,i2] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                in case atcLogicLookup "G_sign_list"
                   i1' of Logic lid -> G_sign_list lid (fromShATerm att')
            u -> fromShATermError "G_sign_list" u

instance ShATermConvertible G_symbol where
     toShATerm att0 (G_symbol lid symbol) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 symbol of { (att2,i2) ->
           addATerm (ShAAppl "G_symbol" [i1,i2] []) att2}}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_symbol" [i1,i2] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                in case atcLogicLookup "G_symbol"
                   i1' of Logic lid -> G_symbol lid (fromShATerm att')
            u -> fromShATermError "G_symbol" u

instance ShATermConvertible G_symb_items_list where
     toShATerm att0 (G_symb_items_list lid symb_items) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 symb_items of { (att2,i2) ->
           addATerm (ShAAppl "G_symb_items_list" [i1,i2] []) att2 }}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_symb_items_list" [i1,i2] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                in case atcLogicLookup
                       "G_symb_items_list" i1' of
                    Logic lid -> G_symb_items_list lid (fromShATerm att')
            u -> fromShATermError "G_symb_items_list" u

instance ShATermConvertible G_symb_map_items_list where
     toShATerm att0 (G_symb_map_items_list lid symb_map_items) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 symb_map_items of { (att2,i2) ->
           addATerm (ShAAppl "G_symb_map_items_list" [i1,i2] []) att2}}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_symb_map_items_list" [i1,i2] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                in case atcLogicLookup
                       "G_symb_map_items_list" i1' of
                    Logic lid -> G_symb_map_items_list lid (fromShATerm att')
            u -> fromShATermError "G_symb_map_items_list" u

instance ShATermConvertible G_diagram where
     toShATerm att0 (G_diagram lid diagram) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 diagram of { (att2,i2) ->
           addATerm (ShAAppl "G_diagram" [i1,i2] []) att2}}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_diagram" [i1,i2] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                in case atcLogicLookup "G_diagram"
                   i1' of Logic lid -> G_diagram lid (fromShATerm att')
            u -> fromShATermError "G_diagram" u

instance ShATermConvertible G_sublogics where
     toShATerm att0 (G_sublogics lid sublogics) =
         case toShATerm att0 (language_name lid)  of { (att1,i1) ->
         case toShATerm att1 sublogics of { (att2,i2) ->
           addATerm (ShAAppl "G_sublogics" [i1,i2] []) att2}}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_sublogics" [i1,i2] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                in case atcLogicLookup
                          "G_sublogics" i1' of
                    Logic lid -> G_sublogics lid (fromShATerm att')
            u -> fromShATermError "G_sublogics" u

instance ShATermConvertible G_morphism where
     toShATerm att0 (G_morphism lid morphism) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 morphism of { (att2,i2) ->
           addATerm (ShAAppl "G_morphism" [i1,i2] []) att2}}
     fromShATerm att =
         case getATerm att of
            ShAAppl "G_morphism" [i1,i2] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                in case atcLogicLookup "G_morphism"
                   i1' of Logic lid -> G_morphism lid (fromShATerm att')
            u -> fromShATermError "G_morphism" u

instance ShATermConvertible AnyComorphism where
     toShATerm att0 (Comorphism cid) =
         case toShATerm att0 (language_name cid) of { (att1,i1) ->
           addATerm (ShAAppl "Comorphism" [i1] []) att1}
     fromShATerm att =
         case getATerm att of
            ShAAppl "Comorphism" [i1] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                in propagateErrors
                    $ lookupComorphism_in_LG i1'
            u -> fromShATermError "AnyComorphism" u

instance ShATermConvertible GMorphism where
     toShATerm att0 (GMorphism cid sign1 morphism2) =
         case toShATerm att0 (language_name cid) of { (att1,i1) ->
         case toShATerm att1 sign1 of { (att2,i2) ->
         case toShATerm att2 morphism2 of { (att3,i3) ->
           addATerm (ShAAppl "GMorphism" [i1,i2,i3] []) att3}}}
     fromShATerm att =
           case getATerm att of
            ShAAppl "GMorphism" [i1,i2,i3] _ ->
                let i1'  = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    att'' = getATermByIndex1 i3 att
                in case propagateErrors $ lookupComorphism_in_LG i1' of
                     Comorphism cid ->
                       GMorphism cid (fromShATerm att') (fromShATerm att'')
            u -> fromShATermError "GMorphism" u

instance ShATermConvertible Grothendieck where
     toShATerm att0 Grothendieck =
         addATerm (ShAAppl "Grothendieck" [] []) att0
     fromShATerm att = case getATerm att of
                      ShAAppl "Grothendieck" [] _ -> Grothendieck
                      u -> fromShATermError "Grothendiek" u

instance ShATermConvertible AnyLogic where
     toShATerm att0 (Logic lid) =
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
           addATerm (ShAAppl "Logic" [i1] []) att1}
     fromShATerm att =
         case getATerm att of
            ShAAppl "Logic" [i1] _ ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                in atcLogicLookup "AnyLogic" i1'
            u -> fromShATermError "AnyLogic" u
