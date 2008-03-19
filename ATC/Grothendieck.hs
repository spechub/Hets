{- |
Module      :  $Header$
Description :  manually created ShATermConvertible instances
Copyright   :  (c) Felix Reckers, C. Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (existential types)

'ShATermConvertible' instances for data types from "Logic.Grothendieck"
-}

module ATC.Grothendieck where

import Logic.Grothendieck
import Common.ATerm.Lib
import Data.Typeable
import Common.Result
import Comorphisms.LogicList
import Comorphisms.LogicGraph
import Logic.Logic
import ATC.Prover ()
import ATC.ExtSign ()
import Static.GTheory
import Control.Concurrent.MVar

atcLogicLookup :: String -> String -> AnyLogic
atcLogicLookup s = lookupLogic_in_LG $ "ShATermConvertible " ++ s ++ ":"

instance ShATermConvertible SigId where
    toShATermAux att0 (SigId a) = do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "SigId" [a'] []) att1
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
            ShAAppl "SigId" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, SigId a') }
            u -> fromShATermError "SigId" u

instance ShATermConvertible MorId where
    toShATermAux att0 (MorId a) = do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "MorId" [a'] []) att1
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
            ShAAppl "MorId" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, MorId a') }
            u -> fromShATermError "MorId" u

instance ShATermConvertible ThId where
    toShATermAux att0 (ThId a) = do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "ThId" [a'] []) att1
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
            ShAAppl "ThId" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, ThId a') }
            u -> fromShATermError "ThId" u

instance ShATermConvertible G_basic_spec where
     toShATermAux att0 (G_basic_spec lid basic_spec) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 basic_spec
         return $ addATerm (ShAAppl "G_basic_spec" [i1,i2] []) att2
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "G_basic_spec" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_basic_spec" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_basic_spec lid i2') }}}
            u -> fromShATermError "G_basic_spec" u

instance ShATermConvertible G_sign where
     toShATermAux att0 (G_sign lid sign si) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 sign
         (att3,i3) <- toShATerm' att2 si
         return $ addATerm (ShAAppl "G_sign" [i1,i2,i3] []) att3
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "G_sign" [i1,i2,i3] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_sign" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                case fromShATerm' i3 att2 of { (att3, i3') ->
                (att3, G_sign lid i2' i3') }}}}
            u -> fromShATermError "G_sign" u

instance ShATermConvertible G_symbol where
     toShATermAux att0 (G_symbol lid symbol) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 symbol
         return $ addATerm (ShAAppl "G_symbol" [i1,i2] []) att2
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "G_symbol" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_symbol" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_symbol lid i2') }}}
            u -> fromShATermError "G_symbol" u

instance ShATermConvertible G_symb_items_list where
     toShATermAux att0 (G_symb_items_list lid symb_items) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 symb_items
         return $ addATerm (ShAAppl "G_symb_items_list" [i1,i2] []) att2
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "G_symb_items_list" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_symb_items_list" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_symb_items_list lid i2') }}}
            u -> fromShATermError "G_symb_items_list" u

instance ShATermConvertible G_symb_map_items_list where
     toShATermAux att0 (G_symb_map_items_list lid symb_map_items) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 symb_map_items
         return $ addATerm (ShAAppl "G_symb_map_items_list" [i1,i2] []) att2
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "G_symb_map_items_list" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_symb_map_items_list" i1'
                of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_symb_map_items_list lid i2') }}}
            u -> fromShATermError "G_symb_map_items_list" u

instance ShATermConvertible G_sublogics where
     toShATermAux att0 (G_sublogics lid sublogics) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 sublogics
         return $ addATerm (ShAAppl "G_sublogics" [i1,i2] []) att2
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "G_sublogics" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_sublogics" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_sublogics lid i2') }}}
            u -> fromShATermError "G_sublogics" u

instance ShATermConvertible G_morphism where
     toShATermAux att0 (G_morphism lid morphism mi) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 morphism
         (att3,i3) <- toShATerm' att2 mi
         return $ addATerm (ShAAppl "G_morphism" [i1,i2,i3] []) att3
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "G_morphism" [i1,i2,i3] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_morphism" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                case fromShATerm' i3 att2 of { (att3, i3') ->
                (att3, G_morphism lid i2' i3') }}}}
            u -> fromShATermError "G_morphism" u

instance ShATermConvertible AnyComorphism where
     toShATermAux att0 (Comorphism cid) = do
         (att1,i1) <- toShATerm' att0 (language_name cid)
         return $ addATerm (ShAAppl "Comorphism" [i1] []) att1
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "Comorphism" [i1] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                (att1, propagateErrors $ lookupComorphism_in_LG i1')}
            u -> fromShATermError "AnyComorphism" u

instance ShATermConvertible GMorphism where
     toShATermAux att0 (GMorphism cid sign1 si morphism2 mi) = do
         (att1,i1) <- toShATerm' att0 (language_name cid)
         (att2,i2) <- toShATerm' att1 sign1
         (att3,i3) <- toShATerm' att2 si
         (att4,i4) <- toShATerm' att3 morphism2
         (att5,i5) <- toShATerm' att4 mi
         return $ addATerm (ShAAppl "GMorphism" [i1,i2,i3,i4,i5] []) att5
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "GMorphism" [i1,i2,i3,i4,i5] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case propagateErrors $ lookupComorphism_in_LG i1'
                of { Comorphism cid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                case fromShATerm' i3 att2 of { (att3, i3') ->
                case fromShATerm' i4 att3 of { (att4, i4') ->
                case fromShATerm' i5 att4 of { (att5, i5') ->
                (att5, GMorphism cid i2' i3' i4' i5') }}}}}}
            u -> fromShATermError "GMorphism" u

instance ShATermConvertible Grothendieck where
     toShATermAux att0 Grothendieck =
         return $ addATerm (ShAAppl "Grothendieck" [] []) att0
     fromShATermAux ix att = case getShATerm ix att of
                      ShAAppl "Grothendieck" [] _ -> (att, Grothendieck)
                      u -> fromShATermError "Grothendiek" u

instance ShATermConvertible AnyLogic where
     toShATermAux att0 (Logic lid) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         return $ addATerm (ShAAppl "Logic" [i1] []) att1
     fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "Logic" [i1] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                (att1, atcLogicLookup "AnyLogic" i1') }
            u -> fromShATermError "AnyLogic" u

instance ShATermConvertible BasicProof where
    toShATermAux att0 (BasicProof lid p) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 p
         return $ addATerm (ShAAppl "BasicProof" [i1,i2] []) att2
    toShATermAux att0 o = do
         (att1, i1) <- toShATerm' att0 (show o)
         return $ addATerm (ShAAppl "BasicProof" [i1] []) att1
    fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "BasicProof" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "BasicProof" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, BasicProof lid i2') }}}
            v@(ShAAppl "BasicProof" [i1] _) ->
               case fromShATerm' i1 att of { (att1, i1') ->
               (att1, case i1' of
                 "Guessed" -> Guessed
                 "Conjectured" -> Conjectured
                 "Handwritten" -> Handwritten
                 _ -> fromShATermError "BasicProof" v)}
            u -> fromShATermError "BasicProof" u

instance ShATermConvertible G_theory where
    toShATermAux att0 (G_theory lid sign si sens ti) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 sign
         (att3,i3) <- toShATerm' att2 si
         (att4,i4) <- toShATerm' att3 sens
         (att5,i5) <- toShATerm' att4 ti
         return $ addATerm (ShAAppl "G_theory" [i1,i2,i3,i4,i5] []) att5
    fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "G_theory" [i1,i2,i3,i4,i5] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_theory" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                case fromShATerm' i3 att2 of { (att3, i3') ->
                case fromShATerm' i4 att3 of { (att4, i4') ->
                case fromShATerm' i5 att4 of { (att5, i5') ->
                (att5, G_theory lid i2' i3' i4' i5') }}}}}}
            u -> fromShATermError "G_theory" u

instance Typeable a => ShATermConvertible (MVar a) where
    toShATermAux att0 _ = return $ addATerm (ShAAppl "MVar" [] []) att0
    fromShATermAux ix att = case getShATerm ix att of
        ShAAppl "MVar" [] _ -> (att, error "ShATermConvertible MVar")
        u -> fromShATermError "MVar" u
