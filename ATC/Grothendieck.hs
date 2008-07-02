{-# OPTIONS -fno-warn-missing-signatures #-}
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

module ATC.Grothendieck () where

import Logic.Comorphism
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
  toShATermAux = toShATermAux_SigId
  fromShATermAux = fromShATermAux_SigId

toShATermAux_SigId att0 (SigId a) = do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "SigId" [a'] []) att1
fromShATermAux_SigId ix att0 =
        case getShATerm ix att0 of
            ShAAppl "SigId" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, SigId a') }
            u -> fromShATermError "SigId" u

instance ShATermConvertible MorId where
  toShATermAux = toShATermAux_MorId
  fromShATermAux = fromShATermAux_MorId

toShATermAux_MorId att0 (MorId a) = do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "MorId" [a'] []) att1
fromShATermAux_MorId ix att0 =
        case getShATerm ix att0 of
            ShAAppl "MorId" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, MorId a') }
            u -> fromShATermError "MorId" u

instance ShATermConvertible ThId where
  toShATermAux = toShATermAux_ThId
  fromShATermAux = fromShATermAux_ThId

toShATermAux_ThId att0 (ThId a) = do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "ThId" [a'] []) att1
fromShATermAux_ThId ix att0 =
        case getShATerm ix att0 of
            ShAAppl "ThId" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, ThId a') }
            u -> fromShATermError "ThId" u

instance ShATermConvertible G_basic_spec where
  toShATermAux = toShATermAux_G_basic_spec
  fromShATermAux = fromShATermAux_G_basic_spec

toShATermAux_G_basic_spec att0 (G_basic_spec lid basic_spec) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 basic_spec
         return $ addATerm (ShAAppl "G_basic_spec" [i1,i2] []) att2
fromShATermAux_G_basic_spec ix att =
         case getShATerm ix att of
            ShAAppl "G_basic_spec" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_basic_spec" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_basic_spec lid i2') }}}
            u -> fromShATermError "G_basic_spec" u

instance ShATermConvertible G_sign where
  toShATermAux = toShATermAux_G_sign
  fromShATermAux = fromShATermAux_G_sign

toShATermAux_G_sign att0 (G_sign lid sign si) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 sign
         (att3,i3) <- toShATerm' att2 si
         return $ addATerm (ShAAppl "G_sign" [i1,i2,i3] []) att3
fromShATermAux_G_sign ix att =
         case getShATerm ix att of
            ShAAppl "G_sign" [i1,i2,i3] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_sign" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                case fromShATerm' i3 att2 of { (att3, i3') ->
                (att3, G_sign lid i2' i3') }}}}
            u -> fromShATermError "G_sign" u

instance ShATermConvertible G_symbol where
  toShATermAux = toShATermAux_G_symbol
  fromShATermAux = fromShATermAux_G_symbol

toShATermAux_G_symbol att0 (G_symbol lid symbol) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 symbol
         return $ addATerm (ShAAppl "G_symbol" [i1,i2] []) att2
fromShATermAux_G_symbol ix att =
         case getShATerm ix att of
            ShAAppl "G_symbol" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_symbol" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_symbol lid i2') }}}
            u -> fromShATermError "G_symbol" u

instance ShATermConvertible G_symb_items_list where
  toShATermAux = toShATermAux_G_symb_items_list
  fromShATermAux = fromShATermAux_G_symb_items_list

toShATermAux_G_symb_items_list att0 (G_symb_items_list lid symb_items) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 symb_items
         return $ addATerm (ShAAppl "G_symb_items_list" [i1,i2] []) att2
fromShATermAux_G_symb_items_list ix att =
         case getShATerm ix att of
            ShAAppl "G_symb_items_list" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_symb_items_list" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_symb_items_list lid i2') }}}
            u -> fromShATermError "G_symb_items_list" u

instance ShATermConvertible G_symb_map_items_list where
  toShATermAux = toShATermAux_G_symb_map_items_list
  fromShATermAux = fromShATermAux_G_symb_map_items_list

toShATermAux_G_symb_map_items_list att0
  (G_symb_map_items_list lid symb_map_items) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 symb_map_items
         return $ addATerm (ShAAppl "G_symb_map_items_list" [i1,i2] []) att2
fromShATermAux_G_symb_map_items_list ix att =
         case getShATerm ix att of
            ShAAppl "G_symb_map_items_list" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_symb_map_items_list" i1'
                of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_symb_map_items_list lid i2') }}}
            u -> fromShATermError "G_symb_map_items_list" u

instance ShATermConvertible G_sublogics where
  toShATermAux = toShATermAux_G_sublogics
  fromShATermAux = fromShATermAux_G_sublogics

toShATermAux_G_sublogics att0 (G_sublogics lid sublogics) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 sublogics
         return $ addATerm (ShAAppl "G_sublogics" [i1,i2] []) att2
fromShATermAux_G_sublogics ix att =
         case getShATerm ix att of
            ShAAppl "G_sublogics" [i1,i2] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_sublogics" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                (att2, G_sublogics lid i2') }}}
            u -> fromShATermError "G_sublogics" u

instance ShATermConvertible G_morphism where
  toShATermAux = toShATermAux_G_morphism
  fromShATermAux = fromShATermAux_G_morphism

toShATermAux_G_morphism att0 (G_morphism lid morphism mi) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 morphism
         (att3,i3) <- toShATerm' att2 mi
         return $ addATerm (ShAAppl "G_morphism" [i1,i2,i3] []) att3
fromShATermAux_G_morphism ix att =
         case getShATerm ix att of
            ShAAppl "G_morphism" [i1,i2,i3] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_morphism" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                case fromShATerm' i3 att2 of { (att3, i3') ->
                (att3, G_morphism lid i2' i3') }}}}
            u -> fromShATermError "G_morphism" u

instance ShATermConvertible AnyComorphism where
  toShATermAux = toShATermAux_AnyComorphism
  fromShATermAux = fromShATermAux_AnyComorphism

toShATermAux_AnyComorphism att0 (Comorphism cid) = do
         (att1,i1) <- toShATerm' att0 (language_name cid)
         return $ addATerm (ShAAppl "Comorphism" [i1] []) att1
fromShATermAux_AnyComorphism ix att =
         case getShATerm ix att of
            ShAAppl "Comorphism" [i1] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                (att1, propagateErrors $ lookupComorphism_in_LG i1')}
            u -> fromShATermError "AnyComorphism" u

instance ShATermConvertible GMorphism where
  toShATermAux = toShATermAux_GMorphism
  fromShATermAux = fromShATermAux_GMorphism

toShATermAux_GMorphism att0 (GMorphism cid sign1 si morphism2 mi) = do
         (att1,i1) <- toShATerm' att0 (language_name cid)
         (att2,i2) <- toShATerm' att1 sign1
         (att3,i3) <- toShATerm' att2 si
         (att4,i4) <- toShATerm' att3 morphism2
         (att5,i5) <- toShATerm' att4 mi
         return $ addATerm (ShAAppl "GMorphism" [i1,i2,i3,i4,i5] []) att5
fromShATermAux_GMorphism ix att =
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

instance ShATermConvertible AnyLogic where
  toShATermAux = toShATermAux_AnyLogic
  fromShATermAux = fromShATermAux_AnyLogic
toShATermAux_AnyLogic att0 (Logic lid) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         return $ addATerm (ShAAppl "Logic" [i1] []) att1
fromShATermAux_AnyLogic ix att =
         case getShATerm ix att of
            ShAAppl "Logic" [i1] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                (att1, atcLogicLookup "AnyLogic" i1') }
            u -> fromShATermError "AnyLogic" u

instance ShATermConvertible BasicProof where
  toShATermAux = toShATermAux_BasicProof
  fromShATermAux = fromShATermAux_BasicProof

toShATermAux_BasicProof att0 (BasicProof lid p) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 p
         return $ addATerm (ShAAppl "BasicProof" [i1,i2] []) att2
toShATermAux_BasicProof att0 o = do
         (att1, i1) <- toShATerm' att0 (show o)
         return $ addATerm (ShAAppl "BasicProof" [i1] []) att1
fromShATermAux_BasicProof ix att =
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
  toShATermAux = toShATermAux_G_theory
  fromShATermAux = fromShATermAux_G_theory

toShATermAux_G_theory att0 (G_theory lid sign si sens ti) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 sign
         (att3,i3) <- toShATerm' att2 si
         (att4,i4) <- toShATerm' att3 sens
         (att5,i5) <- toShATerm' att4 ti
         return $ addATerm (ShAAppl "G_theory" [i1,i2,i3,i4,i5] []) att5
fromShATermAux_G_theory ix att =
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
