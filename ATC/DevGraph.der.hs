{- |
Module      :  $Header$
Description :  ShATermConvertible instances
Copyright   :  (c) Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

derive 'ShATermConvertible' instance 
  for the type(s): 'DGNodeLab' 'DGLinkLab' 'DGRule' 'BasicConsProof' 'ThmLinkStatus' 'DGLinkType' 'Conservativity' 'DGOrigin' 'NodeSig' 'MaybeNode' 'UnitSig' 'ImpUnitSigOrSig' 'ArchSig' 'GlobalEntry' 'SenStatus' 'DGChange'

instances for 'BasicProof' and 'G_theory' need to be given explicitely


-}


module ATC.DevGraph where

import Static.DevGraph
import Logic.Logic
import Common.ATerm.Lib
import ATC.AS_Library()
import ATC.Prover()
import ATC.Grothendieck

{-! for DGNodeLab derive : ShATermConvertible !-}
{-! for DGLinkLab derive : ShATermConvertible !-}
{-! for DGRule derive : ShATermConvertible !-}
{-! for BasicConsProof derive : ShATermConvertible !-}
{-! for ThmLinkStatus derive : ShATermConvertible !-}
{-! for DGLinkType derive : ShATermConvertible !-}
{-! for Conservativity derive : ShATermConvertible !-}
{-! for DGOrigin derive : ShATermConvertible !-}
{-! for NodeSig derive : ShATermConvertible !-}
{-! for MaybeNode derive : ShATermConvertible !-}
{-! for UnitSig derive : ShATermConvertible !-}
{-! for ImpUnitSigOrSig derive : ShATermConvertible !-}
{-! for ArchSig derive : ShATermConvertible !-}
{-! for GlobalEntry derive : ShATermConvertible !-}
{-! for DGChange derive : ShATermConvertible !-}

instance ShATermConvertible BasicProof where
     toShATerm att0 (BasicProof lid p) = 
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 p of { (att2,i2) ->
            addATerm (ShAAppl "BasicProof" [i1,i2] []) att2}}
     toShATerm att0 Guessed =
         case toShATerm att0 (show Guessed) of { (att1, i1) ->
            addATerm (ShAAppl "BasicProof" [i1] []) att1}
     toShATerm att0 Conjectured =
         case toShATerm att0 (show Conjectured) of { (att1, i1) ->
            addATerm (ShAAppl "BasicProof" [i1] []) att1}
     toShATerm att0 Handwritten =
         case toShATerm att0 (show Handwritten) of { (att1, i1) ->
            addATerm (ShAAppl "BasicProof" [i1] []) att1}

     fromShATerm att = 
         case getATerm att of
            (ShAAppl "BasicProof" [i1,i2] _) ->
               case fromShATerm (getATermByIndex1 i1 att) of { i1' ->
               case getATermByIndex1 i2 att of { att' ->
               case atcLogicLookup "BasicProof" i1'  of {
                    Logic lid -> BasicProof lid (fromShATerm att')}}}
            v@(ShAAppl "BasicProof" [i1] _) ->
               case fromShATerm (getATermByIndex1 i1 att) of { i1' ->
               case i1' of
                 "Guessed" -> Guessed
                 "Conjectured" -> Conjectured
                 "Handwritten" -> Handwritten
                 _ -> fromShATermError "BasicProof" v}
            u     -> fromShATermError "BasicProof" u

instance ShATermConvertible G_theory where
     toShATerm att0 (G_theory lid sign sens) = 
         case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 sign of { (att2,i2) ->
         case toShATerm att2 sens of { (att3,i3) ->
           addATerm (ShAAppl "G_theory" [i1,i2,i3] []) att3}}}
     fromShATerm att = 
         case getATerm att of
            (ShAAppl "G_theory" [i1,i2,i3] _) ->
                let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    att'' = getATermByIndex1 i3 att'
                in case atcLogicLookup "G_theory" i1' of
                    Logic lid -> G_theory lid (fromShATerm att') 
                                               (fromShATerm att'')
            u     -> fromShATermError "G_theory" u
