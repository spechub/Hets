{- |
Module      :  $Header$
Description :  ShATermConvertible instances
Copyright   :  (c) C. Maeder, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(imports DevGraph)

derive 'ShATermConvertible' instance
  for the type(s): 'DGNodeLab' 'DGLinkLab' 'DGRule' 'BasicConsProof' 'ThmLinkStatus' 'DGLinkType' 'Conservativity' 'DGOrigin' 'NodeSig' 'MaybeNode' 'UnitSig' 'ImpUnitSigOrSig' 'ArchSig' 'GlobalEntry' 'DGChange'

instances for 'BasicProof' and 'G_theory' need to be given explicitely
-}

module ATC.DevGraph where

import Static.DevGraph
import Logic.Logic
import Common.ATerm.Lib
import Data.Typeable
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
{-! for DGraph derive : ShATermConvertible !-}
{-! for GlobalContext derive : ShATermConvertible !-}

{-! for DGNodeLab derive : Typeable !-}
{-! for DGLinkLab derive : Typeable !-}
{-! for DGRule derive : Typeable !-}
{-! for BasicConsProof derive : Typeable !-}
{-! for ThmLinkStatus derive : Typeable !-}
{-! for DGLinkType derive : Typeable !-}
{-! for Conservativity derive : Typeable !-}
{-! for DGOrigin derive : Typeable !-}
{-! for NodeSig derive : Typeable !-}
{-! for MaybeNode derive : Typeable !-}
{-! for UnitSig derive : Typeable !-}
{-! for ImpUnitSigOrSig derive : Typeable !-}
{-! for ArchSig derive : Typeable !-}
{-! for GlobalEntry derive : Typeable !-}
{-! for DGChange derive : Typeable !-}
{-! for DGraph derive : Typeable !-}
{-! for GlobalContext derive : Typeable !-}

_tc_G_theoryTc :: TyCon
_tc_G_theoryTc = mkTyCon "G_theory"
instance Typeable G_theory where
    typeOf _ = mkTyConApp _tc_G_theoryTc []

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
    toShATermAux att0 (G_theory lid sign _ sens _) = do
         (att1,i1) <- toShATerm' att0 (language_name lid)
         (att2,i2) <- toShATerm' att1 sign
         (att3,i3) <- toShATerm' att2 sens
         return $ addATerm (ShAAppl "G_theory" [i1,i2,i3] []) att3
    fromShATermAux ix att =
         case getShATerm ix att of
            ShAAppl "G_theory" [i1,i2,i3] _ ->
                case fromShATerm' i1 att of { (att1, i1') ->
                case atcLogicLookup "G_theory" i1' of { Logic lid ->
                case fromShATerm' i2 att1 of { (att2, i2') ->
                case fromShATerm' i3 att2 of { (att3, i3') ->
                (att3, G_theory lid i2' 0 i3' 0) }}}}
            u -> fromShATermError "G_theory" u
