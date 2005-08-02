{- |
Module      :  ATC/DevGraph.der.hs
Description :  generated ShATermConvertible instances
Copyright   :  (c) Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

manual 'ShATermConvertible' instance 
  for the type(s): 'BasicProof' 'DGNodeLab' 'DGLinkLab' 'DGRule' 'BasicConsProof' 'ThmLinkStatus' 'DGLinkType' 'Conservativity' 'DGOrigin' 'NodeSig' 'MaybeNode' 'UnitSig' 'ImpUnitSigOrSig' 'ArchSig' 'GlobalEntry' 'Decorated' 'G_theory'
-}


module ATC.DevGraph where

import Static.DevGraph
import Logic.Logic
import Comorphisms.LogicGraph
import Common.ATerm.Lib
import ATC.AS_Library()
import ATC.Prover()
import ATC.Grothendieck()

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
               case lookupLogic_in_LG 
                        ("ShATermConvertible BasicProof") i1'  of {
                    Logic lid -> (BasicProof lid (fromShATerm att'))}}}
            v@(ShAAppl "BasicProof" [i1] _) ->
               case fromShATerm (getATermByIndex1 i1 att) of { i1' ->
               case i1' of
                 "Guessed" -> Guessed
                 "Conjectured" -> Conjectured
                 "Handwritten" -> Handwritten
                 _ -> fromShATermError "BasicProof" v}
	    u     -> fromShATermError "BasicProof" u

instance ShATermConvertible DGNodeLab where
    toShATerm att0 (DGNode a b c d e) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        case toShATerm att3 d of { (att4,d') ->
        case toShATerm att4 e of { (att5,e') ->
        addATerm (ShAAppl "DGNode" [a',b',c',d',e'] []) att5 }}}}}
    toShATerm att0 (DGRef a b c d e) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        case toShATerm att3 d of { (att4,d') ->
        case toShATerm att4 e of { (att5,e') ->
        addATerm (ShAAppl "DGRef" [a',b',c',d',e'] []) att5 }}}}}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "DGNode" [a,b,c,d,e] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    case fromShATerm (getATermByIndex1 c att) of { c' ->
                    case fromShATerm (getATermByIndex1 d att) of { d' ->
                    case fromShATerm (getATermByIndex1 e att) of { e' ->
                    (DGNode a' b' c' d' e') }}}}}
            (ShAAppl "DGRef" [a,b,c,d,e] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    case fromShATerm (getATermByIndex1 c att) of { c' ->
                    case fromShATerm (getATermByIndex1 d att) of { d' ->
                    case fromShATerm (getATermByIndex1 e att) of { e' ->
                    (DGRef a' b' c' d' e') }}}}}
            u -> fromShATermError "DGNodeLab" u

instance ShATermConvertible DGLinkLab where
    toShATerm att0 (DGLink a b c) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        addATerm (ShAAppl "DGLink" [a',b',c'] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "DGLink" [a,b,c] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    case fromShATerm (getATermByIndex1 c att) of { c' ->
                    (DGLink a' b' c') }}}
            u -> fromShATermError "DGLinkLab" u

instance ShATermConvertible DGRule where
    toShATerm att0 TheoremHideShift =
        addATerm (ShAAppl "TheoremHideShift" [] []) att0
    toShATerm att0 (HideTheoremShift a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "HideTheoremShift" [a'] []) att1 }
    toShATerm att0 Borrowing =
        addATerm (ShAAppl "Borrowing" [] []) att0
    toShATerm att0 ConsShift =
        addATerm (ShAAppl "ConsShift" [] []) att0
    toShATerm att0 DefShift =
        addATerm (ShAAppl "DefShift" [] []) att0
    toShATerm att0 MonoShift =
        addATerm (ShAAppl "MonoShift" [] []) att0
    toShATerm att0 ConsComp =
        addATerm (ShAAppl "ConsComp" [] []) att0
    toShATerm att0 DefComp =
        addATerm (ShAAppl "DefComp" [] []) att0
    toShATerm att0 MonoComp =
        addATerm (ShAAppl "MonoComp" [] []) att0
    toShATerm att0 DefToMono =
        addATerm (ShAAppl "DefToMono" [] []) att0
    toShATerm att0 MonoToCons =
        addATerm (ShAAppl "MonoToCons" [] []) att0
    toShATerm att0 FreeIsMono =
        addATerm (ShAAppl "FreeIsMono" [] []) att0
    toShATerm att0 MonoIsFree =
        addATerm (ShAAppl "MonoIsFree" [] []) att0
    toShATerm att0 Composition =
        addATerm (ShAAppl "Composition" [] []) att0
    toShATerm att0 (GlobDecomp a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "GlobDecomp" [a'] []) att1 }
    toShATerm att0 (LocDecomp a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "LocDecomp" [a'] []) att1 }
    toShATerm att0 (LocSubsumption a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "LocSubsumption" [a'] []) att1 }
    toShATerm att0 (GlobSubsumption a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "GlobSubsumption" [a'] []) att1 }
    toShATerm att0 LocalInference =
        addATerm (ShAAppl "LocalInference" [] []) att0
    toShATerm att0 (BasicInference a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "BasicInference" [a'] []) att1 }
    toShATerm att0 (BasicConsInference a b) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        addATerm (ShAAppl "BasicConsInference" [a',b'] []) att2 }}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "TheoremHideShift" [] _) ->
                    TheoremHideShift
            (ShAAppl "HideTheoremShift" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (HideTheoremShift a') }
            (ShAAppl "Borrowing" [] _) ->
                    Borrowing
            (ShAAppl "ConsShift" [] _) ->
                    ConsShift
            (ShAAppl "DefShift" [] _) ->
                    DefShift
            (ShAAppl "MonoShift" [] _) ->
                    MonoShift
            (ShAAppl "ConsComp" [] _) ->
                    ConsComp
            (ShAAppl "DefComp" [] _) ->
                    DefComp
            (ShAAppl "MonoComp" [] _) ->
                    MonoComp
            (ShAAppl "DefToMono" [] _) ->
                    DefToMono
            (ShAAppl "MonoToCons" [] _) ->
                    MonoToCons
            (ShAAppl "FreeIsMono" [] _) ->
                    FreeIsMono
            (ShAAppl "MonoIsFree" [] _) ->
                    MonoIsFree
            (ShAAppl "Composition" [] _) ->
                    Composition
            (ShAAppl "GlobDecomp" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (GlobDecomp a') }
            (ShAAppl "LocDecomp" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (LocDecomp a') }
            (ShAAppl "LocSubsumption" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (LocSubsumption a') }
            (ShAAppl "GlobSubsumption" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (GlobSubsumption a') }
            (ShAAppl "LocalInference" [] _) ->
                    LocalInference
            (ShAAppl "BasicInference" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (BasicInference a') }
            (ShAAppl "BasicConsInference" [a,b] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    (BasicConsInference a' b') }}
            u -> fromShATermError "DGRule" u

instance ShATermConvertible BasicConsProof where
    toShATerm att0 BasicConsProof =
        addATerm (ShAAppl "BasicConsProof" [] []) att0
    fromShATerm att =
        case getATerm att of
            (ShAAppl "BasicConsProof" [] _) ->
                    BasicConsProof
            u -> fromShATermError "BasicConsProof" u

instance ShATermConvertible ThmLinkStatus where
    toShATerm att0 LeftOpen =
        addATerm (ShAAppl "LeftOpen" [] []) att0
    toShATerm att0 (Proven a b) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        addATerm (ShAAppl "Proven" [a',b'] []) att2 }}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "LeftOpen" [] _) ->
                    LeftOpen
            (ShAAppl "Proven" [a,b] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    (Proven a' b') }}
            u -> fromShATermError "ThmLinkStatus" u

instance ShATermConvertible DGLinkType where
    toShATerm att0 LocalDef =
        addATerm (ShAAppl "LocalDef" [] []) att0
    toShATerm att0 GlobalDef =
        addATerm (ShAAppl "GlobalDef" [] []) att0
    toShATerm att0 HidingDef =
        addATerm (ShAAppl "HidingDef" [] []) att0
    toShATerm att0 (FreeDef a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "FreeDef" [a'] []) att1 }
    toShATerm att0 (CofreeDef a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "CofreeDef" [a'] []) att1 }
    toShATerm att0 (LocalThm a b c) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        addATerm (ShAAppl "LocalThm" [a',b',c'] []) att3 }}}
    toShATerm att0 (GlobalThm a b c) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        addATerm (ShAAppl "GlobalThm" [a',b',c'] []) att3 }}}
    toShATerm att0 (HidingThm a b) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        addATerm (ShAAppl "HidingThm" [a',b'] []) att2 }}
    toShATerm att0 (FreeThm a b) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        addATerm (ShAAppl "FreeThm" [a',b'] []) att2 }}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "LocalDef" [] _) ->
                    LocalDef
            (ShAAppl "GlobalDef" [] _) ->
                    GlobalDef
            (ShAAppl "HidingDef" [] _) ->
                    HidingDef
            (ShAAppl "FreeDef" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (FreeDef a') }
            (ShAAppl "CofreeDef" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (CofreeDef a') }
            (ShAAppl "LocalThm" [a,b,c] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    case fromShATerm (getATermByIndex1 c att) of { c' ->
                    (LocalThm a' b' c') }}}
            (ShAAppl "GlobalThm" [a,b,c] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    case fromShATerm (getATermByIndex1 c att) of { c' ->
                    (GlobalThm a' b' c') }}}
            (ShAAppl "HidingThm" [a,b] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    (HidingThm a' b') }}
            (ShAAppl "FreeThm" [a,b] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    (FreeThm a' b') }}
            u -> fromShATermError "DGLinkType" u

instance ShATermConvertible Conservativity where
    toShATerm att0 None =
        addATerm (ShAAppl "None" [] []) att0
    toShATerm att0 Cons =
        addATerm (ShAAppl "Cons" [] []) att0
    toShATerm att0 Mono =
        addATerm (ShAAppl "Mono" [] []) att0
    toShATerm att0 Def =
        addATerm (ShAAppl "Def" [] []) att0
    fromShATerm att =
        case getATerm att of
            (ShAAppl "None" [] _) ->
                    None
            (ShAAppl "Cons" [] _) ->
                    Cons
            (ShAAppl "Mono" [] _) ->
                    Mono
            (ShAAppl "Def" [] _) ->
                    Def
            u -> fromShATermError "Conservativity" u

instance ShATermConvertible DGOrigin where
    toShATerm att0 DGBasic =
        addATerm (ShAAppl "DGBasic" [] []) att0
    toShATerm att0 DGExtension =
        addATerm (ShAAppl "DGExtension" [] []) att0
    toShATerm att0 DGTranslation =
        addATerm (ShAAppl "DGTranslation" [] []) att0
    toShATerm att0 DGUnion =
        addATerm (ShAAppl "DGUnion" [] []) att0
    toShATerm att0 DGHiding =
        addATerm (ShAAppl "DGHiding" [] []) att0
    toShATerm att0 DGRevealing =
        addATerm (ShAAppl "DGRevealing" [] []) att0
    toShATerm att0 DGRevealTranslation =
        addATerm (ShAAppl "DGRevealTranslation" [] []) att0
    toShATerm att0 DGFree =
        addATerm (ShAAppl "DGFree" [] []) att0
    toShATerm att0 DGCofree =
        addATerm (ShAAppl "DGCofree" [] []) att0
    toShATerm att0 DGLocal =
        addATerm (ShAAppl "DGLocal" [] []) att0
    toShATerm att0 DGClosed =
        addATerm (ShAAppl "DGClosed" [] []) att0
    toShATerm att0 DGClosedLenv =
        addATerm (ShAAppl "DGClosedLenv" [] []) att0
    toShATerm att0 DGLogicQual =
        addATerm (ShAAppl "DGLogicQual" [] []) att0
    toShATerm att0 DGLogicQualLenv =
        addATerm (ShAAppl "DGLogicQualLenv" [] []) att0
    toShATerm att0 DGData =
        addATerm (ShAAppl "DGData" [] []) att0
    toShATerm att0 DGFormalParams =
        addATerm (ShAAppl "DGFormalParams" [] []) att0
    toShATerm att0 DGImports =
        addATerm (ShAAppl "DGImports" [] []) att0
    toShATerm att0 (DGSpecInst a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "DGSpecInst" [a'] []) att1 }
    toShATerm att0 DGFitSpec =
        addATerm (ShAAppl "DGFitSpec" [] []) att0
    toShATerm att0 (DGView a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "DGView" [a'] []) att1 }
    toShATerm att0 (DGFitView a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "DGFitView" [a'] []) att1 }
    toShATerm att0 (DGFitViewImp a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "DGFitViewImp" [a'] []) att1 }
    toShATerm att0 (DGFitViewA a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "DGFitViewA" [a'] []) att1 }
    toShATerm att0 (DGFitViewAImp a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "DGFitViewAImp" [a'] []) att1 }
    toShATerm att0 DGProof =
        addATerm (ShAAppl "DGProof" [] []) att0
    fromShATerm att =
        case getATerm att of
            (ShAAppl "DGBasic" [] _) ->
                    DGBasic
            (ShAAppl "DGExtension" [] _) ->
                    DGExtension
            (ShAAppl "DGTranslation" [] _) ->
                    DGTranslation
            (ShAAppl "DGUnion" [] _) ->
                    DGUnion
            (ShAAppl "DGHiding" [] _) ->
                    DGHiding
            (ShAAppl "DGRevealing" [] _) ->
                    DGRevealing
            (ShAAppl "DGRevealTranslation" [] _) ->
                    DGRevealTranslation
            (ShAAppl "DGFree" [] _) ->
                    DGFree
            (ShAAppl "DGCofree" [] _) ->
                    DGCofree
            (ShAAppl "DGLocal" [] _) ->
                    DGLocal
            (ShAAppl "DGClosed" [] _) ->
                    DGClosed
            (ShAAppl "DGClosedLenv" [] _) ->
                    DGClosedLenv
            (ShAAppl "DGLogicQual" [] _) ->
                    DGLogicQual
            (ShAAppl "DGLogicQualLenv" [] _) ->
                    DGLogicQualLenv
            (ShAAppl "DGData" [] _) ->
                    DGData
            (ShAAppl "DGFormalParams" [] _) ->
                    DGFormalParams
            (ShAAppl "DGImports" [] _) ->
                    DGImports
            (ShAAppl "DGSpecInst" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (DGSpecInst a') }
            (ShAAppl "DGFitSpec" [] _) ->
                    DGFitSpec
            (ShAAppl "DGView" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (DGView a') }
            (ShAAppl "DGFitView" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (DGFitView a') }
            (ShAAppl "DGFitViewImp" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (DGFitViewImp a') }
            (ShAAppl "DGFitViewA" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (DGFitViewA a') }
            (ShAAppl "DGFitViewAImp" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (DGFitViewAImp a') }
            (ShAAppl "DGProof" [] _) ->
                    DGProof
            u -> fromShATermError "DGOrigin" u

instance ShATermConvertible NodeSig where
    toShATerm att0 (NodeSig a b) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        addATerm (ShAAppl "NodeSig" [a',b'] []) att2 }}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "NodeSig" [a,b] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    (NodeSig a' b') }}
            u -> fromShATermError "NodeSig" u

instance ShATermConvertible MaybeNode where
    toShATerm att0 (JustNode a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "JustNode" [a'] []) att1 }
    toShATerm att0 (EmptyNode a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "EmptyNode" [a'] []) att1 }
    fromShATerm att =
        case getATerm att of
            (ShAAppl "JustNode" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (JustNode a') }
            (ShAAppl "EmptyNode" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (EmptyNode a') }
            u -> fromShATermError "MaybeNode" u

instance ShATermConvertible UnitSig where
    toShATerm att0 (Unit_sig a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "Unit_sig" [a'] []) att1 }
    toShATerm att0 (Par_unit_sig a b) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        addATerm (ShAAppl "Par_unit_sig" [a',b'] []) att2 }}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "Unit_sig" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (Unit_sig a') }
            (ShAAppl "Par_unit_sig" [a,b] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    (Par_unit_sig a' b') }}
            u -> fromShATermError "UnitSig" u

instance ShATermConvertible ImpUnitSigOrSig where
    toShATerm att0 (Imp_unit_sig a b) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        addATerm (ShAAppl "Imp_unit_sig" [a',b'] []) att2 }}
    toShATerm att0 (Sig a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "Sig" [a'] []) att1 }
    fromShATerm att =
        case getATerm att of
            (ShAAppl "Imp_unit_sig" [a,b] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    (Imp_unit_sig a' b') }}
            (ShAAppl "Sig" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (Sig a') }
            u -> fromShATermError "ImpUnitSigOrSig" u

instance ShATermConvertible ArchSig where
    toShATerm att0 (ArchSig a b) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        addATerm (ShAAppl "ArchSig" [a',b'] []) att2 }}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "ArchSig" [a,b] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    (ArchSig a' b') }}
            u -> fromShATermError "ArchSig" u

instance ShATermConvertible GlobalEntry where
    toShATerm att0 (SpecEntry a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "SpecEntry" [a'] []) att1 }
    toShATerm att0 (ViewEntry a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "ViewEntry" [a'] []) att1 }
    toShATerm att0 (ArchEntry a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "ArchEntry" [a'] []) att1 }
    toShATerm att0 (UnitEntry a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "UnitEntry" [a'] []) att1 }
    toShATerm att0 RefEntry =
        addATerm (ShAAppl "RefEntry" [] []) att0
    fromShATerm att =
        case getATerm att of
            (ShAAppl "SpecEntry" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (SpecEntry a') }
            (ShAAppl "ViewEntry" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (ViewEntry a') }
            (ShAAppl "ArchEntry" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (ArchEntry a') }
            (ShAAppl "UnitEntry" [a] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    (UnitEntry a') }
            (ShAAppl "RefEntry" [] _) ->
                    RefEntry
            u -> fromShATermError "GlobalEntry" u

instance ShATermConvertible a => ShATermConvertible (Decorated a) where
    toShATerm att0 (Decorated a b c d) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        case toShATerm att3 d of { (att4,d') ->
        addATerm (ShAAppl "Decorated" [a',b',c',d'] []) att4 }}}}
    fromShATerm att =
        case getATerm att of
            (ShAAppl "Decorated" [a,b,c,d] _) ->
                    case fromShATerm (getATermByIndex1 a att) of { a' ->
                    case fromShATerm (getATermByIndex1 b att) of { b' ->
                    case fromShATerm (getATermByIndex1 c att) of { c' ->
                    case fromShATerm (getATermByIndex1 d att) of { d' ->
                    (Decorated a' b' c' d') }}}}
            u -> fromShATermError "Decorated" u

instance ShATermConvertible G_theory where
     toShATerm att0 (G_theory lid sign sens) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 sign of { (att2,i2) ->
         case toShATerm att2 sens of { (att3,i3) ->
           addATerm (ShAAppl "G_theory" [i1,i2,i3] []) att3}}}
     fromShATerm att = 
         case aterm of
	    (ShAAppl "G_theory" [i1,i2,i3] _) ->
		let i1' = fromShATerm (getATermByIndex1 i1 att)
                    att' = getATermByIndex1 i2 att
                    att'' = getATermByIndex1 i3 att'
                    l = lookupLogic_in_LG ("ShATermConvertible G_sign:") i1' 
                in case l of
                    Logic lid -> (G_theory lid (fromShATerm att') 
                                               (fromShATerm att''))
	    u     -> fromShATermError "G_theory" u
         where
         aterm = getATerm att
