{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

remaining 'ShATermConvertible' instances for "Haskell.Logic_Haskell" based on
the generated instances in "Haskell.ATC_Haskell".
-}

module Haskell.TiATC where

import Common.ATerm.Lib
import qualified TiTypes
import qualified TiKinds
import qualified TiPropDecorate as T
import qualified TiDecorate as D
import qualified TiInstanceDB as I
import qualified PropSyntaxRec as P
import Haskell.HatParser(HsDecls(..))
import Haskell.HatAna(Sign(..))
import Haskell.ATC_Haskell()
import ATC.Set()

instance ShATermConvertible i => ShATermConvertible (I.InstEntry i) where
    toShATerm att0 (I.IE a b c) =
        case toShATerm att0 a of { (att1,a') ->
        case toShATerm att1 b of { (att2,b') ->
        case toShATerm att2 c of { (att3,c') ->
        addATerm (ShAAppl "IE" [a',b',c'] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "IE" [a,b,c] _ ->
                    case fromShATerm $ getATermByIndex1 a att of { a' ->
                    case fromShATerm $ getATermByIndex1 b att of { b' ->
                    case fromShATerm $ getATermByIndex1 c att of { c' ->
                    I.IE a' b' c' }}}
            u -> fromShATermError "TiInstanceDB.InstEntry" u
    type_of _ = "TiInstanceDB.InstEntry"

instance ShATermConvertible TiKinds.KVar where
    toShATerm att0 (TiKinds.KVar a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "KVar" [a'] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "KVar" [a] _ ->
                    case fromShATerm $ getATermByIndex1 a att of { a' ->
                    TiKinds.KVar a' }
            u -> fromShATermError  "TiKinds.KVar" u
    type_of _ = "TiKinds.KVar"

instance ShATermConvertible TiKinds.Kind where
    toShATerm att0 (TiKinds.K a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "K" [a'] []) att1 }
    toShATerm att0 (TiKinds.Kvar a) =
        case toShATerm att0 a of { (att1,a') ->
        addATerm (ShAAppl "Kvar" [a'] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "K" [a] _ ->
                    case fromShATerm $ getATermByIndex1 a att of { a' ->
                    TiKinds.K a' }
            ShAAppl "Kvar" [a] _ ->
                    case fromShATerm $ getATermByIndex1 a att of { a' ->
                    TiKinds.Kvar a' }
            u -> fromShATermError "TiKinds.Kind" u
    type_of _ = "TiKinds.Kind"

instance ShATermConvertible TiKinds.KindConstraint where
    toShATerm att0 (aa TiKinds.:=* ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "KindConstraint_" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "KindConstraint_" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    (TiKinds.:=*) aa' ab' }}
            u -> fromShATermError "TiKinds.KindConstraint" u
    type_of _ = "TiKinds.KindConstraint"

instance (ShATermConvertible i,
          ShATermConvertible t) => ShATermConvertible (TiTypes.Qual i t) where
    toShATerm att0 (aa TiTypes.:=> ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "Qual_" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Qual_" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    (TiTypes.:=>) aa' ab' }}
            u -> fromShATermError "TiTypes.Qual" u
    type_of _ = "TiTypes.Qual"

instance (ShATermConvertible v) => ShATermConvertible (TiTypes.Scheme v) where
    toShATerm att0 (TiTypes.Forall aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "Forall" [ aa',ab',ac' ] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Forall" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    TiTypes.Forall aa' ab' ac' }}}
            u -> fromShATermError "TiTypes.Scheme" u
    type_of _ = "TiTypes.Scheme"

instance ShATermConvertible i => ShATermConvertible (TiTypes.TypeInfo i) where
    toShATerm att0 TiTypes.Data =
        addATerm (ShAAppl "Data" [] []) att0
    toShATerm att0 TiTypes.Newtype =
        addATerm (ShAAppl "Newtype" [] []) att0
    toShATerm att0 (TiTypes.Class aa ab ac ad) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        case toShATerm att3 ad of { (att4,ad') ->
        addATerm (ShAAppl "Class" [ aa',ab',ac',ad' ] []) att4 }}}}
    toShATerm att0 (TiTypes.Synonym aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "Synonym" [ aa',ab' ] []) att2 }}
    toShATerm att0 TiTypes.Tyvar =
        addATerm (ShAAppl "Tyvar" [] []) att0
    fromShATerm att =
        case getATerm att of
            ShAAppl "Data" [ ] _ ->
                    TiTypes.Data
            ShAAppl "Newtype" [ ] _ ->
                    TiTypes.Newtype
            ShAAppl "Class" [ aa,ab,ac,ad ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    case fromShATerm $ getATermByIndex1 ad att of { ad' ->
                    TiTypes.Class aa' ab' ac' ad' }}}}
            ShAAppl "Synonym" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    TiTypes.Synonym aa' ab' }}
            ShAAppl "Tyvar" [ ] _ ->
                    TiTypes.Tyvar
            u -> fromShATermError "TiTypes.TypeInfo" u
    type_of _ = "TiTypes.TypeInfo"

instance (ShATermConvertible x, ShATermConvertible t)
    => ShATermConvertible (TiTypes.Typing x t) where
    toShATerm att0 (aa TiTypes.:>: ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "Typing_" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Typing_" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    (TiTypes.:>:) aa' ab' }}
            u -> fromShATermError "TiTypes.Typing" u
    type_of _ = "TiTypes.Typing"

instance (ShATermConvertible i) => ShATermConvertible (TiTypes.Subst i) where
    toShATerm att0 (TiTypes.S aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "S" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "S" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    TiTypes.S aa' }
            u -> fromShATermError "TiTypes.Subst" u
    type_of _ = "TiTypes.Subst"

instance (ShATermConvertible i) => ShATermConvertible (P.HsDeclI i) where
    toShATerm att0 (P.Dec aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Dec" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "Dec" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    P.Dec aa' }
            u -> fromShATermError "PropSyntaxRec.HsDeclI" u
    type_of _ = "PropSyntaxRec.HsDeclI"

instance (ShATermConvertible i) => ShATermConvertible (P.AssertionI i) where
    toShATerm att0 (P.PA aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "PA" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "PA" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    P.PA aa' }
            u -> fromShATermError "PropSyntaxRec.AssertionI" u
    type_of _ = "PropSyntaxRec.AssertionI"

instance (ShATermConvertible i) => ShATermConvertible (P.PredicateI i) where
    toShATerm att0 (P.PP aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "PP" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "PP" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    P.PP aa' }
            u -> fromShATermError "PropSyntaxRec.PredicateI" u
    type_of _ = "PropSyntaxRec.PredicateI"

instance (ShATermConvertible i) => ShATermConvertible (P.HsExpI i) where
    toShATerm att0 (P.Exp aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Exp" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "Exp" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    P.Exp aa' }
            u -> fromShATermError "PropSyntaxRec.HsExpI" u
    type_of _ = "PropSyntaxRec.HsExpI"

instance (ShATermConvertible i) => ShATermConvertible (D.TiPat i) where
    toShATerm att0 (D.Pat aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Pat" [ aa' ] []) att1 }
    toShATerm att0 (D.TiPApp aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "TiPApp" [ aa',ab' ] []) att2 }}
    toShATerm att0 (D.TiPSpec aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "TiPSpec" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (D.TiPTyped aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "TiPTyped" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Pat" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    D.Pat aa' }
            ShAAppl "TiPApp" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    D.TiPApp aa' ab' }}
            ShAAppl "TiPSpec" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    D.TiPSpec aa' ab' ac' }}}
            ShAAppl "TiPTyped" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    D.TiPTyped aa' ab' }}
            u -> fromShATermError "TiDecorate.TiPat" u
    type_of _ = "TiDecorate.TiPat"

instance (ShATermConvertible i) => ShATermConvertible (T.TiExp i) where
    toShATerm att0 (T.Exp aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Exp" [ aa' ] []) att1 }
    toShATerm att0 (T.TiSpec aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "TiSpec" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (T.TiTyped aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "TiTyped" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Exp" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    T.Exp aa' }
            ShAAppl "TiSpec" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    T.TiSpec aa' ab' ac' }}}
            ShAAppl "TiTyped" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    T.TiTyped aa' ab' }}
            u -> fromShATermError "TiPropDecorate.TiExp" u
    type_of _ = "TiPropDecorate.TiExp"

instance (ShATermConvertible i) => ShATermConvertible (T.OTiAssertion i) where
    toShATerm att0 (T.OA aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "OA" [ aa',ab',ac' ] []) att3 }}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "OA" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    T.OA aa' ab' ac' }}}
            u -> fromShATermError "TiPropDecorate.OTiAssertion" u
    type_of _ = "TiPropDecorate.OTiAssertion"

instance (ShATermConvertible i) => ShATermConvertible (T.TiPredicate i) where
    toShATerm att0 (T.PP aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "PP" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "PP" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    T.PP aa' }
            u -> fromShATermError "TiPropDecorate.TiPredicate" u
    type_of _ = "TiPropDecorate.TiPredicate"

instance (ShATermConvertible i) => ShATermConvertible (T.TiAssertion i) where
    toShATerm att0 (T.PA aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "PA" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "PA" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    T.PA aa' }
            u -> fromShATermError "TiPropDecorate.TiAssertion" u
    type_of _ = "TiPropDecorate.TiAssertion"

instance (ShATermConvertible i) => ShATermConvertible (T.TiDecl i) where
    toShATerm att0 (T.Dec aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Dec" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "Dec" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    T.Dec aa' }
            u -> fromShATermError "TiPropDecorate.TiDecl" u
    type_of _ = "TiPropDecorate.TiDecl"

instance (ShATermConvertible i) => ShATermConvertible (T.TiDecls i) where
    toShATerm att0 (T.Decs aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "Decs" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Decs" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    T.Decs aa' ab' }}
            u -> fromShATermError "TiPropDecorate.TiDecls" u
    type_of _ = "TiPropDecorate.TiDecls"

instance ShATermConvertible HsDecls where
    toShATerm att0 (HsDecls aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "HsDecls" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "HsDecls" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    HsDecls aa' }
            u -> fromShATermError "Haskell.HsDecls" u
    type_of _ = "Haskell.HsDecls"

instance ShATermConvertible Sign where
    toShATerm att0 (Sign aa ab ac ad ae) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        case toShATerm att3 ad of { (att4,ad') ->
        case toShATerm att4 ae of { (att5,ae') ->
        addATerm (ShAAppl "Sign" [ aa',ab',ac',ad',ae' ] []) att5 }}}}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Sign" [ aa,ab,ac,ad,ae ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    case fromShATerm $ getATermByIndex1 ad att of { ad' ->
                    case fromShATerm $ getATermByIndex1 ae att of { ae' ->
                    Sign aa' ab' ac' ad' ae' }}}}}
            u -> fromShATermError "Haskell.Sign" u
    type_of _ = "Haskell.Sign"
