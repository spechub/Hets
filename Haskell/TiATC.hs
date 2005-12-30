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
import qualified TiPropDecorate
import qualified TiDecorate
import qualified TiInstanceDB
import qualified PropSyntaxRec
import Haskell.HatParser(HsDecls(..))
import Haskell.HatAna(Sign(..))
import Haskell.ATC_Haskell()
import ATC.Set()
import Common.DynamicUtils

_tc_TiInstanceDB_InstEntryTc :: TyCon
_tc_TiInstanceDB_InstEntryTc = mkTyCon "TiInstanceDB.InstEntry"
instance (Typeable a) => Typeable (TiInstanceDB.InstEntry a) where
    typeOf x = mkTyConApp _tc_TiInstanceDB_InstEntryTc [typeOf (geta x)]
      where
        geta :: TiInstanceDB.InstEntry a -> a
        geta = undefined

instance ShATermConvertible i
    => ShATermConvertible (TiInstanceDB.InstEntry i) where
    toShATerm att0 (TiInstanceDB.IE a b c) =
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
                    TiInstanceDB.IE a' b' c' }}}
            u -> fromShATermError "TiInstanceDB.InstEntry" u

_tc_TiKinds_KVarTc :: TyCon
_tc_TiKinds_KVarTc = mkTyCon "TiKinds.KVar"
instance Typeable TiKinds.KVar where
    typeOf _ = mkTyConApp _tc_TiKinds_KVarTc []

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

_tc_TiKinds_KindTc :: TyCon
_tc_TiKinds_KindTc = mkTyCon "TiKinds.Kind"
instance Typeable TiKinds.Kind where
    typeOf _ = mkTyConApp _tc_TiKinds_KindTc []

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

_tc_TiKinds_KindConstraintTc :: TyCon
_tc_TiKinds_KindConstraintTc = mkTyCon "TiKinds.KindConstraint"
instance Typeable TiKinds.KindConstraint where
    typeOf _ = mkTyConApp _tc_TiKinds_KindConstraintTc []

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

_tc_TiTypes_QualTc :: TyCon
_tc_TiTypes_QualTc = mkTyCon "TiTypes.Qual"
instance (Typeable a,
          Typeable b) => Typeable (TiTypes.Qual a b) where
    typeOf x = mkTyConApp _tc_TiTypes_QualTc [typeOf (geta x),typeOf (getb x)]
      where
        geta :: TiTypes.Qual a b -> a
        geta = undefined
        getb :: TiTypes.Qual a b -> b
        getb = undefined

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

_tc_TiTypes_SchemeTc :: TyCon
_tc_TiTypes_SchemeTc = mkTyCon "TiTypes.Scheme"
instance (Typeable a) => Typeable (TiTypes.Scheme a) where
    typeOf x = mkTyConApp _tc_TiTypes_SchemeTc [typeOf (geta x)]
      where
        geta :: TiTypes.Scheme a -> a
        geta = undefined

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

_tc_TiTypes_TypeInfoTc :: TyCon
_tc_TiTypes_TypeInfoTc = mkTyCon "TiTypes.TypeInfo"
instance (Typeable a) => Typeable (TiTypes.TypeInfo a) where
    typeOf x = mkTyConApp _tc_TiTypes_TypeInfoTc [typeOf (geta x)]
      where
        geta :: TiTypes.TypeInfo a -> a
        geta = undefined

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

_tc_TiTypes_TypingTc :: TyCon
_tc_TiTypes_TypingTc = mkTyCon "TiTypes.Typing"
instance (Typeable a,
          Typeable b) => Typeable (TiTypes.Typing a b) where
    typeOf x = mkTyConApp _tc_TiTypes_TypingTc
               [typeOf (geta x),typeOf (getb x)]
      where
        geta :: TiTypes.Typing a b -> a
        geta = undefined
        getb :: TiTypes.Typing a b -> b
        getb = undefined

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

_tc_TiTypes_SubstTc :: TyCon
_tc_TiTypes_SubstTc = mkTyCon "TiTypes.Subst"
instance (Typeable a) => Typeable (TiTypes.Subst a) where
    typeOf x = mkTyConApp _tc_TiTypes_SubstTc [typeOf (geta x)]
      where
        geta :: TiTypes.Subst a -> a
        geta = undefined

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

_tc_PropSyntaxRec_HsDeclITc :: TyCon
_tc_PropSyntaxRec_HsDeclITc = mkTyCon "PropSyntaxRec.HsDeclI"
instance (Typeable a) => Typeable (PropSyntaxRec.HsDeclI a) where
    typeOf x = mkTyConApp _tc_PropSyntaxRec_HsDeclITc [typeOf (geta x)]
      where
        geta :: PropSyntaxRec.HsDeclI a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (PropSyntaxRec.HsDeclI i) where
    toShATerm att0 (PropSyntaxRec.Dec aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Dec" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "Dec" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    PropSyntaxRec.Dec aa' }
            u -> fromShATermError "PropSyntaxRec.HsDeclI" u

_tc_PropSyntaxRec_AssertionITc :: TyCon
_tc_PropSyntaxRec_AssertionITc = mkTyCon "PropSyntaxRec.AssertionI"
instance (Typeable a) => Typeable (PropSyntaxRec.AssertionI a) where
    typeOf x = mkTyConApp _tc_PropSyntaxRec_AssertionITc [typeOf (geta x)]
      where
        geta :: PropSyntaxRec.AssertionI a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (PropSyntaxRec.AssertionI i) where
    toShATerm att0 (PropSyntaxRec.PA aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "PA" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "PA" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    PropSyntaxRec.PA aa' }
            u -> fromShATermError "PropSyntaxRec.AssertionI" u

_tc_PropSyntaxRec_PredicateITc :: TyCon
_tc_PropSyntaxRec_PredicateITc = mkTyCon "PropSyntaxRec.PredicateI"
instance (Typeable a) => Typeable (PropSyntaxRec.PredicateI a) where
    typeOf x = mkTyConApp _tc_PropSyntaxRec_PredicateITc [typeOf (geta x)]
      where
        geta :: PropSyntaxRec.PredicateI a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (PropSyntaxRec.PredicateI i) where
    toShATerm att0 (PropSyntaxRec.PP aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "PP" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "PP" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    PropSyntaxRec.PP aa' }
            u -> fromShATermError "PropSyntaxRec.PredicateI" u

_tc_PropSyntaxRec_HsExpITc :: TyCon
_tc_PropSyntaxRec_HsExpITc = mkTyCon "PropSyntaxRec.HsExpI"
instance (Typeable a) => Typeable (PropSyntaxRec.HsExpI a) where
    typeOf x = mkTyConApp _tc_PropSyntaxRec_HsExpITc [typeOf (geta x)]
      where
        geta :: PropSyntaxRec.HsExpI a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (PropSyntaxRec.HsExpI i) where
    toShATerm att0 (PropSyntaxRec.Exp aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Exp" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "Exp" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    PropSyntaxRec.Exp aa' }
            u -> fromShATermError "PropSyntaxRec.HsExpI" u

_tc_TiDecorate_TiPatTc :: TyCon
_tc_TiDecorate_TiPatTc = mkTyCon "TiDecorate.TiPat"
instance (Typeable a) => Typeable (TiDecorate.TiPat a) where
    typeOf x = mkTyConApp _tc_TiDecorate_TiPatTc [typeOf (geta x)]
      where
        geta :: TiDecorate.TiPat a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (TiDecorate.TiPat i) where
    toShATerm att0 (TiDecorate.Pat aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Pat" [ aa' ] []) att1 }
    toShATerm att0 (TiDecorate.TiPApp aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "TiPApp" [ aa',ab' ] []) att2 }}
    toShATerm att0 (TiDecorate.TiPSpec aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "TiPSpec" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (TiDecorate.TiPTyped aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "TiPTyped" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Pat" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    TiDecorate.Pat aa' }
            ShAAppl "TiPApp" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    TiDecorate.TiPApp aa' ab' }}
            ShAAppl "TiPSpec" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    TiDecorate.TiPSpec aa' ab' ac' }}}
            ShAAppl "TiPTyped" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    TiDecorate.TiPTyped aa' ab' }}
            u -> fromShATermError "TiDecorate.TiPat" u

_tc_TiPropDecorate_TiExpTc :: TyCon
_tc_TiPropDecorate_TiExpTc = mkTyCon "TiPropDecorate.TiExp"
instance (Typeable a) => Typeable (TiPropDecorate.TiExp a) where
    typeOf x = mkTyConApp _tc_TiPropDecorate_TiExpTc [typeOf (geta x)]
      where
        geta :: TiPropDecorate.TiExp a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (TiPropDecorate.TiExp i) where
    toShATerm att0 (TiPropDecorate.Exp aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Exp" [ aa' ] []) att1 }
    toShATerm att0 (TiPropDecorate.TiSpec aa ab ac) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        addATerm (ShAAppl "TiSpec" [ aa',ab',ac' ] []) att3 }}}
    toShATerm att0 (TiPropDecorate.TiTyped aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "TiTyped" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Exp" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    TiPropDecorate.Exp aa' }
            ShAAppl "TiSpec" [ aa,ab,ac ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    TiPropDecorate.TiSpec aa' ab' ac' }}}
            ShAAppl "TiTyped" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    TiPropDecorate.TiTyped aa' ab' }}
            u -> fromShATermError "TiPropDecorate.TiExp" u

_tc_TiPropDecorate_OTiAssertionTc :: TyCon
_tc_TiPropDecorate_OTiAssertionTc = mkTyCon "TiPropDecorate.OTiAssertion"
instance (Typeable a) => Typeable (TiPropDecorate.OTiAssertion a) where
    typeOf x = mkTyConApp _tc_TiPropDecorate_OTiAssertionTc [typeOf (geta x)]
      where
        geta :: TiPropDecorate.OTiAssertion a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (TiPropDecorate.OTiAssertion i) where
    toShATerm att0 (TiPropDecorate.OA aa ab ac) =
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
                    TiPropDecorate.OA aa' ab' ac' }}}
            u -> fromShATermError "TiPropDecorate.OTiAssertion" u

_tc_TiPropDecorate_TiPredicateTc :: TyCon
_tc_TiPropDecorate_TiPredicateTc = mkTyCon "TiPropDecorate.TiPredicate"
instance (Typeable a) => Typeable (TiPropDecorate.TiPredicate a) where
    typeOf x = mkTyConApp _tc_TiPropDecorate_TiPredicateTc [typeOf (geta x)]
      where
        geta :: TiPropDecorate.TiPredicate a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (TiPropDecorate.TiPredicate i) where
    toShATerm att0 (TiPropDecorate.PP aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "PP" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "PP" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    TiPropDecorate.PP aa' }
            u -> fromShATermError "TiPropDecorate.TiPredicate" u

_tc_TiPropDecorate_TiAssertionTc :: TyCon
_tc_TiPropDecorate_TiAssertionTc = mkTyCon "TiPropDecorate.TiAssertion"
instance (Typeable a) => Typeable (TiPropDecorate.TiAssertion a) where
    typeOf x = mkTyConApp _tc_TiPropDecorate_TiAssertionTc [typeOf (geta x)]
      where
        geta :: TiPropDecorate.TiAssertion a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (TiPropDecorate.TiAssertion i) where
    toShATerm att0 (TiPropDecorate.PA aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "PA" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "PA" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    TiPropDecorate.PA aa' }
            u -> fromShATermError "TiPropDecorate.TiAssertion" u

_tc_TiPropDecorate_TiDeclTc :: TyCon
_tc_TiPropDecorate_TiDeclTc = mkTyCon "TiPropDecorate.TiDecl"
instance (Typeable a) => Typeable (TiPropDecorate.TiDecl a) where
    typeOf x = mkTyConApp _tc_TiPropDecorate_TiDeclTc [typeOf (geta x)]
      where
        geta :: TiPropDecorate.TiDecl a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (TiPropDecorate.TiDecl i) where
    toShATerm att0 (TiPropDecorate.Dec aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Dec" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "Dec" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    TiPropDecorate.Dec aa' }
            u -> fromShATermError "TiPropDecorate.TiDecl" u

_tc_TiPropDecorate_TiDeclsTc :: TyCon
_tc_TiPropDecorate_TiDeclsTc = mkTyCon "TiPropDecorate.TiDecls"
instance (Typeable a) => Typeable (TiPropDecorate.TiDecls a) where
    typeOf x = mkTyConApp _tc_TiPropDecorate_TiDeclsTc [typeOf (geta x)]
      where
        geta :: TiPropDecorate.TiDecls a -> a
        geta = undefined

instance (ShATermConvertible i)
    => ShATermConvertible (TiPropDecorate.TiDecls i) where
    toShATerm att0 (TiPropDecorate.Decs aa ab) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        addATerm (ShAAppl "Decs" [ aa',ab' ] []) att2 }}
    fromShATerm att =
        case getATerm att of
            ShAAppl "Decs" [ aa,ab ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    TiPropDecorate.Decs aa' ab' }}
            u -> fromShATermError "TiPropDecorate.TiDecls" u

hsDeclsTc :: TyCon
hsDeclsTc = mkTyCon "Haskell.HatParser.HsDecls"

instance Typeable HsDecls where
    typeOf _ = mkTyConApp hsDeclsTc []

tyconSign :: TyCon
tyconSign = mkTyCon "Haskell.HatAna.Sign"

instance Typeable Sign where
  typeOf _ = mkTyConApp tyconSign []

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
