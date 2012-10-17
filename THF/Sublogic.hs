{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Sublogics for THF
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <j.von_schroeder@dfki.de>
Stability   :  experimental
Portability :  non-portable (via Logic.Logic)

Sublogics for THF
-}

module THF.Sublogic where

import THF.As
import Logic.Logic hiding (join)

data THFCoreSl = THF | THFP | THF0 deriving (Ord,Show,Eq)

data THFSl = THFSl {
 core :: THFCoreSl,
 ext_ShortTypes :: Bool } deriving (Ord,Eq)

{-
The ShortTypes extension allows for unnamed unique types:

 %With ShortTypes
 thf(a_type,type,a : ($tType,$tType))
 thf(b_type,type,b : $tType > a)
 thf(test_const_type,type, test : b)
 %Without ShortTypes
 thf(a1_type,type,a1 : $tType)
 thf(a2_type,type,a2 : $tType)
 thf(b1_type,type,b1 : $tType)
 thf(test_const_type,type, test : b1 > (a1,a2))

Note: Types made of other, non-atomic types are not allowed i.e. the following
is still not a legal type-definition:

 thf(a_type,type, a: $tType > $tType)
 thf(b_type,type, b: a > $tType)

Without this extension $tType may only be used to declare
atomic types i.e.

 thf(a_type,type, a : $tType)

-}

instance Show THFSl where
 show sl = (show $ core sl) ++
           (if ext_ShortTypes sl
            then "_ST" else "")

joinCoreSl :: THFCoreSl -> THFCoreSl -> THFCoreSl
joinCoreSl THF _ = THF
joinCoreSl _ THF = THF
joinCoreSl THFP _ = THFP
joinCoreSl _ THFP = THFP
joinCoreSl _ _ = THF0

join :: THFSl -> THFSl -> THFSl
join sl1 sl2 = THFSl {
 core = joinCoreSl (core sl1) (core sl2),
 ext_ShortTypes = (ext_ShortTypes sl1) ||
                  (ext_ShortTypes sl2) }
tHF0,tHFP,tHF :: THFSl
tHF0 = THFSl { core = THF0, ext_ShortTypes = False }
tHFP = THFSl { core = THFP, ext_ShortTypes = False }
tHF  = THFSl { core = THF , ext_ShortTypes = False }

tHF0_ST,tHFP_ST,tHF_ST :: THFSl
tHF0_ST = tHF0 { ext_ShortTypes = True }
tHFP_ST = tHFP { ext_ShortTypes = True }
tHF_ST  = tHF  { ext_ShortTypes = True }

sublogics_all :: [THFSl]
sublogics_all = [tHF0, tHF0_ST,
                 tHFP, tHFP_ST,
                 tHF, tHF_ST]

instance MinSublogic THFSl THFFormula where
 minSublogic f = case f of
   TF_THF_Logic_Formula f' -> join tHF0 $ minSublogic f'
   TF_THF_Sequent s -> join tHF $ minSublogic s
   T0F_THF_Typed_Const tc -> join tHF0 $ minSublogic tc -- fixme: Not in THF?

instance MinSublogic THFSl THFLogicFormula where
 minSublogic f = case f of
   TLF_THF_Binary_Formula b -> join tHF0 $ minSublogic b
   TLF_THF_Unitary_Formula u -> join tHF0 $ minSublogic u
   TLF_THF_Type_Formula tf -> join tHF $ minSublogic tf
   TLF_THF_Sub_Type st -> join tHF $ minSublogic st

instance MinSublogic THFSl THFSequent where
 minSublogic _ = tHF

instance MinSublogic THFSl THFTypedConst where
 minSublogic c = case c of
   T0TC_Typed_Const _ tp -> minSublogic tp
   T0TC_THF_TypedConst_Par tp -> minSublogic tp

instance MinSublogic THFSl THFBinaryFormula where
 minSublogic b = case b of
   TBF_THF_Binary_Pair f1 c f2 -> join tHF0 (join (minSublogic f1)
    (join (minSublogic c) (minSublogic f2)))
   TBF_THF_Binary_Tuple bt -> join tHF0 $ minSublogic bt
   TBF_THF_Binary_Type bt -> join tHF $ minSublogic bt

instance MinSublogic THFSl THFUnitaryFormula where
 minSublogic u = case u of
   TUF_THF_Quantified_Formula qf -> join tHF0 $ minSublogic qf
   TUF_THF_Unary_Formula uc f -> join tHF0 $ join (minSublogic uc)
                                                  (minSublogic f)
   TUF_THF_Atom a -> join tHF0 $ minSublogic a
   TUF_THF_Tuple uts -> foldr join tHFP (map minSublogic uts)
   TUF_THF_Conditional f1 f2 f3 -> join tHF $ join (minSublogic f1)
                                 (join (minSublogic f2) (minSublogic f3))
   TUF_THF_Logic_Formula_Par f -> join tHF0 $ minSublogic f
   T0UF_THF_Abstraction vs u' -> join (foldr join tHF0
                                      (map minSublogic vs)) $
                                     minSublogic u'

instance MinSublogic THFSl THFTypeFormula where
 minSublogic tf = case tf of
   TTF_THF_Type_Formula tf' tp -> join tHF $ join (minSublogic tf')
                                                  (minSublogic tp)
   TTF_THF_Typed_Const _ tp -> join tHF $ minSublogic tp

instance MinSublogic THFSl THFSubType where
 minSublogic _ = tHF

instance MinSublogic THFSl THFPairConnective where
 minSublogic _ = tHF0

instance MinSublogic THFSl THFBinaryTuple where
 minSublogic bt = case bt of
   TBT_THF_Or_Formula ufs -> foldr join tHF0 $ map minSublogic ufs
   TBT_THF_And_Formula ufs -> foldr join tHF0 $ map minSublogic ufs
   TBT_THF_Apply_Formula ufs -> foldr join tHF0 $ map minSublogic ufs

instance MinSublogic THFSl THFBinaryType where
 minSublogic bt = case bt of
   TBT_THF_Mapping_Type uts ->
    join (if hasTType uts then tHF0_ST else tHF0) $
     foldr join tHF0
      (map minSublogic uts)
   TBT_THF_Xprod_Type uts ->
    foldr join (if hasTType uts then tHFP_ST else tHFP)
               (map minSublogic uts)
   TBT_THF_Union_Type uts ->
    foldr join (if hasTType uts then tHF_ST else tHF)
     (map minSublogic uts)
   T0BT_THF_Binary_Type_Par bt' -> minSublogic bt'
  where hasTType uts = foldr (&&) False $
         map (\ut -> case ut of
                T0UT_THF_Binary_Type_Par bt' -> hasTTypeB bt'
                T0UT_Defined_Type DT_tType -> True
                _ -> False) uts
        hasTTypeB bt' =
          case bt' of
           TBT_THF_Mapping_Type uts' -> hasTType uts'
           TBT_THF_Xprod_Type uts' -> hasTType uts'
           TBT_THF_Union_Type uts' -> hasTType uts'
           T0BT_THF_Binary_Type_Par bt'' -> hasTTypeB bt''
  --fixme: maybe we need to check TUT_THF_Unitary_Formula for ShortTypes
  --fixme: how does this differ from THF?

instance MinSublogic THFSl THFQuantifiedFormula where
 minSublogic qf = case qf of
   TQF_THF_Quantified_Formula qf' vs u -> join (minSublogic u) $
                                         join (minSublogic qf')
                                          (foldr join tHF0
                                            (map minSublogic vs))
   T0QF_THF_Quantified_Var qf' vs u -> join (minSublogic u) $
                                         join (minSublogic qf')
                                          (foldr join tHF0
                                            (map minSublogic vs))
 --note: T0QF_THF_Quantified_Var in THF0 is pretty much the same as
 --      TQF_THF_Quantified_Formula in THF (cf. As.hs 190 ff.)
 --      Maybe we should merge the two constructors?
   T0QF_THF_Quantified_Novar qf' u -> join (minSublogic qf')
                                           (minSublogic u)
 -- fixme: not in THF?!?

instance MinSublogic THFSl THFUnaryConnective where
 minSublogic uc = case uc of
   Negation -> tHF0
   PiForAll -> tHF
   SigmaExists -> tHF

instance MinSublogic THFSl THFAtom where
 minSublogic a = case a of
   TA_Term _ -> tHF
   TA_THF_Conn_Term conn ->
     case conn of
       TCT_THF_Pair_Connective pc -> join tHF $ minSublogic pc
       TCT_Assoc_Connective _ -> tHF0
       TCT_THF_Unary_Connective uc -> join tHF0 $ minSublogic uc
       T0CT_THF_Quantifier qf -> join tHF0 $ minSublogic qf
   TA_Defined_Type df -> join tHF $ minSublogic df
   TA_Defined_Plain_Formula _ -> tHF
   TA_System_Type _ -> tHF
   TA_System_Atomic_Formula _ -> tHF
   T0A_Constant _ -> tHF0
   T0A_Defined_Constant _ -> tHF0
   T0A_System_Constant _ -> tHF0
   T0A_Variable _ -> tHF0
 -- fixme: how do these in THF0 differ from THF?

instance MinSublogic THFSl THFVariable where
 minSublogic v = case v of
   TV_THF_Typed_Variable _ t -> join tHF0 $ minSublogic t
   _ -> tHF0

instance MinSublogic THFSl THFQuantifier where
 minSublogic qf = case qf of
  T0Q_PiForAll -> tHF0
  T0Q_SigmaExists -> tHF0
  _ -> tHF

instance MinSublogic THFSl Quantifier where
 minSublogic _ = tHF0

instance MinSublogic THFSl THFTopLevelType where
 minSublogic tp = case tp of
   TTLT_THF_Logic_Formula f -> join tHF $ minSublogic f
   --fixme: maybe we need to check for ShortTypes extension?
   T0TLT_Constant _ -> tHF0
   T0TLT_Variable _ -> tHF0
   T0TLT_Defined_Type df -> join tHF0 $ minSublogic df
   T0TLT_System_Type _ -> tHF0
   T0TLT_THF_Binary_Type bt -> join tHF0 $ minSublogic bt
 --fixme: how do all these THF0 types differ from THF?

instance MinSublogic THFSl THFTypeableFormula where
 minSublogic tf = case tf of
   TTyF_THF_Atom a -> join tHF $ minSublogic a
   TTyF_THF_Tuple ts -> foldr join tHFP $ map minSublogic ts
   TTyF_THF_Logic_Formula f -> join tHF $ minSublogic f

instance MinSublogic THFSl DefinedType where
 minSublogic df = case df of
   DT_oType -> tHF0
   DT_o -> tHF0
   DT_iType -> tHF0
   DT_i -> tHF0
   DT_tType -> tHF0
   DT_real -> tHF
   DT_rat -> tHF
   DT_int -> tHF

instance MinSublogic THFSl THFUnitaryType where
 minSublogic ut = case ut of
   TUT_THF_Unitary_Formula f -> join tHF $ minSublogic f
   T0UT_Constant _ -> tHF0
   T0UT_Variable _ -> tHF0
   T0UT_Defined_Type df -> join tHF0 $ minSublogic df
   T0UT_System_Type _ -> tHF0
   T0UT_THF_Binary_Type_Par bt -> join tHF0 $ minSublogic bt
 --fixme: how do all these THF0 types differ from THF?
