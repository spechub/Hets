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
import THF.Cons
import Logic.Logic hiding (join)

data THFSl = THF | THFP | THF0 deriving (Ord,Show,Eq)

join :: THFSl -> THFSl -> THFSl
join THF _ = THF
join _ THF = THF
join THFP _ = THFP
join _ THFP = THFP
join _ _ = THF0

sublogics_all :: [THFSl]
sublogics_all = [THF,THFP,THF0]

instance MinSublogic THFSl SentenceTHF where
 minSublogic s = minSublogic $ senFormula s

instance MinSublogic THFSl THFFormula where
 minSublogic f = case f of
   TF_THF_Logic_Formula f' -> join THF0 $ minSublogic f'
   TF_THF_Sequent s -> join THF0 $ minSublogic s
   T0F_THF_Typed_Const tc -> join THF0 $ minSublogic tc -- fixme: Not in THF?

instance MinSublogic THFSl THFLogicFormula where
 minSublogic f = case f of
   TLF_THF_Binary_Formula b -> join THF0 $ minSublogic b
   TLF_THF_Unitary_Formula u -> join THF0 $ minSublogic u
   TLF_THF_Type_Formula tf -> join THF $ minSublogic tf
   TLF_THF_Sub_Type st -> join THF $ minSublogic st

instance MinSublogic THFSl THFSequent where
 minSublogic _ = THF

instance MinSublogic THFSl THFTypedConst where
 minSublogic c = case c of
   T0TC_Typed_Const _ tp -> minSublogic tp
   T0TC_THF_TypedConst_Par tp -> minSublogic tp

instance MinSublogic THFSl THFBinaryFormula where
 minSublogic b = case b of
   TBF_THF_Binary_Pair f1 c f2 -> join THF0 (join (minSublogic f1)
    (join (minSublogic c) (minSublogic f2)))
   TBF_THF_Binary_Tuple bt -> join THF0 $ minSublogic bt
   TBF_THF_Binary_Type bt -> join THF $ minSublogic bt

instance MinSublogic THFSl THFUnitaryFormula where
 minSublogic u = case u of
   TUF_THF_Quantified_Formula qf -> join THF0 $ minSublogic qf
   TUF_THF_Unary_Formula uc f -> join THF0 $ join (minSublogic uc)
                                                  (minSublogic f)
   TUF_THF_Atom a -> join THF0 $ minSublogic a
   TUF_THF_Tuple uts -> foldr join THFP (map minSublogic uts)
   TUF_THF_Conditional f1 f2 f3 -> join THF $ join (minSublogic f1)
                                 (join (minSublogic f2) (minSublogic f3))
   TUF_THF_Logic_Formula_Par f -> join THF0 $ minSublogic f
   T0UF_THF_Abstraction vs u' -> join (foldr join THF0
                                      (map minSublogic vs)) $
                                     minSublogic u'

instance MinSublogic THFSl THFTypeFormula where
 minSublogic tf = case tf of
   TTF_THF_Type_Formula tf' tp -> join THF $ join (minSublogic tf')
                                                  (minSublogic tp)
   TTF_THF_Typed_Const _ tp -> join THF $ minSublogic tp

instance MinSublogic THFSl THFSubType where
 minSublogic _ = THF

instance MinSublogic THFSl THFPairConnective where
 minSublogic _ = THF0

instance MinSublogic THFSl THFBinaryTuple where
 minSublogic bt = case bt of
   TBT_THF_Or_Formula ufs -> foldr join THF0 $ map minSublogic ufs
   TBT_THF_And_Formula ufs -> foldr join THF0 $ map minSublogic ufs
   TBT_THF_Apply_Formula ufs -> foldr join THF0 $ map minSublogic ufs

instance MinSublogic THFSl THFBinaryType where
 minSublogic bt = case bt of
   TBT_THF_Mapping_Type uts -> join THF0 $ foldr join THF0
                                            (map minSublogic uts)
   TBT_THF_Xprod_Type ts -> foldr join THFP (map minSublogic ts)
   TBT_THF_Union_Type uts -> join THF $ foldr join THF
                                         (map minSublogic uts)
   T0BT_THF_Binary_Type_Par bt' -> join THF0 $ minSublogic bt'
  --fixme: how does this differ from THF?

instance MinSublogic THFSl THFQuantifiedFormula where
 minSublogic qf = case qf of
   TQF_THF_Quantified_Formula qf' vs u -> join (minSublogic u) $
                                         join (minSublogic qf')
                                          (foldr join THF0
                                            (map minSublogic vs))
   T0QF_THF_Quantified_Var qf' vs u -> join (minSublogic u) $
                                         join (minSublogic qf')
                                          (foldr join THF0
                                            (map minSublogic vs))
 --note: T0QF_THF_Quantified_Var in THF0 is pretty much the same as 
 --      TQF_THF_Quantified_Formula in THF (cf. As.hs 190 ff.)
 --      Maybe we should merge the two constructors?
   T0QF_THF_Quantified_Novar qf' u -> join (minSublogic qf')
                                           (minSublogic u)
 -- fixme: not in THF?!?

instance MinSublogic THFSl THFUnaryConnective where
 minSublogic uc = case uc of
   Negation -> THF0
   PiForAll -> THF
   SigmaExists -> THF

instance MinSublogic THFSl THFAtom where
 minSublogic a = case a of
   TA_Term _ -> THF
   TA_THF_Conn_Term conn ->
     case conn of
       TCT_THF_Pair_Connective pc -> join THF $ minSublogic pc
       TCT_Assoc_Connective _ -> THF0
       TCT_THF_Unary_Connective uc -> join THF0 $ minSublogic uc
       T0CT_THF_Quantifier qf -> join THF0 $ minSublogic qf
   TA_Defined_Type df -> join THF $ minSublogic df
   TA_Defined_Plain_Formula _ -> THF
   TA_System_Type _ -> THF
   TA_System_Atomic_Formula _ -> THF
   T0A_Constant _ -> THF0
   T0A_Defined_Constant _ -> THF0
   T0A_System_Constant _ -> THF0
   T0A_Variable _ -> THF0
 -- fixme: how do these in THF0 differ from THF?

instance MinSublogic THFSl THFVariable where
 minSublogic v = case v of
   TV_THF_Typed_Variable _ t -> join THF0 $ minSublogic t
   _ -> THF0

instance MinSublogic THFSl THFQuantifier where
 minSublogic qf = case qf of
  T0Q_PiForAll -> THF0
  T0Q_SigmaExists -> THF0
  _ -> THF

instance MinSublogic THFSl Quantifier where
 minSublogic _ = THF0

instance MinSublogic THFSl THFTopLevelType where
 minSublogic tp = case tp of
   TTLT_THF_Logic_Formula f -> join THF $ minSublogic f
   T0TLT_Constant _ -> THF0
   T0TLT_Variable _ -> THF0
   T0TLT_Defined_Type df -> join THF0 $ minSublogic df
   T0TLT_System_Type _ -> THF0
   T0TLT_THF_Binary_Type bt -> join THF0 $ minSublogic bt
 --fixme: how do all these THF0 types differ from THF?

instance MinSublogic THFSl THFTypeableFormula where
 minSublogic tf = case tf of
   TTyF_THF_Atom a -> join THF $ minSublogic a
   TTyF_THF_Tuple ts -> foldr join THFP $ map minSublogic ts
   TTyF_THF_Logic_Formula f -> join THF $ minSublogic f

instance MinSublogic THFSl DefinedType where
 minSublogic df = case df of
   DT_oType -> THF0
   DT_o -> THF0
   DT_iType -> THF0
   DT_i -> THF0
   DT_tType -> THF0
   DT_real -> THF
   DT_rat -> THF
   DT_int -> THF

instance MinSublogic THFSl THFUnitaryType where
 minSublogic ut = case ut of
   TUT_THF_Unitary_Formula f -> join THF $ minSublogic f
   T0UT_Constant _ -> THF0
   T0UT_Variable _ -> THF0
   T0UT_Defined_Type df -> join THF0 $ minSublogic df
   T0UT_System_Type _ -> THF0
   T0UT_THF_Binary_Type_Par bt -> join THF0 $ minSublogic bt
 --fixme: how do all these THF0 types differ from THF?
