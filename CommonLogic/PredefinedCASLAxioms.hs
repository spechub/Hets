{- |
Module      :  $Header$
Description :  Central datastructures for development graphs
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Fixed CASL axioms needed for translation of CommonLogic to CASL
-}

module CommonLogic.PredefinedCASLAxioms where


import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id

import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sign as CSign

import qualified Data.Set as Set

list :: Id.Id
list = Id.stringToId "list"

rel :: Id.Id
rel = Id.stringToId "rel"

fun :: Id.Id
fun = Id.stringToId "fun"

cons :: Id.Id
cons = Id.stringToId "cons"

nil :: Id.Id
nil = Id.stringToId "nil"

individual :: Id.Id
individual = Id.stringToId "individual"

x1 :: Id.Token
x1 = Id.mkSimpleId "X1"

x2 :: Id.Token
x2 = Id.mkSimpleId "X2"

y1 :: Id.Token
y1 = Id.mkSimpleId "Y1"

y2 :: Id.Token
y2 = Id.mkSimpleId "Y2"

nilType :: CBasic.OP_TYPE
nilType = CBasic.Op_type CBasic.Total [] list Id.nullRange

consType :: CBasic.OP_TYPE
consType = CBasic.Op_type CBasic.Total [individual, list] list Id.nullRange

baseCASLAxioms :: [AS_Anno.Named CBasic.CASLFORMULA]
baseCASLAxioms = [ga_injective_cons, ga_disjoint_nil_cons, ga_generated_list]

-- | setting casl sign: sorts, cons, fun, nil, pred
caslSig :: CSign.CASLSign
caslSig = (CSign.emptySign ())
               { CSign.sortRel = Rel.fromKeysSet
                   $ Set.fromList [list, individual]
               , CSign.opMap = MapSet.fromList
                         [ (cons, [CSign.toOpType consType])
                         , (fun, [CSign.mkTotOpType
                                  [individual, list]
                                  individual])
                         , (nil, [CSign.toOpType nilType])]
               , CSign.predMap = MapSet.fromList
                [(rel, [CSign.PredType [individual, list]])]
               }


-- | setting casl sign: sorts, cons, nil
listSig :: CSign.CASLSign
listSig = (CSign.emptySign ())
               { CSign.sortRel = Rel.fromKeysSet
                   $ Set.fromList [list, individual]
               , CSign.opMap = MapSet.fromList
                         [ (cons, [CSign.toOpType consType])
                         , (nil, [CSign.toOpType nilType])]
               }
vy1 :: CBasic.VAR_DECL
vy1 = CBasic.mkVarDecl y1 individual

vy2 :: CBasic.VAR_DECL
vy2 = CBasic.mkVarDecl y2 list

tx1, tx2, ty1, ty2 :: CBasic.TERM f

tx1 = CBasic.mkVarTerm x1 individual
tx2 = CBasic.mkVarTerm x2 list

ty1 = CBasic.mkVarTerm y1 individual
ty2 = CBasic.mkVarTerm y2 list

ga_injective_cons :: AS_Anno.Named CBasic.CASLFORMULA
ga_injective_cons = AS_Anno.makeNamed "ga_injective_cons" $
  CBasic.mkForall
    [ CBasic.mkVarDecl x1 individual
    , CBasic.mkVarDecl x2 list
    , vy1
    , vy2
    ]
    $ CBasic.mkEqv
        (CBasic.mkStEq
          (CBasic.mkAppl
            (CBasic.mkQualOp cons consType)
            [tx1, tx2]
          )
          $ CBasic.mkAppl
            (CBasic.mkQualOp cons consType)
            [ty1, ty2]
          )
        $ CBasic.conjunct
          [ CBasic.mkStEq tx1 ty1
          , CBasic.mkStEq tx2 ty2
          ]

ga_disjoint_nil_cons :: AS_Anno.Named CBasic.CASLFORMULA
ga_disjoint_nil_cons = AS_Anno.makeNamed "ga_disjoint_nil_cons" $
  CBasic.mkForall [vy1, vy2]
    $ CBasic.mkNeg
      $ CBasic.mkStEq
        (CBasic.mkAppl (CBasic.mkQualOp nil nilType) [])
        $ CBasic.mkAppl
          (CBasic.mkQualOp cons consType)
          [ty1, ty2]

ga_generated_list :: AS_Anno.Named CBasic.CASLFORMULA
ga_generated_list = AS_Anno.makeNamed "ga_generated_list" $
  CBasic.Sort_gen_ax
    [ CBasic.Constraint
      { CBasic.newSort = list
      , CBasic.opSymbs =
          [ (CBasic.mkQualOp cons consType, [-1, 0] )
          , (CBasic.mkQualOp nil nilType, [])
          ]
      , CBasic.origSort = list
      }
    ] True
