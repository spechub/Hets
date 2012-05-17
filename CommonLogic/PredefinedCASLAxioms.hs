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

baseCASLAxioms :: [AS_Anno.Named CBasic.CASLFORMULA]
baseCASLAxioms = [ga_injective_cons, ga_disjoint_nil_cons, ga_generated_list]

-- | setting casl sign: sorts, cons, fun, nil, pred
caslSig :: CSign.CASLSign
caslSig = (CSign.emptySign ())
               { CSign.sortRel = Rel.fromKeysSet
                   $ Set.fromList [list, individual]
               , CSign.opMap = MapSet.fromList
                         [ (cons, [CSign.mkTotOpType
                                   [individual, list]
                                   list])
                         , (fun, [CSign.mkTotOpType
                                  [individual, list]
                                  individual])
                         , (nil, [CSign.mkTotOpType [] list])]
               , CSign.predMap = MapSet.fromList
                [(rel, [CSign.PredType [individual, list]])]
               }

ga_injective_cons :: AS_Anno.Named CBasic.CASLFORMULA
ga_injective_cons = AS_Anno.makeNamed "ga_injective_cons" $
  CBasic.Quantification CBasic.Universal
    [ CBasic.Var_decl [x1] individual Id.nullRange
    , CBasic.Var_decl [x2] list Id.nullRange
    , CBasic.Var_decl [y1] individual Id.nullRange
    , CBasic.Var_decl [y2] list Id.nullRange
    ]
    (CBasic.Equivalence
        (CBasic.Strong_equation
          (CBasic.Application
            (CBasic.Qual_op_name cons
              (CBasic.Op_type CBasic.Total [individual,list] list Id.nullRange)
              Id.nullRange
            )
            [ CBasic.Qual_var (x1) individual Id.nullRange
            , CBasic.Qual_var (x2) list Id.nullRange
            ] Id.nullRange
          )
          (CBasic.Application
            (CBasic.Qual_op_name cons
              (CBasic.Op_type CBasic.Total [individual,list] list Id.nullRange)
              Id.nullRange
            )
            [ CBasic.Qual_var (y1) individual Id.nullRange
            , CBasic.Qual_var (y2) list Id.nullRange
            ] Id.nullRange
          ) Id.nullRange)
        (CBasic.Conjunction
          [ CBasic.Strong_equation
              (CBasic.Qual_var (x1) individual Id.nullRange)
              (CBasic.Qual_var (y1) individual Id.nullRange)
              Id.nullRange
          , CBasic.Strong_equation
              (CBasic.Qual_var (x2) list Id.nullRange)
              (CBasic.Qual_var (y2) list Id.nullRange)
              Id.nullRange
          ] Id.nullRange
        ) Id.nullRange
    ) Id.nullRange

ga_disjoint_nil_cons :: AS_Anno.Named CBasic.CASLFORMULA
ga_disjoint_nil_cons = AS_Anno.makeNamed "ga_disjoint_nil_cons" $
  CBasic.Quantification CBasic.Universal
    [ CBasic.Var_decl [y1] individual Id.nullRange
    , CBasic.Var_decl [y2] list Id.nullRange
    ]
    (CBasic.Negation
      (CBasic.Strong_equation
        (CBasic.Application
          (CBasic.Qual_op_name nil
            (CBasic.Op_type CBasic.Total [] list Id.nullRange)
            Id.nullRange
          ) [] Id.nullRange
        )
        (CBasic.Application
          (CBasic.Qual_op_name cons
            (CBasic.Op_type CBasic.Total [individual,list] list Id.nullRange)
            Id.nullRange
          )
          [ CBasic.Qual_var (y1) individual Id.nullRange
          , CBasic.Qual_var (y2) list Id.nullRange
          ] Id.nullRange
        ) Id.nullRange
      ) Id.nullRange
    ) Id.nullRange

ga_generated_list :: AS_Anno.Named CBasic.CASLFORMULA
ga_generated_list = AS_Anno.makeNamed "ga_generated_list" $
  CBasic.Sort_gen_ax
    [ CBasic.Constraint
      { CBasic.newSort = list
      , CBasic.opSymbs =
          [ (CBasic.Qual_op_name cons
              (CBasic.Op_type CBasic.Total [individual,list] list Id.nullRange)
              Id.nullRange
            , [-1,0] )
          , (CBasic.Qual_op_name nil
              (CBasic.Op_type CBasic.Total [] list Id.nullRange)
              Id.nullRange
              , [])
          ]
      , CBasic.origSort = list
      }
    ] True
