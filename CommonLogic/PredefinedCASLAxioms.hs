{- |
Module      :  ./CommonLogic/PredefinedCASLAxioms.hs
Description :  Central datastructures for development graphs
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Fixed CASL axioms needed for translation of CommonLogic to CASL
-}

module CommonLogic.PredefinedCASLAxioms where


import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id

import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import CASL.AS_Basic_CASL
import CASL.Sign

import qualified Data.Set as Set
import qualified Data.HashMap.Strict as Map

list :: Id
list = stringToId "list"

append :: Id
append = stringToId "append"

cons :: Id
cons = stringToId "cons"

nil :: Id
nil = stringToId "nil"

individual :: Id
individual = stringToId "individual"

x1 :: Token
x1 = mkSimpleId "X1"

x2 :: Token
x2 = mkSimpleId "X2"

y1 :: Token
y1 = mkSimpleId "Y1"

y2 :: Token
y2 = mkSimpleId "Y2"

nilTypeS :: OpType
nilTypeS = mkTotOpType [] list

consTypeS :: OpType
consTypeS = mkTotOpType [individual, list] list

appendTypeS :: OpType
appendTypeS = mkTotOpType [list, list] list

nilType :: OP_TYPE
nilType = toOP_TYPE nilTypeS

consType :: OP_TYPE
consType = toOP_TYPE consTypeS

appendType :: OP_TYPE
appendType = toOP_TYPE appendTypeS

baseListAxioms :: [Named CASLFORMULA]
baseListAxioms =
  [ ga_injective_cons
  , ga_disjoint_nil_cons
  , ga_generated_list
  , ga_nil_append
  , ga_cons_append ]

-- currently a list annotation is needed in the .dol file %list [__], nil, cons
brId :: Id
brId = mkId [mkSimpleId "[", placeTok, mkSimpleId "]"]

-- | setting casl sign: sorts, cons, nil, append
listSig :: CASLSign
listSig = (emptySign ())
               { sortRel = Rel.fromKeysSet
                   $ Set.fromList [list, individual]
               , opMap = MapSet.fromList
                         [ (cons, [consTypeS])
                         , (nil, [nilTypeS])
                         , (append, [appendTypeS])
                         ]
               , globAnnos = emptyGlobalAnnos
                     { literal_annos = emptyLiteralAnnos
                       { list_lit = Map.singleton brId (nil, cons) }
                     , literal_map = Map.fromList
                          [ (cons, ListCons brId nil)
                          , (nil, ListNull brId)]}
               }

vx2 :: VAR_DECL
vx2 = mkVarDecl x2 list

vy1 :: VAR_DECL
vy1 = mkVarDecl y1 individual

vy2 :: VAR_DECL
vy2 = mkVarDecl y2 list

tx1, tx2, ty1, ty2 :: TERM f

tx1 = mkVarTerm x1 individual
tx2 = mkVarTerm x2 list

ty1 = mkVarTerm y1 individual
ty2 = mkVarTerm y2 list

consOp :: OP_SYMB
consOp = mkQualOp cons consType

nilOp :: OP_SYMB
nilOp = mkQualOp nil nilType

mkCons :: TERM f -> TERM f -> TERM f
mkCons t1 t2 = mkAppl consOp [t1, t2]

mkNil :: TERM f
mkNil = mkAppl nilOp []

mkAppend :: TERM f -> TERM f -> TERM f
mkAppend l1 l2 = mkAppl (mkQualOp append appendType) [l1, l2]

ga_injective_cons :: Named CASLFORMULA
ga_injective_cons = makeNamed "ga_injective_cons" $
  mkForall
    [ mkVarDecl x1 individual
    , vy1
    , vx2
    , vy2
    ]
    $ mkEqv
        (mkStEq
          (mkCons tx1 tx2)
          $ mkCons ty1 ty2
        )
        $ conjunct
          [ mkStEq tx1 ty1
          , mkStEq tx2 ty2
          ]

ga_disjoint_nil_cons :: Named CASLFORMULA
ga_disjoint_nil_cons = makeNamed "ga_disjoint_nil_cons" $
  mkForall [vy1, vy2] $ mkNeg $ mkStEq mkNil $ mkCons ty1 ty2

ga_nil_append :: Named CASLFORMULA
ga_nil_append = makeNamed "ga_nil_append"
  $ mkForall [vx2]
  $ mkStEq (mkAppend mkNil tx2) tx2

ga_cons_append :: Named CASLFORMULA
ga_cons_append = makeNamed "ga_cons_append"
  $ mkForall [vy1, vy2, vx2]
  $ mkStEq (mkAppend (mkCons ty1 ty2) tx2)
      $ mkCons ty1 $ mkAppend ty2 tx2

ga_generated_list :: Named CASLFORMULA
ga_generated_list = makeNamed "ga_generated_list" $
  mkSort_gen_ax
    [ Constraint
      { newSort = list
      , opSymbs =
          [ (consOp, [-1, 0] )
          , (nilOp, [])
          ]
      , origSort = list
      }
    ] True
