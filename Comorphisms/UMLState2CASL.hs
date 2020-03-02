{-# LANGUAGE MultiParamTypeClasses , RankNTypes , TypeSynonymInstances , FlexibleInstances #-}
module Comorphisms.UMLState2CASL where

import Common.Id
import Common.ProofTree
import Common.AS_Annotation (makeNamed,emptyAnno)
import Common.Lib.State
import Common.Lib.MapSet as MapSet
import Common.Lib.Rel as Rel

import Data.Set as Set
import Data.Map as Map

import Logic.Logic
import Logic.Comorphism

import UMLState.Logic_UMLState

import qualified CASL.Logic_CASL as CL
import qualified CASL.AS_Basic_CASL as CA
import qualified CASL.Sublogic as CSL
import qualified CASL.Formula as CF
import qualified CASL.Morphism as CM
import qualified CASL.Sign as CS


type CSub     = CSL.CASL_Sublogics
type CBasic   = CL.CASLBasicSpec
type CForm    = CA.CASLFORMULA
type CSyms    = CA.SYMB_ITEMS
type CSymMaps = CA.SYMB_MAP_ITEMS
type CSign    = CS.CASLSign
type CMor     = CM.CASLMor
type CSym     = CS.Symbol
type CRawSym  = CM.RawSymbol
type CProof   = ProofTree

data UMLState2CASL = UMLState2CASL deriving Show

instance Language UMLState2CASL where
  language_name UMLState2CASL = "UMLState2CASL"
  description   UMLState2CASL = "TODO"

instance Comorphism UMLState2CASL
  UMLState ()   BASIC_SPEC EDHML ()    ()       Library  Morphism Token ()      ()
  CL.CASL  CSub CBasic     CForm CSyms CSymMaps CSign    CMor     CSym  CRawSym CProof
  where
    sourceLogic UMLState2CASL = UMLState
    sourceSublogic UMLState2CASL = ()
    targetLogic UMLState2CASL = CL.CASL
    mapSublogic UMLState2CASL () = Just top
    map_theory UMLState2CASL (sign, _) = do
      let
        computeSign = do
          sequence [ CS.addSort CA.NonEmptySorts (emptyAnno s) s
                   | s <- [ctrlSort, evtSort, natSort, confSort, evtNameSort, evtNameSetSort]
                   ]
          sequence [ CS.addSymbol $ CS.idToOpSymbol (token2Id o)
                                  $ CS.OpType CA.Total [] ctrlSort
                   | o <- Set.toList $ statesL sign
                   ]
          sequence [ CS.addSymbol $ CS.idToOpSymbol (token2Id o)
                                  $ CS.OpType CA.Total [confSort] natSort
                   | o <- Set.toList $ attrL sign
                   ]
          sequence [ CS.addSymbol $ CS.idToOpSymbol (token2Id $ prefixEvt o)
                                  $ CS.OpType CA.Total (take ar $ repeat natSort) evtSort
                   | ((o,ar),_) <- Map.toList $ actsL sign
                   ]
          CS.addSymbol $ CS.idToPredSymbol (str2Id "reachable2")
                       $ CS.PredType [evtNameSetSort,confSort]
          CS.addSymbol $ CS.idToPredSymbol (str2Id "reachable3")
                       $ CS.PredType [evtNameSetSort,confSort,confSort]
          CS.addSymbol $ CS.idToOpSymbol (str2Id "ctrl")
                       $ CS.OpType CA.Total [confSort] ctrlSort
          CS.addSymbol $ CS.idToOpSymbol (str2Id "evtName")
                       $ CS.OpType CA.Total [evtSort] evtNameSort
          modify $ \csign -> csign
            { CS.sortRel = transClosure $ Rel.fromMap $ Map.fromList
                [ (ctrlSort, Set.empty)
                , (evtSort, Set.empty)
                , (natSort, Set.empty)
                , (confSort, Set.empty)
                , (evtNameSort, Set.empty)
                , (evtNameSetSort, Set.empty)
                ]
            , CS.predMap = MapSet.fromMap $ Map.fromList
                [ (str2Id "reachable2", Set.fromList[CS.PredType [evtNameSetSort,confSort]])
                , (str2Id "init", Set.fromList[CS.PredType [confSort]])
                , (str2Id "trans", Set.fromList[CS.PredType [confSort,evtSort,confSort]])
                ]
            , CS.opMap = MapSet.fromMap $ Map.fromList (
                [ (token2Id $ prefixEvt o, Set.fromList[CS.OpType CA.Total (take ar $ repeat natSort) evtSort])
                | ((o,ar),_) <- Map.toList $ actsL sign
                ] ++ [ (token2Id $ prefixEvtName o, Set.fromList[CS.OpType CA.Total [] evtNameSort])
                     | ((o,ar),_) <- Map.toList $ actsL sign
                ] ++ [ (token2Id o, Set.fromList[CS.OpType CA.Total [confSort] natSort])
                     | o <- Set.toList $ attrL sign
                ] ++ [ (str2Id "ctrl", Set.fromList[CS.OpType CA.Total [confSort] ctrlSort])
                     , (str2Id "conf", Set.fromList[CS.OpType CA.Total ([ctrlSort] ++ take (Set.size $ attrL sign) (repeat natSort)) confSort])
                     , (str2Id "evtName", Set.fromList[CS.OpType CA.Total [evtSort] evtNameSort])
                ] ++ [ (token2Id s, Set.fromList[CS.OpType CA.Total [] ctrlSort])
                     | s <- Set.toList $ statesL sign
                     ]
              )
            }
        csign = execState computeSign (CS.emptySign ())
        g = str2Token "g"
        vars = (attrL sign,g,prime g)
        machine = CA.mkForall [CA.mkVarDecl g confSort] (
                    initP (confVar g) `CA.mkImpl` edhml2CASL vars (lib2EDHML sign)
                  )
        confOp = op (str2Token "conf")
                    ([ctrlSort] ++ take (Set.size $ attrL sign) (repeat natSort))
                    confSort
      {- error ("sortRel: " ++ show (CS.sortRel csign)) `seq`-}
      return ( csign
             , [ makeNamed "init" $ initCASL sign
               , makeNamed "free_types"
                 $ CA.Sort_gen_ax [ CA.Constraint evtSort
                                                  [ ( op (prefixEvt o) (take ar $ repeat natSort) evtSort
                                                    , take ar $ repeat 0
                                                    )
                                                  | ((o,ar),_) <- Map.toList $ actsL sign
                                                  ]
                                                  evtSort
                                  , CA.Constraint evtNameSort
                                                  [ ( op (prefixEvtName o) [] evtNameSort
                                                    , take ar $ repeat 0
                                                    )
                                                  | ((o,ar),_) <- Map.toList $ actsL sign
                                                  ]
                                                  evtNameSort
                                  , CA.Constraint confSort [(confOp, [])] confSort
                                  ]
                                  True
               ] ++ [ makeNamed "machine" m
                    | m <- sepCASL $ edhml2CASL vars $ lib2EDHML sign
                    ]
                 ++ [ makeNamed "evtEqs"
                        ( univEvtArgs vars
                            (CA.mkStEq (evtNameOp `CA.mkAppl` [eventItem2CASLterm e])
                                       (constTerm (prefixEvtName name) evtNameSort)
                            )
                        )
                    | (_, e@(EvtI name vars)) <- Map.toList $ actsL sign
                    ]
             )

    map_sentence UMLState2CASL sen = undefined
    map_symbol UMLState2CASL lib tok = Set.singleton $ CS.Symbol (token2Id tok) undefined
