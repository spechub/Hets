{-# LANGUAGE MultiParamTypeClasses , FlexibleContexts , TypeSynonymInstances , FlexibleInstances, DeriveDataTypeable #-}

{- |
Module      : $Id$
Description : Instance of class Logic for the UMLComp logic
Copyright   :  (c) Tobias Rosenberger, Swansea University and Universit{'e} Grenoble Alpes 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  TRosenberger@gmx.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

This implements simple UML Composite structures which are suitable to compose the State Machines of "UMLState.Logic_UMLState".

The construction and the reasons behind it are explained in:
  Rosenberger, T., Knapp, A., & Roggenbach, M. (2022). An Institutional Approach to Communicating UML State Machines. In International Conference on Fundamental Approaches to Software Engineering (pp. 205-224). Springer, Cham. DOI: https://doi.org/10.1007/978-3-030-99429-7

However, these Composite Structures can be used more generally. We recommend composing with them through CASL.
All you need for this are compatible 'initP' and 'transP' predicates. Our precise interface in CASL can be seen in the 'translate' function, specifically, in the equations for 'sortRel', 'predMap' and 'opMap'. We also strongly recommend using our 'ap' function for applying operators and our 'pr' function for predication.

The type 'BASIC_SPEC' is the entry point for the abstract syntax, the function 'parse_BASIC_SPEC' for parsing and the function 'ana_BASIC_SPEC' for static analysis.

An example file can be found in @test\/UMLTests\/atmmod.het@.
-}

module UMLComp.Logic_UMLComp where

import ATerm.Conversion

import CASL.ToDoc -- just for ghci debugging
import qualified CASL.AS_Basic_CASL as C
import qualified CASL.Formula as CF
import qualified CASL.Logic_CASL as CL
import qualified CASL.Morphism as CM
import qualified CASL.Sign as CS
import qualified CASL.Sublogic as CSL

import Common.AnnoState
import Common.AS_Annotation (Named,makeNamed,emptyAnno)
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.Lexer
import Common.Lib.MapSet as MapSet
import Common.Lib.Rel as Rel
import Common.Parsec
  hiding ( (<|>) ) -- use the more general version from "Control.Applicative"
import Common.ProofTree
import Common.Result as R

import Control.Applicative ( Alternative, (<|>) )
import Control.Monad (when)
import Control.Monad.Fail (MonadFail)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State as S

import Data.Set as Set
import Data.Map as Map
import Data.List as List
import Data.Functor.Identity

import qualified Data.Data as D

import Logic.Logic
import Logic.Comorphism

import Text.Parsec
  hiding ( (<|>) ) -- use the more general version from "Control.Applicative"
import Text.Parsec.Expr
import Text.Parsec.String
import Text.ParserCombinators.Parsec.Char

type CSub     = CSL.CASL_Sublogics
type CBasic   = CL.CASLBasicSpec
type CForm    = C.CASLFORMULA
type CSyms    = C.SYMB_ITEMS
type CSymMaps = C.SYMB_MAP_ITEMS
type CSign    = CS.CASLSign
type CMor     = CM.CASLMor
type CSym     = CS.Symbol
type CRawSym  = CM.RawSymbol
type CProof   = ProofTree


data UMLComp = UMLComp deriving (Eq,Ord,Show,D.Data) -- typeclass argument to identify logic
type Morphism = Sign -- only identity morphisms
data Sentence = TrueSen deriving (Eq,Ord,Show,D.Data) -- no nontrivial sentences
data Sign = Sign
  { nameS        :: [COMP_NAME]
  , machinesS    :: Map MACHINE_NAME MACHINE_TYPE
  , machineTysS  :: Set MACHINE_TYPE
  , exportsS     :: Map PORT_NAME MACHINE_NAME
  , connsS       :: Map PORT_NAME (MACHINE_NAME, MACHINE_NAME, PORT_NAME)
  } deriving (Eq,Show,Ord)

sign2SymSet sign = ( Set.fromList $ nameS     sign )
       `Set.union` ( Map.keysSet  $ machinesS sign )
       `Set.union` ( machineTysS  $           sign )
       `Set.union` ( Map.keysSet  $ exportsS  sign )
       `Set.union` ( Map.keysSet  $ connsS    sign )

instance Category Sign Morphism where
  ide sig = sig
  inverse f = return f
  composeMorphisms f g = return f
  dom f = f
  cod f = f
  isInclusion f = True
  legal_mor f = return ()

instance Monoid BASIC_SPEC where
instance Pretty BASIC_SPEC where
instance GetRange BASIC_SPEC where
instance GetRange Sentence where
instance Language UMLComp where

-- BEGIN parsing, grammar, AS

type COMP_NAME    = Token
parse_COMP_NAME = do string "name"
                     skipSmart
                     name <- str2Token <$> scanLetterWord
                     skipSmart
                     return name
ana_COMP_NAME nameT@(Token name _) = do
  lib <- S.get
  case nameS lib of []                   -> do S.put lib { nameS = [nameT] }
                                               return nameT
                    (Token oldName _: _) ->
                       errC (    "Two name declarations for Composite Structure: '"
                               ++ oldName ++ "' and '" ++ name ++ "'."
                            )
type MACHINE_NAME = Token
parse_MACHINE_NAME = str2Token <$> scanLetterWord

type MACHINE_TYPE = Token
parse_MACHINE_TYPE = str2Token <$> scanLetterWord

type PORT_NAME    = Token
parse_PORT_NAME = str2Token <$> scanLetterWord


data  BASIC_SPEC  = Basic [DECL] deriving (Eq,Ord,Show,D.Data)

parse_BASIC_SPEC :: t -> ParsecT [Char] u Identity BASIC_SPEC
parse_BASIC_SPEC  _ = Basic <$> (parse_DECL `sepBy` asSeparator ";") << theEnd

ana_BASIC_SPEC :: BASIC_SPEC -> Check BASIC_SPEC
ana_BASIC_SPEC (Basic xs) = Basic <$> sequence (ana_DECL <$> xs)

data  DECL = NameD   COMP_NAME
           | MachD   MACHINE_DECL
           | ExportD EXPORT_DECL
           | ConnD   CONN_DECL
           deriving (Eq,Ord,Show,D.Data)
parse_DECL = do NameD   <$> parse_COMP_NAME
         <|> do MachD   <$> parse_MACHINE_DECL
         <|> do ExportD <$> parse_EXPORT_DECL
         <|> do ConnD   <$> parse_CONN_DECL
ana_DECL (NameD   decl) = NameD   <$> ana_COMP_NAME    decl
ana_DECL (MachD   decl) = MachD   <$> ana_MACHINE_DECL decl
ana_DECL (ExportD decl) = ExportD <$> ana_EXPORT_DECL  decl
ana_DECL (ConnD   decl) = ConnD   <$> ana_CONN_DECL    decl

data  MACHINE_DECL = Mach MACHINE_NAME MACHINE_TYPE
                   deriving (Eq,Ord,Show,D.Data)
parse_MACHINE_DECL = do key "comp"
                        name <- parse_MACHINE_NAME
                        skipSmart
                        asSeparator ":"
                        ty   <- parse_MACHINE_TYPE
                        skipSmart
                        return $ Mach name ty
ana_MACHINE_DECL mach@(Mach name@(Token nameStr _) ty) = do
  lib <- S.get
  let oldMachines   = machinesS   lib
      oldMachineTys = machineTysS lib
      newLib = lib { machinesS   = Map.insert name ty oldMachines
                   , machineTysS = Set.insert ty oldMachineTys
                   }
  when (name `Map.member` oldMachines)
       $ errC ("machine declared twice: " ++ nameStr)
  S.put newLib
  return mach

data  EXPORT_DECL  = Export MACHINE_NAME PORT_NAME
                   deriving (Eq,Ord,Show,D.Data)
parse_EXPORT_DECL  = do key "export"
                        mach <- parse_MACHINE_NAME
                        string "."
                        port <- parse_PORT_NAME
                        skipSmart
                        return $ Export mach port
ana_EXPORT_DECL ex@(Export mach@(Token mname _) port@(Token pname _)) = do
  lib <- S.get
  when ( mach `Map.notMember` machinesS lib)
       $ errC ("Port exported for undeclared machine: "++mname++"."++ pname)
  when ( port `Map.member` exportsS lib || port `Map.member` connsS lib )
       $ errC (  "We do not allow duplicate ports, even for different machines. "
              ++ "Port declared twice: "
              ++ token2Str port
              )
  S.put $ lib { exportsS = Map.insert port mach $ exportsS lib }
  return ex
  

data  CONN_DECL = Conn MACHINE_NAME PORT_NAME MACHINE_NAME PORT_NAME
                deriving (Eq,Ord,Show,D.Data)
parse_CONN_DECL = do key "conn"
                     name1 <- parse_MACHINE_NAME
                     string "."
                     port1 <- parse_PORT_NAME
                     skipSmart
                     asSeparator "--"
                     name2 <- parse_MACHINE_NAME
                     string "."
                     port2 <- parse_PORT_NAME
                     skipSmart
                     return $ Conn name1 port1 name2 port2
ana_CONN_DECL conn@(Conn m1@(Token m1name _) p1@(Token p1name _)
                         m2@(Token m2name _) p2@(Token p2name _)) = do
  lib <- S.get
  let machs = machinesS lib
      connsOld = connsS lib
      connsNew = Map.insert p1 (m1,m2,p2)
               $ Map.insert p2 (m2,m1,p1)
               $ connsOld
      checkMachine mach@(Token mname _) pname
        = when ( mach `Map.notMember` machinesS lib)
               $ errC ("Can't connect port for undeclared machine: "++mname++"."++pname)
      checkForDoubleConn port
        = when ( port `Map.member` exportsS lib || port `Map.member` connsS lib )
               $ errC (  "We do not allow duplicate ports, even for different machines. "
                      ++ "Port declared twice: "
                      ++ token2Str port
                      )
  checkMachine m1 p1name
  checkMachine m2 p2name
  checkForDoubleConn p1
  checkForDoubleConn p2
  S.put $ lib { connsS = connsNew }
  return conn

-- END parsing, grammar, AS

instance ShATermConvertible BASIC_SPEC where
instance Syntax UMLComp BASIC_SPEC Token () () where
  parsersAndPrinters UMLComp = makeDefault (parse_BASIC_SPEC, pretty)

instance Sentences UMLComp Sentence Sign Morphism Token where
instance StaticAnalysis UMLComp BASIC_SPEC Sentence () () Sign Morphism Token () where
  basic_analysis _ = Just $ \ (spec,sign,annos) -> do
    (spec',sign') <- runStateT (ana_BASIC_SPEC spec) mempty
    let symSet             = sign2SymSet sign'
        extSign            = ExtSign sign' symSet
        sentencesWithAnnos = []
    return (spec', extSign, sentencesWithAnnos)

instance Logic UMLComp () BASIC_SPEC Sentence () () Sign Morphism Token () () where
instance Pretty Sentence where
instance Pretty Sign where
instance ShATermConvertible Sentence where
instance ShATermConvertible Sign where
instance Monoid Sign where
  mempty = Sign mempty mempty mempty mempty mempty
  l1 `mappend` l2 = Sign { nameS       = nameS       l1 `mappend` nameS       l2
                         , machinesS   = machinesS   l1 `mappend` machinesS   l2
                         , machineTysS = machineTysS l1 `mappend` machineTysS l2
                         , exportsS    = exportsS    l1 `mappend` exportsS    l2
                         , connsS      = connsS      l1 `mappend` connsS      l2
                         }

-- miscallaneous helpers
theEnd :: Parsec String st String
theEnd = optionMaybe (asSeparator ";") >> key "end"

str2Token :: String -> Token
str2Token name = Token name nullRange

type Check = StateT Sign Result  
errC :: String -> Check a
errC s = lift $ fatal_error s nullRange

key :: String -> Parsec String st String
key s = try (keyWord (string s) << skipSmart)

-- BEGIN translation
data UMLComp2CASL = UMLComp2CASL deriving Show

instance Language UMLComp2CASL where -- default is OK

instance Comorphism UMLComp2CASL
  UMLComp  ()   BASIC_SPEC Sentence    ()    ()       Sign  Morphism Token ()      ()
  CL.CASL  CSub CBasic     CForm       CSyms CSymMaps CSign CMor     CSym  CRawSym CProof
  where
    sourceLogic UMLComp2CASL = UMLComp
    sourceSublogic UMLComp2CASL = ()
    targetLogic UMLComp2CASL = CL.CASL
    map_theory UMLComp2CASL = translate
    map_sentence UMLComp2CASL lib sen = return C.trueForm
    map_symbol UMLComp2CASL lib tok = Set.singleton $ CS.Symbol (token2Id tok) undefined

translate :: (Sign, [Named Sentence])
          -> Result (CSign, [Named CForm])
translate (sign,sentences) = do
  justHint undefined "translating from UMLComp to CASL"
  let 
      [composTy] = nameS sign  -- should just be one, checked at ana_COMP_NAME
      machTys    = Set.elems  $ machineTysS sign
      machs      = Map.toList $ machinesS   sign
      conns      = connsS sign
      innerPorts = Map.keys conns
      portNames  = innerPorts ++ Map.keys (exportsS sign)


      -- machOfPort, portOpposite and machOpposite MUST NOT be called with possibly nonexistant ports!
      -- portOpposite and machOpposite MUST ONLY be called with internal ports!
      machOfPort port
        | Just (m1,m2,p2) <- Map.lookup port conns
        = m1
        | Just m          <- Map.lookup port $ exportsS sign
        = m
      portOpposite port
        | Just (m1,m2,p2) <- Map.lookup port conns
        = p2
      machOpposite port
        | Just (m1,m2,p2) <- Map.lookup port conns
        = m2

      csign = (CS.emptySign ())
        { CS.sortRel = transClosure $ Rel.fromMap $ Map.fromList
          (
            -- per machine type/composTy
            [ (s tyName, Set.empty) 
            | tyName <- composTy : machTys
            , s <- [ confSort
                   ]
            ] ++
            -- just once (per composTy)
            [ (s, Set.empty)
            | s <- [ portSort
                   , evtSort
                   , msgSort
                   , msgListSort
                   , msgQueueSort
                   ]
            ]
         )
        , CS.predMap = MapSet.fromMap $ Map.fromList
            ( 
              -- per machine type/composTy
              [ (pname, Set.fromList [pty])
              | tyName <- composTy : machTys
              , (pname, pty) <- [ initP  tyName
                                , transP tyName
                                ]
              ] ++
              -- just once (per composTy)
              [ (pname, Set.fromList [pty])
              | (pname, pty) <- [ distP composTy $ length machs ]
              ]
            )
        , CS.opMap = MapSet.fromMap $ Map.fromList
            (
              -- per individual machine (and composTy)
              [ (oname, Set.fromList [oty])
              | (machName,_) <- machs
              , (oname,oty)  <- [ queueProjOp composTy machName
                                ]
              ] ++
              -- just once (per composTy)
              [ (oname, Set.fromList [oty])
              | (oname,oty) <- [ con
                               | (_,cons) <- constructors
                               , con <- cons
                               ]
                            ++ [ dequeueOp ]
                            ++ ( portConOp <$> portNames )
              ]
            )
        }

      -- Constructors for free types.
      -- Note that machine specific types,
      --   as well as event types,
      --   are not free as far as the composite structure is concerned.
      constructors = [ ( (confSort composTy)
                       , [confConOp composTy machs]
                       )
                     , ( msgSort
                       , [msgConOp]
                       )
                     , ( msgListSort
                       , [nilOp, consOp]
                       )
                     , ( msgQueueSort
                       , [emptyQueueOp, enqueueOp]
                       )
                     ]

      -- numbered argument variables for "noConfusion" axioms:
      argVars op baseNum = [ C.mkVarDecl (str2Token ("v" ++ show n))
                                         sort
                           | (n,sort) <- [baseNum..] `zip` argSorts op
                           ]
      csentences =
        [ makeNamed "generatedTypes"
           $ C.Sort_gen_ax
               [ C.Constraint sort (op <$> constructor) sort
               | (sort,constructor) <- constructors
               ]
               True
        ] ++
        [ makeNamed ("noConfusion " ++ nameStr c1 ++" "++ nameStr c2)
                    $ C.mkForall (c1Vars++c2Vars) $ if   c1 == c2
                                                    then injectivity
                                                    else disjointness
        | (sort, cons) <- constructors
        , c1 <- cons
        , c2 <- cons
        , let c1Vars = argVars c1 0
        , let c2Vars = argVars c2 $ length c1Vars
        , let c1Args = var2Term <$> c1Vars
        , let c2Args = var2Term <$> c2Vars
        , let c1Term = c1 `ap` c1Args
        , let c2Term = c2 `ap` c2Args
        , let injectivity = (c1Term `C.mkStEq` c2Term)
                            `C.mkImpl`
                            (C.conjunct $ zipWith C.mkStEq c1Args c2Args)
        , let disjointness = C.mkNeg (c1Term `C.mkStEq` c2Term)
        ] ++
        [ makeNamed "portsDisjoint"
           $ C.conjunct [ C.mkNeg (portTerm p1 `C.mkStEq` portTerm p2)
                        | p1 <- portNames
                        , p2 <- portNames
                        , p1 /= p2
                        ]
        , makeNamed "defInit"
           $ C.mkForall (confQueueVars machs)
              ( ( initP composTy `pr` [confConOp composTy machs `ap` (var2Term <$> confQueueVars machs)] )
                `C.mkEqv`
                C.conjunct [ initP machTy `pr` [var2Term $ confVar mach]
                           | mach@(machName, machTy) <- machs
                           ]
              )
        , makeNamed "defTrans" -- each step of the system corresponds to a step of some machine
           $ C.mkForall (confQueueVars machs ++ [inVar,outVar] ++ confQueueVars' machs)
               (   ( transP composTy `pr` [ confConOp composTy machs `ap` (var2Term <$> confQueueVars  machs)
                                          , var2Term inVar
                                          , var2Term outVar
                                          , confConOp composTy machs `ap` (var2Term <$> confQueueVars' machs)
                                          ]
                   )
                 `C.mkEqv` 
                   ( C.disjunct [ transP machType `pr` ( var2Term <$> [ confVar  mach
                                                                      , inVar
                                                                      , outVar
                                                                      , confVar' mach
                                                                      ]
                                                       )
                                  `andC`
                                  ( distP composTy (length machs) `pr` [ if    var == queueVar mach
                                                                            && port `elem` innerPorts 
                                                                         then dequeueOp `ap` [var2Term var]
                                                                         else var2Term var
                                                                       | var <- distVars machs
                                                                       ]
                                  )
                                | mach@(machName, machType) <- machs
                                , port <- portNames
                                , machOfPort port == machName -- TODO more efficient join for large composite structures
                                ]
                   )
               )
        , makeNamed "defDist"
            $ C.mkForall (distVars machs)
                ( ( distP composTy (length machs) `pr` (var2Term <$> distVars machs) )
                  `C.mkEqv`
                  ( C.disjunct [ var2Term outVar `C.mkStEq` (nilOp `ap` [])
                               | mach <- machs
                               ]
                    `orC`
                    C.mkExist [evtVar, outVar']
                      ( C.disjunct
                          [ ( var2Term outVar
                              `C.mkStEq`
                              ( consOp `ap` [ msgConOp `ap` [portTerm innerPort, var2Term evtVar]
                                            , var2Term outVar'
                                            ]
                              )
                            )
                            `andC`
                            ( distP composTy (length machs)
                              `pr`
                              (   var2Term outVar'
                                : concat [ [ if machOpposite innerPort == machName
                                             then enqueueOp
                                                  `ap`
                                                  [ msgConOp `ap` [ portTerm $ portOpposite innerPort
                                                                  , var2Term evtVar
                                                                  ]
                                                  , var2Term $ queueVar mach
                                                  ]
                                             else var2Term $ queueVar mach
                                           , var2Term $ queueVar' mach
                                           ]
                                         | mach@(machName, machType) <- machs
                                         ]
                              )
                            )
                          | innerPort <- innerPorts
                          ]
                      )
                  )
                )
        ]
  return (csign,csentences)

-- | auxiliary definitions for constructing CASL sentences
confQueueVars, confQueueVars', distVars :: [(MACHINE_NAME, MACHINE_TYPE)]
                                        -> [C.VAR_DECL]
confQueueVars  machs = concat [ [ confVar  mach
                                , queueVar mach
                                ]
                              | mach <- machs
                              ]
confQueueVars' machs = concat [ [ confVar'  mach
                                , queueVar' mach
                                ]
                              | mach <- machs
                              ]
distVars machs = outVar : concat [ [queueVar mach, queueVar' mach]
                                 | mach <- machs
                                 ]

confVar, confVar', queueVar, queueVar' :: (MACHINE_NAME, MACHINE_TYPE)
                                       -> C.VAR_DECL
confVar  (machName, machType)  =
  C.mkVarDecl (composeTok ["g", token2Str machName])
              (confSort machType)
confVar'  (machName, machType) =
  C.mkVarDecl (composeTok ["g'", token2Str machName])
              (confSort machType)
queueVar (machName,_) =
  C.mkVarDecl (composeTok ["q", token2Str machName])
              msgQueueSort
queueVar' (machName,_) =
  C.mkVarDecl (composeTok ["q'", token2Str machName])
              msgQueueSort

inVar, outVar, outVar', evtVar :: C.VAR_DECL
inVar   = C.mkVarDecl (str2Token "inMsg")    msgSort
outVar  = C.mkVarDecl (str2Token "outMsgs")  msgListSort
outVar' = C.mkVarDecl (str2Token "outMsgs'") msgListSort
evtVar  = C.mkVarDecl (str2Token "e")        evtSort

var2Term :: C.VAR_DECL -> C.TERM f
var2Term (C.Var_decl [name] ty _) = C.mkVarTerm name ty
var2Term decl = error (    "Can't turn VAR_DECL of several variables into term:"
                         ++ show decl
                         ++ "\nTrying this indicates a bug. Please report this."
                      )

type SortName = Id

-- | The sort of configurations for the named machine type or composite structure type.
confSort :: Token -> SortName
confSort     tname = composeId ["Conf"     , token2Str tname]


portSort, evtSort, msgSort, msgListSort, msgQueueSort :: SortName
portSort           = composeId ["Port"     ]
evtSort            = composeId ["Evt"      ]
msgSort            = composeId ["Msg"      ]
msgListSort        = composeId ["MsgList"  ]
msgQueueSort       = composeId ["MsgQueue" ]

portTerm :: PORT_NAME -> C.TERM f
portTerm portName = portConOp portName `ap` []

portConOp :: PORT_NAME -> (Id, CS.OpType)
portConOp portName = ( composeId ["port", token2Str portName]
                     , CS.OpType C.Total [] portSort
                     )

-- | A constructor for a configuration of the named machine type or composite structure type.
confConOp :: Token -> [(t, Token)] -> (Id, CS.OpType)
confConOp ctname machs = ( composeId ["con","Conf",token2Str ctname]
                         , CS.OpType
                             C.Total
                             ( concat [ [confSort machTy, msgQueueSort]
                                      | (_,machTy) <- machs
                                      ]
                             )
                             (confSort ctname)
                         )

msgConOp :: (Id, CS.OpType)
msgConOp = ( composeId ["msg"]
           , CS.OpType C.Total
                       [portSort, evtSort] 
                       msgSort
           )

queueProjOp :: COMP_NAME -> MACHINE_TYPE -> (Id, CS.OpType)
queueProjOp ctname mtname = ( composeId ["proj", "Queue", token2Str ctname, token2Str mtname]
                            , CS.OpType C.Total
                                        [confSort ctname]
                                        msgQueueSort
                            )

emptyQueueOp, enqueueOp, dequeueOp :: (Id, CS.OpType)
emptyQueueOp = ( composeId ["empty"]
               , CS.OpType C.Total
                           []
                           msgQueueSort
               )
enqueueOp = ( composeId ["enqueue"]
            , CS.OpType C.Total
                        [msgSort,msgQueueSort]
                        msgQueueSort
            )
dequeueOp = ( composeId ["dequeue"]
            , CS.OpType C.Partial
                        [msgQueueSort]
                        msgQueueSort
            )

nilTerm :: C.TERM f
nilTerm = nilOp `ap` []

nilOp, consOp :: (Id, CS.OpType)
nilOp = ( composeId ["[]"]
        , CS.OpType C.Total
                    []
                    msgListSort
        )
consOp = ( mkInfix "::"
         , CS.OpType C.Total
                     [msgSort,msgListSort]
                     msgListSort
         )

-- | CASL predication. Infix use recommended.
pr :: (C.PRED_NAME, CS.PredType) -> [C.TERM f] -> C.FORMULA f
pr (name, CS.PredType argTys) args =
  C.mkPredication (C.mkQualPred name (C.Pred_type argTys nullRange))
                  args

-- | CASL operator application. Infix use recommended.
ap :: (C.OP_NAME, CS.OpType) -> [C.TERM f] -> C.TERM f
ap (name, (CS.OpType totality argTys resTy)) args =
  C.mkAppl (C.mkQualOp name (C.Op_type totality argTys resTy nullRange))
           args

op :: (Id, CS.OpType) -> (C.OP_SYMB, [Int])
op (name, (CS.OpType C.Total argTys resTy)) =
  ( C.mkQualOp name (C.Op_type C.Total argTys resTy nullRange)
  , take (length argTys)
         (repeat 0)
  )

argSorts :: (t, CS.OpType) -> [C.SORT]
argSorts (name, (CS.OpType totality argTys resTy)) = argTys

nameStr :: (Id, t) -> String
nameStr (name, _) = simpleId2Str name

andC, orC :: C.FORMULA f -> C.FORMULA f -> C.FORMULA f
f `andC` g = C.conjunct [f,g]
f `orC`  g = C.disjunct [f,g]

-- | The initial configuration predicate for the named composite structure type or machine type.
initP :: Token -> (Id, CS.PredType)
initP  tname = ( composeId ["init",token2Str tname]
               , CS.PredType [confSort tname]
               )

-- | The transition predicate for the named composite structure type or machine type.
transP :: Token -> (Id, CS.PredType)
transP tname = ( composeId ["trans", token2Str tname]
               , CS.PredType [confSort tname, msgSort, msgListSort,confSort tname]
               )

-- | A CASL predicate for distributing outputs into message queues.
distP :: COMP_NAME -> Int -> (Id, CS.PredType)
distP ctname mcount = ( composeId ["dist", token2Str ctname]
                      , CS.PredType (    [msgListSort]
                                      ++ (take mcount $ repeat $ msgQueueSort)
                                    )
                      )

token2Id :: Token -> Id
token2Id tok   = Id [tok] [] nullRange

token2Str :: Token -> String
token2Str (Token s _) = s

str2Id :: String -> Id
str2Id = token2Id . str2Token

simpleId2Str :: Id -> String
simpleId2Str (Id [Token s _] [] _) = s
simpleId2Str _                     = "MIX"


-- | Define separator, as well as escaping s. t. separator does not occur in words.
--   Escape sequence will be part of CASL identifiers and must consist of ordinary letters.
--   Changing this requires changing 'escape' and 'unescape'.
separator :: String
separator = "Of"

escape :: String -> String
escape ('O':'f':xs)     = "EscF" ++ escape xs
escape ('E':'s':'c':xs) = "EscC" ++ escape xs
escape (x:xs)           = x : escape xs
escape []               = []

unescape :: (Alternative m, MonadFail m) => String -> m String
unescape ('E':'s':'c':xs) = do ('F':ys) <- return xs
                               ("Of"++)  <$> unescape ys
                        <|> do ('C':ys) <- return xs
                               ("Esc"++) <$> unescape ys
unescape (x:xs) = (x:) <$> unescape xs
unescape []     = return []

composeStr :: [String] -> String
composeStr = concat . intersperse separator . fmap escape

composeTok :: [String] -> Token
composeTok = str2Token . composeStr

composeId :: [String] -> Id
composeId  = str2Id    . composeStr

-- END translation

