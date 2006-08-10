{- |
Module      :$Header$
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Function that executes the script commands together with the datatypes used.

 TODO :
      - add comments
      - implement the rest of the functions 
      - delete the test function
-} 

module PGIP.Commands where

import Static.AnalysisLibrary
import Driver.Options
import Common.Utils
import Proofs.Automatic
import Proofs.Global
import Proofs.Local
import Proofs.Composition
import Proofs.HideTheoremShift
import Proofs.TheoremHideShift
import Common.Taxonomy
import Data.Maybe
import PGIP.Common




test::([CmdParam])->IO()
test (ls) = putStrLn $ show ls
               

cUse::[CmdParam]->IO [Status]
cUse ls 
  = case ls of
    (Path list):_ -> 
        do
          let file = joinWith '/' list
          let opts = defaultHetcatsOpts
          result<- anaLib opts file
          case result of
              Just (name,env) -> 
                  do
                    let l=createAllGoalsList name env
                    return ((Address list):(Env name env):(AllGoals l):[] )
              Nothing ->  
                    return [(OutputErr "Couldn't load the file specified")]
    _       -> return [(OutputErr "Wrong parameter")]    

cDgAllAuto::[Status] -> [Status]
cDgAllAuto arg
   = case arg of
       (Env x y):_   -> let result= automatic x y 
                            newGoalList = createAllGoalsList x result
                        in  (Env x result):(AllGoals newGoalList):[]
       _:l           -> cDgAllAuto l
       []            -> [(OutputErr "Wrong parameter")]

cDgAuto :: ([CmdParam],[Status]) -> [Status]
cDgAuto (param,status)
  = case status of
     (Env ln libEnv):l -> 
         case l of
           (AllGoals allGoals):_ ->
               case param of
                 (Goals ls):_ -> 
                     let ll = getEdgeList $ getGoalList ls allGoals
                         result = automaticFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in (Env ln result):(AllGoals newGoalList):[]
                 _  -> [(OutputErr "Wrong parameters")]
           _:list -> cDgAuto (param, (Env ln libEnv):list)
           _  ->[(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l -> 
         case l of
          (Env ln libEnv):_ -> 
               case param of 
                 (Goals ls):_ ->
                     let ll = getEdgeList $ getGoalList ls allGoals
                         result = automaticFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in (Env ln result):(AllGoals newGoalList):[]
                 _ -> [(OutputErr "Wrong parameters")]
          _:list -> cDgAuto(param, (AllGoals allGoals):list)
          _      -> [(OutputErr "Wrong parameters")]
     _:l       -> cDgAuto (param, l)
     []        -> [(OutputErr "Wrong parameters")]

cDgGlobSubsume::([CmdParam],[Status]) -> [Status]
cDgGlobSubsume (param,status)
  = case status of
     (Env ln libEnv):l  -> 
         case l of 
           (AllGoals allGoals):_ -> 
               case param of
                 (Goals ls):_ -> 
                     let ll = getEdgeList $ getGoalList ls allGoals
                         result = globSubsumeFromList ln ll  libEnv 
                         newGoalList = createAllGoalsList ln result
                     in (Env ln result):(AllGoals newGoalList):[]
                 _            -> [(OutputErr "Wrong parameters")]
           _:ll -> cDgGlobSubsume(param, (Env ln libEnv):ll)
           _    -> [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l -> 
         case l of 
           (Env ln libEnv):_ -> 
               case param of
                 (Goals ls):_ -> 
                     let ll= getEdgeList $ getGoalList ls allGoals
                         result = globSubsumeFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in (Env ln result):(AllGoals newGoalList):[]
                 _   -> [(OutputErr "Wrong parameters")]
           _:ll -> cDgGlobSubsume(param, (AllGoals allGoals):ll)
           _    -> [(OutputErr "Wrong parameters")]
     _:l  -> cDgGlobSubsume (param,l)
     []   -> [(OutputErr "Wrong parameters")]



cDgAllGlobSubsume::[Status] -> [Status]
cDgAllGlobSubsume arg
  = case arg of
     (Env x y):_  -> 
       let result =(globSubsume x) y 
           newGoalList = createAllGoalsList x result
       in  (Env x result):(AllGoals newGoalList):[]
     _:l          -> cDgAllGlobSubsume l
     []           -> [(OutputErr "Wrong parameters")]

cDgAllGlobDecomp::[Status] -> [Status]
cDgAllGlobDecomp arg 
  = case arg of 
     (Env x y):_ -> 
       let result= (globDecomp x) y 
           newGoalList = createAllGoalsList x result
       in  (Env x result):(AllGoals newGoalList):[]
     _:l         -> cDgAllGlobDecomp l
     []          -> [(OutputErr "Wrong parameters")]


cDgGlobDecomp :: ([CmdParam],[Status]) -> [Status]
cDgGlobDecomp (param,status) 
  = case status of
     (Env ln libEnv):l  -> 
        case l of 
          (AllGoals allGoals):_ -> 
              case param of
                (Goals ls):_ -> 
                      let ll = getEdgeList $ getGoalList ls allGoals
                          result = globDecompFromList ln ll  libEnv 
                          newGoalList = createAllGoalsList ln result
                      in  (Env ln result):(AllGoals newGoalList):[]
                _   -> [(OutputErr "Wrong parameters")]
          _:list -> cDgGlobDecomp(param, (Env ln libEnv):list)
          _      -> [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l -> 
        case l of 
          (Env ln libEnv):_ -> 
              case param of
                (Goals ls):_ -> 
                      let ll= getEdgeList $ getGoalList ls allGoals
                          result = globDecompFromList ln ll libEnv
                          newGoalList = createAllGoalsList ln result
                      in  (Env ln result):(AllGoals newGoalList):[]
                _  -> [(OutputErr "Wrong parameters")]
          _:list -> cDgGlobDecomp(param, (AllGoals allGoals):list)
          _      -> [(OutputErr "Wrong parameters")]
     _:l                -> cDgGlobDecomp (param,l)
     []                 -> [(OutputErr "Wrong parameters")]


cDgAllLocInfer::[Status] -> [Status]
cDgAllLocInfer arg
  = case arg of
      (Env x y):_ -> let result= (localInference x) y
                         newGoalList = createAllGoalsList x result 
                     in  (Env x result):(AllGoals newGoalList):[]
      _:l         -> cDgAllLocInfer l
      []          -> [(OutputErr "Wrong parameters")]


cDgLocInfer::([CmdParam],[Status]) -> [Status]
cDgLocInfer (param,status)
  = case status of
      (Env ln libEnv):l  -> 
          case l of 
            (AllGoals allGoals):_ ->
                 case param of
                  (Goals ls):_ -> 
                      let ll = getEdgeList $ getGoalList ls allGoals
                          result = localInferenceFromList ln ll  libEnv 
                          newGoalList = createAllGoalsList ln result
                      in (Env ln result):(AllGoals newGoalList):[]
                  _   -> [(OutputErr "Wrong parameters")]
            _:list -> cDgLocInfer(param, (Env ln libEnv):list)
            _      -> [(OutputErr "Wrong parameters")]
      (AllGoals allGoals):l -> 
          case l of 
            (Env ln libEnv):_ -> 
                case param of
                 (Goals ls):_ ->
                     let ll= getEdgeList $ getGoalList ls allGoals
                         result = localInferenceFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in (Env ln result):(AllGoals newGoalList):[]
                 _    -> [(OutputErr "Wrong parameters")]
            _:list -> cDgLocInfer(param, (AllGoals allGoals):list)
            _      -> [(OutputErr "Wrong parameters")]
      _:l    -> cDgLocInfer (param,l)
      []     -> [(OutputErr "Wrong parameters")]


cDgAllLocDecomp::[Status] -> [Status]
cDgAllLocDecomp arg
  = case arg of 
     (Env x y):_ -> 
           let result= (locDecomp x) y 
               newGoalList = createAllGoalsList x result
           in  (Env x result):(AllGoals newGoalList):[]
     _:l         -> cDgAllLocDecomp l
     []          -> [(OutputErr "Wrong parameters")]


cDgLocDecomp::([CmdParam], [Status])-> [Status]
cDgLocDecomp (param,status)
  = case status of
     (Env ln libEnv):l  -> 
        case l of 
          (AllGoals allGoals):_ -> 
               case param of
                 (Goals ls):_ -> 
                      let ll = getEdgeList $ getGoalList ls allGoals
                          result = locDecompFromList ln ll  libEnv 
                          newGoalList = createAllGoalsList ln result
                      in (Env ln result):(AllGoals newGoalList):[]
                 _  -> [(OutputErr "Wrong parameters")]
          _:list -> cDgLocDecomp(param, (Env ln libEnv):list)
          _      -> [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l -> 
        case l of 
          (Env ln libEnv):_ -> 
               case param of
                    (Goals ls):_ -> 
                       let ll= getEdgeList $ getGoalList ls allGoals
                           result = locDecompFromList ln ll libEnv
                           newGoalList = createAllGoalsList ln result
                       in (Env ln result):(AllGoals newGoalList):[]
                    _  -> [(OutputErr "Wrong parameters")]
          _:list -> cDgLocDecomp(param, (AllGoals allGoals):list)
          _      -> [(OutputErr "Wrong parameters")]
     _:l            -> cDgLocDecomp (param,l)
     []             -> [(OutputErr "Wrong parameters")]



cDgComp::([CmdParam], [Status]) -> [Status]
cDgComp (param, status)
  = case status of
      (Env ln libEnv):l  -> 
          case l of 
            (AllGoals allGoals):_ -> 
              case param of
                 (Goals ls):_ -> 
                     let ll = getEdgeList $ getGoalList ls allGoals
                         result = compositionFromList ln ll  libEnv 
                         newGoalList = createAllGoalsList ln result
                     in (Env ln result):(AllGoals newGoalList):[]
                 _ -> [(OutputErr "Wrong parameters")]
            _:list -> cDgComp(param, (Env ln libEnv):list)
            _      -> [(OutputErr "Wrong parameters")]
      (AllGoals allGoals):l -> 
         case l of 
           (Env ln libEnv):_ -> 
              case param of
                 (Goals ls):_ -> 
                     let ll= getEdgeList $ getGoalList ls allGoals
                         result = compositionFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in (Env ln result):(AllGoals newGoalList):[]
                 _    -> [(OutputErr "Wrong parameters")]
           _:list -> cDgComp(param, (AllGoals allGoals):list)
           _      -> [(OutputErr "Wrong parameters")]
      _:l                -> cDgComp (param,l)
      []                 -> [(OutputErr "Wrong parameters")]




cDgAllComp::[Status] -> [Status]
cDgAllComp arg 
  = case arg of
     (Env x y):_ -> 
         let result= (composition x) y 
             newGoalList = createAllGoalsList x result
         in  (Env x result):(AllGoals newGoalList):[]
     _:l         -> cDgAllComp l
     []          -> [(OutputErr "Wrong parameters")]


cDgCompNew::([CmdParam],[Status]) -> [Status]
cDgCompNew (param, status)
 = case status of
    (Env ln libEnv):l  -> 
      case l of 
       (AllGoals allGoals):_ -> 
         case param of
          (Goals ls):_ -> 
            let ll = getEdgeList $ getGoalList ls allGoals
                result = compositionCreatingEdgesFromList ln ll libEnv
                newGoalList = createAllGoalsList ln result
            in (Env ln result):(AllGoals newGoalList):[]
          _   -> [(OutputErr "Wrong parameters")]
       _:list -> cDgCompNew(param, (Env ln libEnv):list)
       _      -> [(OutputErr "Wrong parameters")]
    (AllGoals allGoals):l -> 
       case l of 
        (Env ln libEnv):_ -> 
           case param of
            (Goals ls):_ -> 
              let ll= getEdgeList $ getGoalList ls allGoals
                  result = compositionCreatingEdgesFromList ln ll libEnv
                  newGoalList = createAllGoalsList ln result
              in (Env ln result):(AllGoals newGoalList):[]
            _  -> [(OutputErr "Wrong parameters")]
        _:list -> cDgCompNew(param, (AllGoals allGoals):list)
        _      -> [(OutputErr "Wrong parameters")]
    _:l                -> cDgCompNew (param,l)
    []                 -> [(OutputErr "Wrong parameters")]


 

cDgAllCompNew::[Status] -> [Status]
cDgAllCompNew arg
 = case arg of
    (Env x y):_ -> 
       let result=(compositionCreatingEdges x) y
           newGoalList = createAllGoalsList x result
       in  (Env x result):(AllGoals newGoalList):[]
    _:l         -> cDgAllCompNew l
    []          -> [(OutputErr "Wrong parameters")]

cDgHideThm::([CmdParam],[Status]) -> [Status]
cDgHideThm (param, status)
 = case status of
    (Env ln libEnv):l  -> 
       case l of 
        (AllGoals allGoals):_ -> 
          case param of
            (Goals ls):_ -> 
               let ll = getEdgeList $ getGoalList ls allGoals
                   result = automaticHideTheoremShiftFromList ln ll  libEnv
                   newGoalList = createAllGoalsList ln result
               in (Env ln result):(AllGoals newGoalList):[]
            _   -> [(OutputErr "Wrong parameters")]
        _:list -> cDgHideThm(param, (Env ln libEnv):list)
        _      -> [(OutputErr "Wrong parameters")]
    (AllGoals allGoals):l -> 
       case l of 
        (Env ln libEnv):_ -> 
           case param of
             (Goals ls):_ -> 
                let ll= getEdgeList $ getGoalList ls allGoals
                    result = automaticHideTheoremShiftFromList ln ll libEnv
                    newGoalList = createAllGoalsList ln result
                in (Env ln result):(AllGoals newGoalList):[]
             _   -> [(OutputErr "Wrong parameters")]
        _:list -> cDgHideThm(param, (AllGoals allGoals):list)
        _      -> [(OutputErr "Wrong parameters")]
    _:l        -> cDgHideThm (param,l)
    []         -> [(OutputErr "Wrong parameters")]



cDgAllHideThm::[Status] -> [Status]
cDgAllHideThm arg
  = case arg of
     (Env x y):_ -> 
        let result= (automaticHideTheoremShift x) y 
            newGoalList = createAllGoalsList x result
        in  (Env x result):(AllGoals newGoalList):[]
     _:l         -> cDgAllHideThm l
     []          -> [(OutputErr "Wrong parameters")]

cDgAllThmHide::[Status] -> [Status]
cDgAllThmHide arg
  = case arg of
     (Env x y):_ -> 
        let result=(theoremHideShift x) y 
            newGoalList = createAllGoalsList x result
        in  (Env x result):(AllGoals newGoalList):[]
     _:l         -> cDgAllThmHide l
     []          -> [(OutputErr "Wrong parameters")]


cDgAllInferBasic::[Status] -> [Status]
cDgAllInferBasic arg
 = case arg of
    (AllGoals allGoals):_ -> [Selected allGoals] 
    _:l         -> cDgAllInferBasic l
    []          -> [(OutputErr "Wrong parameters")]



cDgInferBasic::([CmdParam],[Status]) -> [Status]
cDgInferBasic (param, status)
  = case status of
     (AllGoals allGoals):_ -> 
       case param of
        (Goals ls):_ -> let ll = getGoalList ls allGoals
                        in  (Selected ll):[] 
        _            -> [(OutputErr "Wrong parameters")]
     _:l               -> cDgInferBasic (param, l)
     []                -> [(OutputErr "Wrong parameters")]
                                        

cTranslate::([CmdParam],[Status]) -> [Status]
cTranslate (param, _)
      = case param of
                 (ParsedComorphism ls):_ -> [(Comorph ls)] 
                 _                       -> [(OutputErr "Wrong parameters")]

cProver::([CmdParam],[Status]) -> [Status]
cProver (param, _)
       = case param of
                 (UseProver ls ):_      -> [(Prover ls)]
                 _                   -> [(OutputErr "Wrong parameters")]

cShowDgGoals::[Status]-> IO()
cShowDgGoals  arg
  = do
     case arg of
       (AllGoals allGoals):_ -> 
         printNodeInfoFromList allGoals--putStr ("Goals:" ++ (show allGoals))
       _:l -> cShowDgGoals l
       []  -> putStr "Error, no goal list found!\n "


cShowTheory::[Status] -> IO()
cShowTheory arg
  = case arg of 
     (AllGoals allGoals):_ -> printNodeTheoryFromList allGoals
     _:l                        -> cShowNodeTheory l
     []                         -> putStr "Error, no goal list found ! \n"


cShowNodeTheory::[Status] -> IO()
cShowNodeTheory arg
  = case arg of 
     (Selected xx):_ -> printNodeTheoryFromList xx 
     _:l                        -> cShowNodeTheory l
     []                         -> putStr "Error, no nodes selected ! \n"

cShowNodeInfo :: [Status] -> IO()
cShowNodeInfo arg
  = case arg of
     (Selected xx):_ -> printNodeInfoFromList xx
     _:l             -> cShowNodeInfo l
     []              -> putStr "Error, no nodes selected ! \n"

cShowNodeConcept :: [Status] -> IO()
cShowNodeConcept arg
  = case arg of 
     (Selected xx):_ -> printNodeTaxonomyFromList KConcept xx
     _:l             -> cShowNodeConcept l
     []              -> putStr "Error, no nodes selected ! \n"

cShowNodeTaxonomy ::[Status] -> IO()
cShowNodeTaxonomy arg
  = case arg of
     (Selected xx):_ -> printNodeTaxonomyFromList KSubsort xx
     _:l             -> cShowNodeTaxonomy l
     []              -> putStr "Error, no nodes selected !\n"


cProveAll :: [Status]->IO [Status]
cProveAll arg =
  case arg of
    (Env ln libEnv):l -> 
       case l of
         (AllGoals ls):_ -> 
            do 
              result <- proveNodes ls ln libEnv
              let newGoalList = createAllGoalsList ln result
              return  ((AllGoals newGoalList):(Env ln result):[])
         _:ll                 -> cProveAll ((Env ln libEnv):ll)
         _                    -> return [OutputErr "Wrong parameters"]
    (AllGoals ls):l -> 
       case l of
         (Env ln libEnv):_ -> 
            do
              result <- proveNodes ls ln libEnv
              let newGoalList = createAllGoalsList ln result
              return  ((AllGoals newGoalList):(Env ln result):[])
         _:ll              -> cProveAll ((AllGoals ls):ll)
         _                 -> return [OutputErr "Wrong parameters"]
    _:l                -> cProveAll l
    _                  -> return [OutputErr "Wrong parameters"]
