{-# OPTIONS -cpp #-}
{- |
Module      :$Header$
Description : Execution of Hets commands (for command line interface)
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Function that executes the script commands together with the datatypes used.
Even though there is a scanning Path function created with parsec it is not
used, instead shellac is used so that autocomplition for path can be enabled
-}
{-
 TODO :
      - add comments
      - implement the rest of the functions
      - delete the test function

-}

module PGIP.Commands where

import Static.AnalysisLibrary
import Static.DevGraph

import Driver.Options

import Proofs.Automatic
import Proofs.Global
import Proofs.Local
import Proofs.Composition
import Proofs.HideTheoremShift
import Proofs.TheoremHideShift

import PGIP.Common
import PGIP.Utils

import Common.Utils
import Common.AnnoState
import Common.Lexer
import Common.Taxonomy
import Common.Result

import Comorphisms.LogicGraph
import Logic.Grothendieck

import Proofs.InferBasic

import Text.ParserCombinators.Parsec
import Data.Graph.Inductive.Graph
import Data.Maybe
import Data.Char


#ifdef UNI_PACKAGE
import GUI.ShowGraph
#endif

-- | Scans a word contained in a path
scanPathFile::CharParser st String
scanPathFile
     = many1 $ satisfy isPathChar

isPathChar :: Char -> Bool
isPathChar c = isAlphaNum c || elem c ['-','_','.']

scanAnyWord::CharParser st String
scanAnyWord
     = many1 $ satisfy isPathChar <|> prime

-- | the 'getPath' function reads a path as a list of words
getPath::AParser st String
getPath
        = try ( do
                    v<-sepBy1 scanPathFile (string "/")
                    let result = joinWith '/' v
                    return result
              )
      <|>
          try ( do  skip
                    v<-sepBy1 scanPathFile (string "/")
                    let result = joinWith '/' v
                    return result
              )
      <?>
          "path"

-- | the 'getKeyWord' function takes an argument string and tries to read it
getKeyWord::String -> AParser st String
getKeyWord wd
              =  try ( string wd
                     )
              <|>
                 try ( do  skip
                           string wd
                     )
              <?> ("keyword "++wd)

-- | The function 'getGoal' parses a goal (node, edge or labeled edge)
getGoal::AParser st GOAL
getGoal
       = try ( do  v1<-scanAnyWord
                   try (skip)
                   getKeyWord "-"
                   try (skip)
                   v2<-getNumber
                   try (skip)
                   getKeyWord "->"
                   try (skip)
                   v3<-scanAnyWord
                   try (skip)
                   return (LabeledEdge v1 (read v2::Int) v3)
             )
      <|>
         try ( do  v1<-scanAnyWord
                   try (skip)
                   getKeyWord "->"
                   try (skip)
                   v2<-scanAnyWord
                   try (skip)
                   return (Edge  v1  v2)
             )
      <|>
         try ( do  v<-scanAnyWord
                   try (skip)
                   return (Node  v)
             )
      <?>
         "goal"
-- | The function 'getScript' tries to read some script commands
-- It is not ready yet to work with shellac !
getScript::AParser st String
getScript
         = try ( do  getKeyWord "end-script"
                     try (skip)
                     return ""
               )
        <|>
           try ( do  v<-scanAnyWord
                     vs <-getScript
                     return (v++" "++vs)
               )
        <|>
           try ( do  skip
                     v<-scanAnyWord
                     vs<-getScript
                     return (v++" "++vs)
               )
        <?>
           "some prover script"

-- | The function 'getComorphism' reads a comorphism as a list of Ids
getComorphism::AParser st [String]
getComorphism
             = try ( do  v<-scanAnyWord
                         try (skip)
                         getKeyWord ";"
                         try (skip)
                         vs <-getComorphism
                         return ( v:vs)
                   )
            <|>
               try ( do  v<-scanAnyWord
                         return [ v]
                   )
            <?>
               " list of ID's separated by semicolon"

-- | The function 'scanCommand' given a list of string describing what
-- kind of parameters to expect tries to parse them and returns a
-- CmdParam list with the parsed parameters
scanCommand::[String] -> AParser st [CmdParam]
scanCommand arg
               = case arg of
                          []  ->  do
                                 string ""
                                 return []
--- scanning a path
                          "PATH":ls  ->  do
                                 v <- getPath
                                 vs<- scanCommand ls
                                 return ((Path v):vs)
--- scanning a prover
                          "PROVER":ls  ->  do
                                 v <- scanAnyWord
                                 vs<- scanCommand ls
                                 return ((UseProver v):vs)
--- scanning a formula
                          "FORMULA":ls  ->  do
                                 v <- scanAnyWord
                                 vs<- scanCommand ls
                                 return ((Formula  v):vs)
--- scanning a comorphism
                          "COMORPHISM":ls  ->  do
                                 v <- getComorphism
                                 vs<-scanCommand ls
                                 return ((ParsedComorphism v):vs)
--- scanning goals
                          "GOALS":ls  ->  do
                                 v<-many getGoal
--                                 v<- getGoal
                                 vs<- scanCommand ls
                                 return ((Goals v):vs)
--- scanning none or many formulas
                          "FORMULA-STAR":ls  ->  do
                                 v<- many ( do  tmp<-scanAnyWord
                                                return  tmp
                                          )
                                 vs<-scanCommand ls
                                 return  ((Formulas v):vs)
--- scanning one or more formula
                          "FORMULA-PLUS":ls  ->  do
                                 v<- many1 ( do  tmp<-scanAnyWord
                                                 return tmp
                                           )
                                 vs<-scanCommand ls
                                 return ((Formulas v):vs)
--- scanning proof script
                          "PROOF-SCRIPT":ls  ->  do
                                 v<- getScript
                                 vs <-scanCommand ls
                                 return ((ProofScript v):vs)
--- scanning keywords
                          keyword:ls  ->  do
                                 getKeyWord keyword
                                 vs<- scanCommand ls
                                 return vs



-- | A test function to use with shellac for the non-implemented commands
-- should be deleted when all commands are implemented
test::String->[Status] 
             -> IO [Status]
test ls _
  = do
      putStrLn $ show ls
      return []

-- | It seems that the way shellac reads the file path it adds an extra blank
-- at the end that needs to be removed
removeSpace :: String -> String
removeSpace ls
  = case ls of
      []   -> []
      ' ':[] -> []
      x:[]   -> x:[]
      x:l  -> x:(removeSpace l)

-- | Loads a list of libraries and returns the status of the
-- interpreter after those libraries were loaded
getStatus ::[String] ->[Status]
                          -> IO [Status]
getStatus files state
 = case files of
       []  -> do
               return state
       f:l -> do
              result <- cUse f state
              nwState <- update result state
              getStatus l nwState


-- | The function 'cUse' implements the command Use, i.e. given a path it
-- tries to load the library at that path
cUse::String->[Status] 
               -> IO [Status]
cUse input state
 = case state of
    (Env _ libEnv):_ ->
       do
        let file = removeSpace input
        let opts = defaultHetcatsOpts
        result <- anaLibExt opts file libEnv
        case result of
          Just (name , env) ->
              do
                let l= createAllGoalsList name env
                return ((Address file):(Env name env):(AllGoals l):[])
          Nothing -> do
              putStr "Couldn't load the new file!\n"
              return []
    _:list -> cUse input list
    [] ->do
          let file = removeSpace input
          let opts = defaultHetcatsOpts
          result<- anaLib opts file
          case result of
              Just (name,env) ->
                  do
                    let l=createAllGoalsList name env
                    return ((Address file):(Env name env):(AllGoals l):[] )
              Nothing ->
                    return [(OutputErr "Couldn't load the file specified")]


-- | The function 'cDgAllAuto' tries to implement the command dg-all auto
cDgAllAuto::String -> [Status] 
                     -> IO [Status]
cDgAllAuto _ arg
   = case arg of
       (Env x y):_   -> let result= automatic x y
                            newGoalList = createAllGoalsList x result
                        in  return ((Env x result):(AllGoals newGoalList):[])
       _:l           -> cDgAllAuto "" l
       []            -> return ([(OutputErr "Wrong parameter")])

-- | The 'cDgAuto' function implements dg auto, note that the parameters
-- are passed as string and parsed inside this function. All the other
-- function are implemented in the same manner
cDgAuto :: String -> [Status] 
                   -> IO [Status]
cDgAuto input status
 = do
    let r= runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
    case r of
     Left _ -> do
                putStr "Error parsing the goal list ! \n"
                return []
     Right param ->
      do
       case status of
        (Env ln libEnv):l ->
         case l of
           (AllGoals allGoals):_ ->
               case param of
                 (Goals ls):_ -> do
                     let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                     list <- getGoalList ls allGoals allNodes
                     let ll = getEdgeList list
                     let result = automaticFromList ln ll libEnv
                     let newGoalList = createAllGoalsList ln result
                     return ((Env ln result):(AllGoals newGoalList):[])
                 _  -> return ([(OutputErr "Wrong parameters")])
           _:list -> cDgAuto input ((Env ln libEnv):list)
           _  ->return ([(OutputErr "Wrong parameters")])
        (AllGoals allGoals):l ->
         case l of
          (Env ln libEnv):_ ->
               case param of
                 (Goals ls):_ -> do
                     let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                     list <-getGoalList ls allGoals allNodes
                     let ll = getEdgeList list
                     let result = automaticFromList ln ll libEnv
                     let newGoalList = createAllGoalsList ln result
                     return ((Env ln result):(AllGoals newGoalList):[])
                 _ -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgAuto input ((AllGoals allGoals):list)
          _      -> return [(OutputErr "Wrong parameters")]
        _:l       -> cDgAuto input l
        []        -> return [(OutputErr "Wrong parameters")]

cDgGlobSubsume::String -> [Status] 
                         -> IO [Status]
cDgGlobSubsume input status
 =do
   let r = runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
   case r of
    Left _ -> do
               putStr "Error parsing the goal list ! \n"
               return []
    Right param ->
     do
      case status of
       (Env ln libEnv):l  ->
         case l of
           (AllGoals allGoals):_ ->
               case param of
                 (Goals ls):_ -> do
                     let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                     list <- getGoalList ls allGoals allNodes
                     let ll = getEdgeList list
                     let result = globSubsumeFromList ln ll  libEnv
                     let newGoalList = createAllGoalsList ln result
                     return ((Env ln result):(AllGoals newGoalList):[])
                 _            ->return  [(OutputErr "Wrong parameters")]
           _:ll -> cDgGlobSubsume input ((Env ln libEnv):ll)
           _    -> return [(OutputErr "Wrong parameters")]
       (AllGoals allGoals):l ->
         case l of
           (Env ln libEnv):_ ->
               case param of
                 (Goals ls):_ -> do
                     let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                     list <- getGoalList ls allGoals allNodes
                     let ll= getEdgeList list
                     let result = globSubsumeFromList ln ll libEnv
                     let newGoalList = createAllGoalsList ln result
                     return ((Env ln result):(AllGoals newGoalList):[])
                 _   -> return [(OutputErr "Wrong parameters")]
           _:ll -> cDgGlobSubsume input ((AllGoals allGoals):ll)
           _    -> return [(OutputErr "Wrong parameters")]
       _:l  -> cDgGlobSubsume input l
       []   -> return [(OutputErr "Wrong parameters")]



cDgAllGlobSubsume::String -> [Status] 
                            -> IO [Status]
cDgAllGlobSubsume _ arg
  = case arg of
     (Env x y):_  ->
       let result =(globSubsume x) y
           newGoalList = createAllGoalsList x result
       in  return ((Env x result):(AllGoals newGoalList):[])
     _:l          -> cDgAllGlobSubsume "" l
     []           -> return [(OutputErr "Wrong parameters")]

cDgAllGlobDecomp::String -> [Status] 
                           -> IO [Status]
cDgAllGlobDecomp _ arg
  = case arg of
     (Env x y):_ ->
       let result= (globDecomp x) y
           newGoalList = createAllGoalsList x result
       in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllGlobDecomp "" l
     []          -> return [(OutputErr "Wrong parameters")]


cDgGlobDecomp :: String -> [Status] 
                           -> IO [Status]
cDgGlobDecomp input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):l  ->
        case l of
          (AllGoals allGoals):_ ->
              case param of
                (Goals ls):_ -> do
                      let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                      list <- getGoalList ls allGoals allNodes
                      let ll = getEdgeList list
                      let result = globDecompFromList ln ll  libEnv
                      let newGoalList = createAllGoalsList ln result
                      return ((Env ln result):(AllGoals newGoalList):[])
                _   -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgGlobDecomp input  ((Env ln libEnv):list)
          _      -> return [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l ->
        case l of
          (Env ln libEnv):_ ->
              case param of
                (Goals ls):_ -> do
                      let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                      list <- getGoalList ls allGoals allNodes
                      let ll= getEdgeList list
                      let result = globDecompFromList ln ll libEnv
                      let newGoalList = createAllGoalsList ln result
                      return ((Env ln result):(AllGoals newGoalList):[])
                _  -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgGlobDecomp input ((AllGoals allGoals):list)
          _      -> return [(OutputErr "Wrong parameters")]
     _:l                -> cDgGlobDecomp input l
     []                 -> return [(OutputErr "Wrong parameters")]


cDgAllLocInfer::String -> [Status] 
                          -> IO [Status]
cDgAllLocInfer _ arg
  = case arg of
      (Env x y):_ -> let result= (localInference x) y
                         newGoalList = createAllGoalsList x result
                     in  return ((Env x result):(AllGoals newGoalList):[])
      _:l         -> cDgAllLocInfer "" l
      []          -> return [(OutputErr "Wrong parameters")]


cDgLocInfer::String -> [Status] 
                       -> IO [Status]
cDgLocInfer input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "Error parsing the goal list ! \n"
              return []
   Right param ->
     case status of
      (Env ln libEnv):l  ->
          case l of
            (AllGoals allGoals):_ ->
                 case param of
                  (Goals ls):_ -> do
                      let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                      list <- getGoalList ls allGoals allNodes
                      let ll = getEdgeList list
                      let result = localInferenceFromList ln ll  libEnv
                      let newGoalList = createAllGoalsList ln result
                      return ((Env ln result):(AllGoals newGoalList):[])
                  _   -> return [(OutputErr "Wrong parameters")]
            _:list -> cDgLocInfer input ((Env ln libEnv):list)
            _      -> return [(OutputErr "Wrong parameters")]
      (AllGoals allGoals):l ->
          case l of
            (Env ln libEnv):_ ->
                case param of
                 (Goals ls):_ -> do
                     let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                     list <- getGoalList ls allGoals allNodes
                     let ll= getEdgeList list
                     let result = localInferenceFromList ln ll libEnv
                     let newGoalList = createAllGoalsList ln result
                     return ((Env ln result):(AllGoals newGoalList):[])
                 _    -> return [(OutputErr "Wrong parameters")]
            _:list -> cDgLocInfer input ((AllGoals allGoals):list)
            _      -> return [(OutputErr "Wrong parameters")]
      _:l    -> cDgLocInfer input l
      []     -> return [(OutputErr "Wrong parameters")]


cDgAllLocDecomp::String -> [Status] 
                           ->IO [Status]
cDgAllLocDecomp _ arg =
  case arg of
     (Env x y):_ ->
           let result= (locDecomp x) y
               newGoalList = createAllGoalsList x result
           in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllLocDecomp "" l
     []          -> return [(OutputErr "Wrong parameters")]


cDgLocDecomp::String-> [Status]
                        ->IO [Status]
cDgLocDecomp input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):l  ->
        case l of
          (AllGoals allGoals):_ ->
               case param of
                 (Goals ls):_ -> do
                      let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                      list <- getGoalList ls allGoals allNodes
                      let ll = getEdgeList list
                      let result = locDecompFromList ln ll  libEnv
                      let newGoalList = createAllGoalsList ln result
                      return ((Env ln result):(AllGoals newGoalList):[])
                 _  -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgLocDecomp input  ((Env ln libEnv):list)
          _      -> return [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l ->
        case l of
          (Env ln libEnv):_ ->
               case param of
                    (Goals ls):_ -> do
                       let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                       list <- getGoalList ls allGoals allNodes
                       let ll= getEdgeList list
                       let result = locDecompFromList ln ll libEnv
                       let newGoalList = createAllGoalsList ln result
                       return ((Env ln result):(AllGoals newGoalList):[])
                    _  -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgLocDecomp input ((AllGoals allGoals):list)
          _      -> return [(OutputErr "Wrong parameters")]
     _:l            -> cDgLocDecomp input l
     []             -> return [(OutputErr "Wrong parameters")]



cDgComp::String -> [Status] 
                   -> IO [Status]
cDgComp input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
      (Env ln libEnv):l  ->
          case l of
            (AllGoals allGoals):_ ->
              case param of
                 (Goals ls):_ -> do
                     let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                     list <- getGoalList ls allGoals allNodes
                     let ll = getEdgeList list
                     let result = compositionFromList ln ll  libEnv
                     let newGoalList = createAllGoalsList ln result
                     return ((Env ln result):(AllGoals newGoalList):[])
                 _ -> return [(OutputErr "Wrong parameters")]
            _:list -> cDgComp input  ((Env ln libEnv):list)
            _      -> return [(OutputErr "Wrong parameters")]
      (AllGoals allGoals):l ->
         case l of
           (Env ln libEnv):_ ->
              case param of
                 (Goals ls):_ -> do
                     let allNodes = convToGoal $
                                     labNodes (lookupDGraph ln libEnv)
                     list <-getGoalList ls allGoals allNodes
                     let ll= getEdgeList list
                     let result = compositionFromList ln ll libEnv
                     let newGoalList = createAllGoalsList ln result
                     return ((Env ln result):(AllGoals newGoalList):[])
                 _    -> return [(OutputErr "Wrong parameters")]
           _:list -> cDgComp input ((AllGoals allGoals):list)
           _      -> return [(OutputErr "Wrong parameters")]
      _:l                -> cDgComp input l
      []                 -> return [(OutputErr "Wrong parameters")]




cDgAllComp::String -> [Status] 
                       ->IO [Status]
cDgAllComp _ arg
  = case arg of
     (Env x y):_ ->
         let result= (composition x) y
             newGoalList = createAllGoalsList x result
         in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllComp "" l
     []          -> return [(OutputErr "Wrong parameters")]


cDgCompNew::String -> [Status] 
                     ->IO [Status]
cDgCompNew input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):l  ->
      case l of
       (AllGoals allGoals):_ ->
         case param of
          (Goals ls):_ -> do
            let allNodes = convToGoal $
                       labNodes (lookupDGraph ln libEnv)
            list <- getGoalList ls allGoals allNodes
            let ll = getEdgeList list
            let result = compositionCreatingEdgesFromList ln ll libEnv
            let newGoalList = createAllGoalsList ln result
            return ((Env ln result):(AllGoals newGoalList):[])
          _   -> return [(OutputErr "Wrong parameters")]
       _:list -> cDgCompNew input ((Env ln libEnv):list)
       _      -> return [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l ->
       case l of
        (Env ln libEnv):_ ->
           case param of
            (Goals ls):_ -> do
              let allNodes = convToGoal $
                         labNodes (lookupDGraph ln libEnv)
              list <- getGoalList ls allGoals allNodes
              let ll= getEdgeList list
              let result = compositionCreatingEdgesFromList ln ll libEnv
              let newGoalList = createAllGoalsList ln result
              return ((Env ln result):(AllGoals newGoalList):[])
            _  -> return [(OutputErr "Wrong parameters")]
        _:list -> cDgCompNew input ((AllGoals allGoals):list)
        _      -> return [(OutputErr "Wrong parameters")]
     _:l                -> cDgCompNew input l
     []                 -> return [(OutputErr "Wrong parameters")]




cDgAllCompNew::String -> [Status] 
                        ->IO [Status]
cDgAllCompNew _ arg
 = case arg of
    (Env x y):_ ->
       let result=(compositionCreatingEdges x) y
           newGoalList = createAllGoalsList x result
       in  return ((Env x result):(AllGoals newGoalList):[])
    _:l         -> cDgAllCompNew "" l
    []          -> return [(OutputErr "Wrong parameters")]

cDgHideThm::String -> [Status] 
                     ->IO [Status]
cDgHideThm input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):l  ->
       case l of
        (AllGoals allGoals):_ ->
          case param of
            (Goals ls):_ -> do
               let allNodes = convToGoal $
                        labNodes (lookupDGraph ln libEnv)
               list <- getGoalList ls allGoals allNodes
               let ll = getEdgeList list
               let result = automaticHideTheoremShiftFromList ln ll  libEnv
               let newGoalList = createAllGoalsList ln result
               return ((Env ln result):(AllGoals newGoalList):[])
            _   -> return [(OutputErr "Wrong parameters")]
        _:list -> cDgHideThm input ((Env ln libEnv):list)
        _      -> return [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l ->
       case l of
        (Env ln libEnv):_ ->
           case param of
             (Goals ls):_ -> do
                let allNodes = convToGoal $
                           labNodes (lookupDGraph ln libEnv)
                list <- getGoalList ls allGoals allNodes
                let ll= getEdgeList list
                let result = automaticHideTheoremShiftFromList ln ll libEnv
                let newGoalList = createAllGoalsList ln result
                return ((Env ln result):(AllGoals newGoalList):[])
             _   -> return [(OutputErr "Wrong parameters")]
        _:list -> cDgHideThm input ((AllGoals allGoals):list)
        _      -> return [(OutputErr "Wrong parameters")]
     _:l        -> cDgHideThm input l
     []         -> return [(OutputErr "Wrong parameters")]



cDgAllHideThm::String -> [Status] 
                          ->IO [Status]
cDgAllHideThm _ arg
  = case arg of
     (Env x y):_ ->
        let result= (automaticHideTheoremShift x) y
            newGoalList = createAllGoalsList x result
        in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllHideThm "" l
     []          -> return [(OutputErr "Wrong parameters")]

cDgAllThmHide::String -> [Status] 
                          ->IO [Status]
cDgAllThmHide _ arg
  = case arg of
     (Env x y):_ ->
        let result=(theoremHideShift x) y
            newGoalList = createAllGoalsList x result
        in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllThmHide "" l
     []          -> return [(OutputErr "Wrong parameters")]


cDgAllInferBasic::String -> [Status] 
                           ->IO [Status]
cDgAllInferBasic _ arg
 = case arg of
    (AllGoals allGoals):_ -> return [Selected allGoals]
    _:l         -> cDgAllInferBasic "" l
    []          -> return [(OutputErr "Wrong parameters")]



cDgInferBasic::String -> [Status] 
                           -> IO [Status]
cDgInferBasic input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "Error parsing the node list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):l ->
      case l of
       (AllGoals allgoals):_ ->
          case param of
            (Goals ls):_ -> do
                         let allNodes = convToGoal $
                               labNodes (lookupDGraph ln libEnv)
                         ll <- getGoalList ls (allgoals ++ allNodes) allNodes
                         return ((Selected ll):[])
            _            -> return [(OutputErr "Wrong parameters")]
       _:ll              -> cDgInferBasic input ((Env ln libEnv):ll)
       []                -> return [(OutputErr "Wrong parameters")]
     (AllGoals allgoals):l ->
      case l of
       (Env ln libEnv):_ ->
           case param of
             (Goals ls):_ -> do
                          let allNodes = convToGoal $
                                labNodes (lookupDGraph ln libEnv)
                          ll <- getGoalList ls (allgoals ++ allNodes) allNodes
                          return ((Selected ll):[])
             _           ->  return [(OutputErr "Wrong parameters")]
       _:ll              -> cDgInferBasic input ((AllGoals allgoals):ll)
       []                -> return [(OutputErr "Wrong parameters")]
     _:l                 -> cDgInferBasic input l
     []                  -> return [(OutputErr "Wrong parameters")]

trimSpace:: String -> String
trimSpace ls
 = case ls of
   ' ':l  -> trimSpace l
   x:l    -> x:(trimSpace l)
   []     -> []

cTranslate::String -> [Status] 
                       -> IO [Status]
cTranslate input _
 = do case lookupComorphism_in_LG (trimSpace input) of
         Result _ (Just smth) -> return [Comorph smth]
         _                    -> return [OutputErr "Wrong parameters"]




decideProver :: String ->[(G_prover,AnyComorphism)] -> IO [Status]
decideProver input ls
 = do
   case ls of
    (x,_):l -> case ((getPName x)== input) of
                 True -> return [SProver x] 
		 False-> decideProver input l
    _       -> return [OutputErr "Wrong parameters"]



	     

cProver::String -> [Status] 
                    ->IO [Status]
cProver input state
 = do
    case solveComorph state of 
       Nothing   -> return [OutputErr "Wrong parameters"]
       Just smth -> decideProver input
                       (getProversCMDLautomatic smth)


cShowDgGoals::String -> [Status]
                        -> IO [Status]
cShowDgGoals  _ arg
 =do
     case arg of
       (AllGoals allGoals):l -> do
             case l of
               (Env x y):_ -> do
                      let dgraph = lookupDGraph x y
                      let allNodes = labNodes dgraph
                      printNamesFromList allGoals allNodes
                      return []
               _:ll -> cShowDgGoals "" ((AllGoals allGoals):ll)
               []   -> do
                        putStr "Error, no library is loaded!\n"
                        return []
       (Env x y):l -> do
             case l of
                (AllGoals allGoals):_ -> do
                      let dgraph = lookupDGraph x y
                      let allNodes = labNodes dgraph
                      printNamesFromList allGoals allNodes
                      return []
                _:ll  -> cShowDgGoals "" ((Env x y):ll)
                [] -> do
                        putStr "Error, no library is loaded! \n"
                        return []
       _:l -> cShowDgGoals "" l
       []  -> do
               putStr "Error, no goal list found!\n"
               return []

cShowTheory::String -> [Status] 
                          -> IO [Status]
cShowTheory _ arg
  = do
     let allGoals = getAllGoals arg
     let comorph = getComorph arg
     case allGoals of
       Nothing -> do
                   putStr "Error, not goal list found ! \n"
		   return []
       Just val -> do
                    printNodeTheoryFromList val comorph
		    return []
  


cShowNodeTheory::String -> [Status] 
                             -> IO [Status]
cShowNodeTheory input arg
 =
  case input of
   "" -> do
          let xx = getSelected arg
          let comorph = getComorph arg
          case xx of
	    Nothing -> do
	                putStr "Error, no nodes selected ! \n"
			return []
	    Just val -> do
	                printNodeTheoryFromList val comorph
			return []
   _ -> do
      let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
      case r of
         Left _ -> do
              putStr "Error parsing the node list ! \n"
              return []
         Right param -> do
	  let t_allGoals = getAllGoals arg
	  let t_ln = getLIB_NAME arg
	  let t_libEnv = getLibEnv arg
	  let comorph = getComorph arg
	  case t_allGoals of
	   Nothing -> do
	               putStr "No library loaded !\n"
		       return []
           Just allGoals ->
	      case t_ln of
	        Nothing -> do
	                putStr "No library loaded !\n"
			return []
	        Just ln ->
	          case t_libEnv of
	           Nothing -> do
	                  putStr "No library loaded !\n"
			  return []
	           Just libEnv ->
                     case param of
                        (Goals ls):_ -> do
                             let allNodes = convToGoal $
                                  labNodes (lookupDGraph ln libEnv)
                             list <- getGoalList ls allNodes allNodes
                             printNodeTheoryFromList list comorph
                             return []
                        _ -> do
                              putStr "Error parsing the node list! \n"
                              return []

cShowInfo :: String -> [Status] 
                         -> IO [Status]
cShowInfo input arg
 =
  case input of
   "" ->
    case arg of
     (Selected xx):l -> do
         case l of
            (Env ln libEnv):_ -> do
                         let allNodes =
                               labNodes (lookupDGraph ln libEnv)
                         printInfoFromList xx allNodes
                         return []
            _:ll -> cShowInfo "" ((Selected xx):ll)
            []   -> do putStr "Error, no library was loaded ! \n"
                       return []
     (Env ln libEnv):l -> do
        case l of
          (Selected xx):_ -> do
                     let nodeList =
                             labNodes (lookupDGraph ln libEnv)
--                     let allNodes = convToGoal nodeList
                     printInfoFromList xx nodeList
                     return []
          _:ll -> cShowInfo "" ((Env ln libEnv):ll)
          []   -> do putStr "Error, no nodes or edges were selected ! \n"
                     return []
     _:l             -> cShowInfo "" l
     []              -> do
                         putStr "Error, no nodes or edges selected ! \n"
                         return []
   _ -> do
      let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
      case r of
         Left _ -> do
              putStr "Error parsing the node list ! \n"
              return []
         Right param -> do
           case arg of
             (AllGoals allGoals):l ->
                case l of
                  (Env ln libEnv):_ ->
                     case param of
                        (Goals ls):_ -> do
                             let nodeList = labNodes (lookupDGraph ln libEnv)
                             let allNodes = convToGoal nodeList
                             list <- getGoalList ls (allGoals++allNodes)
                                     allNodes
                             printInfoFromList list nodeList
                             return []
                        _ -> do
                              putStr "Error parsing the node list! \n"
                              return []
                  _:ll -> cShowInfo input ((AllGoals allGoals):ll)
                  []   -> do
                           putStr "Error, no library loaded ! \n"
                           return []
             (Env ln libEnv):l ->
                 case l of
                   (AllGoals allGoals):_ ->
                       case param of
                          (Goals ls):_ -> do
                               let nodeList = labNodes (lookupDGraph ln libEnv)
                               let allNodes = convToGoal nodeList
                               list <- getGoalList ls (allGoals++allNodes)
                                       allNodes
                               printInfoFromList list nodeList
                               return []
                          _ -> do
                                putStr "Error parsing the node list! \n"
                                return []
                   _:ll -> cShowInfo input ((Env ln libEnv):ll)
                   []    -> do
                             putStr "Error, no library loaded ! \n"
                             return []
             _:l -> cShowInfo input l
             [] -> do putStr "Error, no library loaded ! \n"
                      return []

cShowNodeConcept :: String -> [Status] 
                               -> IO [Status]
cShowNodeConcept input arg
 =
  case input of
   "" ->
    case arg of
     (Selected xx):l -> do
           case l of
              (Env ln libEnv):_ -> do
                         printNodeTaxonomyFromList KConcept xx libEnv ln
                         return []
              _:ll   -> cShowNodeConcept "" ((Selected xx):ll)
              []     -> do
                         putStr "Error, no library loaded !\n"
                         return []
     (Env ln libEnv):l -> do
           case l of
              (Selected xx):_ -> do
                         printNodeTaxonomyFromList KConcept xx libEnv ln
                         return []
              _:ll   -> cShowNodeConcept "" ((Env ln libEnv):ll)
              []     -> do
                         putStr "Error, no nodes selected !\n"
                         return []
     _:l             -> cShowNodeConcept "" l
     []              -> do
                         putStr "Error, no nodes selected ! \n"
                         return []
   _ -> do
    let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
    case r of
      Left _ -> do
         putStr "Error parsing the node list ! \n"
         return []
      Right param->
            case arg of
             (AllGoals allGoals):l ->
                case l of
                  (Env ln libEnv):_ ->
                     case param of
                        (Goals ls):_ -> do
                             let allNodes = convToGoal $
                                  labNodes (lookupDGraph ln libEnv)
                             list <- getGoalList ls allNodes allNodes
                             printNodeTaxonomyFromList KConcept list libEnv ln
                             return []
                        _ -> do
                              putStr "Error parsing the node list! \n"
                              return []
                  _:ll -> cShowNodeConcept input ((AllGoals allGoals):ll)
                  []   -> do
                           putStr "Error, no library loaded ! \n"
                           return []
             (Env ln libEnv):l ->
                 case l of
                   (AllGoals _):_ ->
                       case param of
                          (Goals ls):_ -> do
                            let allNodes = convToGoal $
                                  labNodes (lookupDGraph ln libEnv)
                            list <- getGoalList ls allNodes allNodes
                            printNodeTaxonomyFromList KConcept list libEnv ln
                            return []
                          _ -> do
                                putStr "Error parsing the node list! \n"
                                return []
                   _:ll -> cShowNodeConcept input ((Env ln libEnv):ll)
                   []    -> do
                             putStr "Error, no library loaded ! \n"
                             return []
             _:l -> cShowNodeConcept input l
             [] -> do putStr "Error, no library loaded ! \n"
                      return []

cShowNodeTaxonomy ::String -> [Status] 
                                 -> IO [Status]
cShowNodeTaxonomy input arg
 =
  case input of
   "" ->
    case arg of
     (Selected xx):l -> do
           case l of
              (Env ln libEnv):_ -> do
                         printNodeTaxonomyFromList KSubsort xx libEnv ln
                         return []
              _:ll   -> cShowNodeTaxonomy "" ((Selected xx):ll)
              []     -> do
                         putStr "Error, no library loaded !\n"
                         return []
     (Env ln libEnv):l -> do
           case l of
              (Selected xx):_ -> do
                         printNodeTaxonomyFromList KSubsort xx libEnv ln
                         return []
              _:ll   -> cShowNodeTaxonomy "" ((Env ln libEnv):ll)
              []     -> do
                         putStr "Error, no nodes selected !\n"
                         return []
     _:l             -> cShowNodeTaxonomy "" l
     []              -> do
                         putStr "Error, no nodes selected !\n"
                         return []
   _ -> do
    let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
    case r of
      Left _ -> do
          putStr "Error parsing the node list ! \n"
          return []
      Right param ->
            case arg of
             (AllGoals allGoals):l ->
                case l of
                  (Env ln libEnv):_ ->
                     case param of
                        (Goals ls):_ -> do
                             let allNodes = convToGoal $
                                  labNodes (lookupDGraph ln libEnv)
                             list <- getGoalList ls allNodes allNodes
                             printNodeTaxonomyFromList KSubsort list libEnv ln
                             return []
                        _ -> do
                              putStr "Error parsing the node list! \n"
                              return []
                  _:ll -> cShowNodeTaxonomy input ((AllGoals allGoals):ll)
                  []   -> do
                           putStr "Error, no library loaded ! \n"
                           return []
             (Env ln libEnv):l ->
                 case l of
                   (AllGoals _):_ ->
                       case param of
                          (Goals ls):_ -> do
                             let allNodes = convToGoal $
                                   labNodes (lookupDGraph ln libEnv)
                             list <- getGoalList ls allNodes allNodes
                             printNodeTaxonomyFromList KSubsort list libEnv ln
                             return []
                          _ -> do
                                putStr "Error parsing the node list! \n"
                                return []
                   _:ll -> cShowNodeTaxonomy input ((Env ln libEnv):ll)
                   []    -> do
                             putStr "Error, no library loaded ! \n"
                             return []
             _:l -> cShowNodeTaxonomy input l
             [] -> do putStr "Error, no library loaded ! \n"
                      return []

cEdges :: String -> [Status] 
                        -> IO [Status]
cEdges _ arg =
 case arg of
   (Env ln libEnv):_ -> do
                 printNamesFromList ( convEdgeToGoal (
                     labEdges (lookupDGraph ln libEnv)))
                     (labNodes (lookupDGraph ln libEnv))
                 return []
   _:l -> cEdges "" l
   [] -> do
          putStr "Error, no library loaded ! \n"
          return []



cNodes :: String -> [Status] 
                      -> IO [Status]
cNodes _ arg =
 case arg of
   (Env ln libEnv):_ -> do
            printNamesFromList ( convToGoal (
                      labNodes (lookupDGraph ln libEnv)))
                      (labNodes (lookupDGraph ln libEnv))
            return []
   _:l -> cNodes "" l
   [] -> do
          putStr "Error, no library loaded ! \n"
          return []

cProveAll :: String -> [Status]
                        ->IO [Status]
cProveAll _ arg =
  case arg of
    (Env ln libEnv):l ->
       case l of
         (AllGoals ls):_ ->
            do
              result <- proveNodes ls ln libEnv
              let newGoalList = createAllGoalsList ln result
              return  ((AllGoals newGoalList):(Env ln result):[])
         _:ll                 -> cProveAll "" ((Env ln libEnv):ll)
         _                    -> return [OutputErr "Wrong parameters"]
    (AllGoals ls):l ->
       case l of
         (Env ln libEnv):_ ->
            do
              result <- proveNodes ls ln libEnv
              let newGoalList = createAllGoalsList ln result
              return  ((AllGoals newGoalList):(Env ln result):[])
         _:ll              -> cProveAll "" ((AllGoals ls):ll)
         _                 -> return [OutputErr "Wrong parameters"]
    _:l                -> cProveAll "" l
    _                  -> return [OutputErr "Wrong parameters"]

cViewNodeNumber :: String -> [Status] 
                              -> IO [Status]
cViewNodeNumber input status =
  do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "\n Error parsing the node list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):_ ->
       case param of
        (Goals ls):_ -> do
                         let allNodes = convToGoal $
                               labNodes (lookupDGraph ln libEnv)
                         ll <- getGoalList ls allNodes allNodes
                         printNodeNumberFromList ll
                         return []
        _            -> return [(OutputErr "Wrong parameters")]
     _:l               -> cViewNodeNumber input l
     []                -> return [(OutputErr "Wrong parameters")]


cShowGraph :: String -> [Status] 
                          -> IO [Status]
cShowGraph _ status =
  (do
    case status of
#ifdef UNI_PACKAGE
       Env ln libEnv : l ->
         case l of
           Address file : _ -> do
               showGraph file defaultHetcatsOpts (Just (ln, libEnv))
               return []
           _ : ll -> cShowGraph "" (Env ln libEnv : ll)
           [] -> do putStrLn "Error, no library loaded!"
                    return []
       Address file : l ->
         case l of
           Env ln libEnv : _ -> do
               showGraph file defaultHetcatsOpts (Just (ln, libEnv))
               return []
           _ : ll -> cShowGraph "" (Address file : ll)
           [] -> do putStrLn "Error, no library loaded!"
                    return []
#endif
       _ : l -> cShowGraph "" l
       [] -> do putStrLn "Error, no library loaded! (or compiled without uni)"
                return []) `catch` (\_ -> return [])


{--
spassApplyProveTo :: Bool -> [GraphGoals]  -> [String] 
                  -> IO [Status]
spassApplyProveTo exclTh nodelist comorph
 = case nodelist of
    []   -> return []
    x:ls ->
      case x of
        GraphNode (_,(DGNode name gtheory _ _ _ _ _)) -> 
          case gtheory of
            G_theory lid sigma sens ->
              case (do 
                     let th = mapTheoryStatus (\_ ->empty_proof_tree)
                                              (Theory sigma sens)
                     th1<- coerceTheory lid lidProver "errmsg" th
                     return (th1)) of
               Just th1 -> do
                             result <-  spassProveCMDLautomatic
                                          (showName name)     
					  (Tactic_script 
					   (show $ ATPTactic_script {
                                            ts_timeLimit = 20, 
                                            ts_extraOpts = [] }))
       					  th1
			     putStr $ show result
                             return [] 
        GraphNode (_,(DGRef name _ _ gtheory _ _ )) ->
          case gtheory of
           G_theory lid sigma sens -> 
            case (do
                   let th = mapTheoryStatus (\_ -> empty_proof_tree)
                                            (Theory sigma sens)
                   th1<- coerceTheory lid lidProver "errmsg" th
                   return (th1)) of
             Just th1 -> do 
                          result <- spassProveCMDLautomatic
					(showName name)
                                        (Tactic_script
                                         (show $ ATPTactic_script {
                                          ts_timeLimit = 20,
                                          ts_extraOpts = [] }))
                                        th1
                          putStr $ show result
                          return []
        _ -> spassApplyProveTo exclTh ls comorph

--}
cDummy :: String -> [Status] -> IO [Status]
cDummy _ _ 
  = do
        return []
