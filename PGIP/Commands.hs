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
import Text.ParserCombinators.Parsec
import Common.Lexer
import Common.AnnoState

 
scanPathFile::CharParser st String
scanPathFile 
     = many1 ( oneOf (caslLetters ++ ['0'..'9'] ++ ['-','_','.']))


scanAnyWord::CharParser st String
scanAnyWord
     = many1 (oneOf (caslLetters ++ ['0'..'9'] ++ ['_','\'','.','-']))

-- |the 'getPath' function read a path as a a list of words
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
-- |the 'getKeyWord' function accepts a string as argument and tries to read it
getKeyWord::String -> AParser st String
getKeyWord wd 
              =  try ( string wd
                     ) 
              <|> 
                 try ( do  skip 
                           string wd
                     )
              <?> ("keyword "++wd)
                       
getGoal::AParser st GOAL
getGoal        
       = try ( do  v1<-scanAnyWord
                   getKeyWord "-"
                   v2<-getNumber
                   getKeyWord "->"
                   v3<-scanAnyWord
                   return (LabeledEdge v1 (read v2::Int) v3)
             )       
      <|> 
         try ( do  v1<-scanAnyWord
                   getKeyWord "->"                                  
                   v2<-scanAnyWord
                   return (Edge  v1  v2)
             )
      <|> 
         try ( do  v<-scanAnyWord
                   return (Node  v)
             )   
      <?>
         "goal"    

getScript::AParser st String
getScript 
         = try ( do  getKeyWord "end-script"
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
                                        
getComorphism::AParser st [String]
getComorphism 
             = try ( do  v<-scanAnyWord
                         getKeyWord ";"
                         vs <-getComorphism
                         return ( v:vs)
                   )
            <|>
               try ( do  v<-scanAnyWord
                         return [ v]
                   )
            <?>
               " list of ID's separated by semicolon"

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



test::String->[Status] -> IO [Status]
test ls _  
  = do
      putStrLn $ show ls
      return []          

removeSpace :: String -> String
removeSpace ls
  = case ls of
      []   -> []
      _:[] -> []
      x:l  -> x:(removeSpace l)

cUse::String->[Status] -> IO [Status]
cUse input _
 =do
--   let r=runParser (scanCommand ["PATH"]) (emptyAnnos ()) "" input
--   case r of
--    Left _ -> do
--                putStr "\n Error parsing the argument ! \n"
--                return []
--    Right ls ->
--     case ls of
--      (Path file):_ -> 
--        do
--          let file = joinWith '/' list
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
--      _       -> return [(OutputErr "Wrong parameter")]    

cDgAllAuto::String -> [Status] -> IO [Status]
cDgAllAuto _ arg
   = case arg of
       (Env x y):_   -> let result= automatic x y 
                            newGoalList = createAllGoalsList x result
                        in  return ((Env x result):(AllGoals newGoalList):[])
       _:l           -> cDgAllAuto "" l
       []            -> return ([(OutputErr "Wrong parameter")])

cDgAuto :: String -> [Status] -> IO [Status]
cDgAuto input status
 = do 
    let r= runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
    case r of
     Left _ -> do
                putStr "\n Error parsing the goal list ! \n"
                return []
     Right param ->
      do
       case status of
        (Env ln libEnv):l -> 
         case l of
           (AllGoals allGoals):_ ->
               case param of
                 (Goals ls):_ -> 
                     let ll = getEdgeList $ getGoalList ls allGoals
                         result = automaticFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in return ((Env ln result):(AllGoals newGoalList):[])
                 _  -> return ([(OutputErr "Wrong parameters")])
           _:list -> cDgAuto input ((Env ln libEnv):list)
           _  ->return ([(OutputErr "Wrong parameters")])
        (AllGoals allGoals):l -> 
         case l of
          (Env ln libEnv):_ -> 
               case param of 
                 (Goals ls):_ ->
                     let ll = getEdgeList $ getGoalList ls allGoals
                         result = automaticFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in return ((Env ln result):(AllGoals newGoalList):[])
                 _ -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgAuto input ((AllGoals allGoals):list)
          _      -> return [(OutputErr "Wrong parameters")]
        _:l       -> cDgAuto input l
        []        -> return [(OutputErr "Wrong parameters")]

cDgGlobSubsume::String -> [Status] ->IO [Status]
cDgGlobSubsume input status
 =do
   let r = runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
   case r of
    Left _ -> do
               putStr "\n Error parsing the goal list ! \n"
               return []
    Right param ->
     do
      case status of
       (Env ln libEnv):l  -> 
         case l of 
           (AllGoals allGoals):_ -> 
               case param of
                 (Goals ls):_ -> 
                     let ll = getEdgeList $ getGoalList ls allGoals
                         result = globSubsumeFromList ln ll  libEnv 
                         newGoalList = createAllGoalsList ln result
                     in return ((Env ln result):(AllGoals newGoalList):[])
                 _            ->return  [(OutputErr "Wrong parameters")]
           _:ll -> cDgGlobSubsume input ((Env ln libEnv):ll)
           _    -> return [(OutputErr "Wrong parameters")]
       (AllGoals allGoals):l -> 
         case l of 
           (Env ln libEnv):_ -> 
               case param of
                 (Goals ls):_ -> 
                     let ll= getEdgeList $ getGoalList ls allGoals
                         result = globSubsumeFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in return ((Env ln result):(AllGoals newGoalList):[])
                 _   -> return [(OutputErr "Wrong parameters")]
           _:ll -> cDgGlobSubsume input ((AllGoals allGoals):ll)
           _    -> return [(OutputErr "Wrong parameters")]
       _:l  -> cDgGlobSubsume input l
       []   -> return [(OutputErr "Wrong parameters")]



cDgAllGlobSubsume::String -> [Status] -> IO [Status]
cDgAllGlobSubsume _ arg
  = case arg of
     (Env x y):_  -> 
       let result =(globSubsume x) y 
           newGoalList = createAllGoalsList x result
       in  return ((Env x result):(AllGoals newGoalList):[])
     _:l          -> cDgAllGlobSubsume "" l
     []           -> return [(OutputErr "Wrong parameters")]

cDgAllGlobDecomp::String -> [Status] -> IO [Status]
cDgAllGlobDecomp _ arg 
  = case arg of 
     (Env x y):_ -> 
       let result= (globDecomp x) y 
           newGoalList = createAllGoalsList x result
       in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllGlobDecomp "" l
     []          -> return [(OutputErr "Wrong parameters")]


cDgGlobDecomp :: String -> [Status] -> IO [Status]
cDgGlobDecomp input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "\n Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):l  -> 
        case l of 
          (AllGoals allGoals):_ -> 
              case param of
                (Goals ls):_ -> 
                      let ll = getEdgeList $ getGoalList ls allGoals
                          result = globDecompFromList ln ll  libEnv 
                          newGoalList = createAllGoalsList ln result
                      in  return ((Env ln result):(AllGoals newGoalList):[])
                _   -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgGlobDecomp input  ((Env ln libEnv):list)
          _      -> return [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l -> 
        case l of 
          (Env ln libEnv):_ -> 
              case param of
                (Goals ls):_ -> 
                      let ll= getEdgeList $ getGoalList ls allGoals
                          result = globDecompFromList ln ll libEnv
                          newGoalList = createAllGoalsList ln result
                      in  return ((Env ln result):(AllGoals newGoalList):[])
                _  -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgGlobDecomp input ((AllGoals allGoals):list)
          _      -> return [(OutputErr "Wrong parameters")]
     _:l                -> cDgGlobDecomp input l
     []                 -> return [(OutputErr "Wrong parameters")]


cDgAllLocInfer::String -> [Status] -> IO [Status]
cDgAllLocInfer _ arg
  = case arg of
      (Env x y):_ -> let result= (localInference x) y
                         newGoalList = createAllGoalsList x result 
                     in  return ((Env x result):(AllGoals newGoalList):[])
      _:l         -> cDgAllLocInfer "" l
      []          -> return [(OutputErr "Wrong parameters")]


cDgLocInfer::String -> [Status] -> IO [Status] 
cDgLocInfer input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of 
   Left _ -> do
              putStr "\n Error parsing the goal list ! \n"
              return []
   Right param ->
     case status of
      (Env ln libEnv):l  -> 
          case l of 
            (AllGoals allGoals):_ ->
                 case param of
                  (Goals ls):_ -> 
                      let ll = getEdgeList $ getGoalList ls allGoals
                          result = localInferenceFromList ln ll  libEnv 
                          newGoalList = createAllGoalsList ln result
                      in return ((Env ln result):(AllGoals newGoalList):[])
                  _   -> return [(OutputErr "Wrong parameters")]
            _:list -> cDgLocInfer input ((Env ln libEnv):list)
            _      -> return [(OutputErr "Wrong parameters")]
      (AllGoals allGoals):l -> 
          case l of 
            (Env ln libEnv):_ -> 
                case param of
                 (Goals ls):_ ->
                     let ll= getEdgeList $ getGoalList ls allGoals
                         result = localInferenceFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in return ((Env ln result):(AllGoals newGoalList):[])
                 _    -> return [(OutputErr "Wrong parameters")]
            _:list -> cDgLocInfer input ((AllGoals allGoals):list)
            _      -> return [(OutputErr "Wrong parameters")]
      _:l    -> cDgLocInfer input l
      []     -> return [(OutputErr "Wrong parameters")]


cDgAllLocDecomp::String -> [Status] ->IO [Status]
cDgAllLocDecomp _ arg =
  case arg of 
     (Env x y):_ -> 
           let result= (locDecomp x) y 
               newGoalList = createAllGoalsList x result
           in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllLocDecomp "" l
     []          -> return [(OutputErr "Wrong parameters")]


cDgLocDecomp::String-> [Status]->IO [Status]
cDgLocDecomp input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do 
              putStr "\n Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):l  -> 
        case l of 
          (AllGoals allGoals):_ -> 
               case param of
                 (Goals ls):_ -> 
                      let ll = getEdgeList $ getGoalList ls allGoals
                          result = locDecompFromList ln ll  libEnv 
                          newGoalList = createAllGoalsList ln result
                      in return ((Env ln result):(AllGoals newGoalList):[])
                 _  -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgLocDecomp input  ((Env ln libEnv):list)
          _      -> return [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l -> 
        case l of 
          (Env ln libEnv):_ -> 
               case param of
                    (Goals ls):_ -> 
                       let ll= getEdgeList $ getGoalList ls allGoals
                           result = locDecompFromList ln ll libEnv
                           newGoalList = createAllGoalsList ln result
                       in return ((Env ln result):(AllGoals newGoalList):[])
                    _  -> return [(OutputErr "Wrong parameters")]
          _:list -> cDgLocDecomp input ((AllGoals allGoals):list)
          _      -> return [(OutputErr "Wrong parameters")]
     _:l            -> cDgLocDecomp input l
     []             -> return [(OutputErr "Wrong parameters")]



cDgComp::String -> [Status] -> IO [Status]
cDgComp input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "\n Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
      (Env ln libEnv):l  -> 
          case l of 
            (AllGoals allGoals):_ -> 
              case param of
                 (Goals ls):_ -> 
                     let ll = getEdgeList $ getGoalList ls allGoals
                         result = compositionFromList ln ll  libEnv 
                         newGoalList = createAllGoalsList ln result
                     in return ((Env ln result):(AllGoals newGoalList):[])
                 _ -> return [(OutputErr "Wrong parameters")]
            _:list -> cDgComp input  ((Env ln libEnv):list)
            _      -> return [(OutputErr "Wrong parameters")]
      (AllGoals allGoals):l -> 
         case l of 
           (Env ln libEnv):_ -> 
              case param of
                 (Goals ls):_ -> 
                     let ll= getEdgeList $ getGoalList ls allGoals
                         result = compositionFromList ln ll libEnv
                         newGoalList = createAllGoalsList ln result
                     in return ((Env ln result):(AllGoals newGoalList):[])
                 _    -> return [(OutputErr "Wrong parameters")]
           _:list -> cDgComp input ((AllGoals allGoals):list)
           _      -> return [(OutputErr "Wrong parameters")]
      _:l                -> cDgComp input l
      []                 -> return [(OutputErr "Wrong parameters")]




cDgAllComp::String -> [Status] ->IO [Status]
cDgAllComp _ arg 
  = case arg of
     (Env x y):_ -> 
         let result= (composition x) y 
             newGoalList = createAllGoalsList x result
         in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllComp "" l
     []          -> return [(OutputErr "Wrong parameters")]


cDgCompNew::String -> [Status] ->IO [Status]
cDgCompNew input status =
 do 
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do 
              putStr "\n Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):l  -> 
      case l of 
       (AllGoals allGoals):_ -> 
         case param of
          (Goals ls):_ -> 
            let ll = getEdgeList $ getGoalList ls allGoals
                result = compositionCreatingEdgesFromList ln ll libEnv
                newGoalList = createAllGoalsList ln result
            in return ((Env ln result):(AllGoals newGoalList):[])
          _   -> return [(OutputErr "Wrong parameters")]
       _:list -> cDgCompNew input ((Env ln libEnv):list)
       _      -> return [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l -> 
       case l of 
        (Env ln libEnv):_ -> 
           case param of
            (Goals ls):_ -> 
              let ll= getEdgeList $ getGoalList ls allGoals
                  result = compositionCreatingEdgesFromList ln ll libEnv
                  newGoalList = createAllGoalsList ln result
              in return ((Env ln result):(AllGoals newGoalList):[])
            _  -> return [(OutputErr "Wrong parameters")]
        _:list -> cDgCompNew input ((AllGoals allGoals):list)
        _      -> return [(OutputErr "Wrong parameters")]
     _:l                -> cDgCompNew input l
     []                 -> return [(OutputErr "Wrong parameters")]


 

cDgAllCompNew::String -> [Status] ->IO [Status]
cDgAllCompNew _ arg
 = case arg of
    (Env x y):_ -> 
       let result=(compositionCreatingEdges x) y
           newGoalList = createAllGoalsList x result
       in  return ((Env x result):(AllGoals newGoalList):[])
    _:l         -> cDgAllCompNew "" l
    []          -> return [(OutputErr "Wrong parameters")]

cDgHideThm::String -> [Status] ->IO [Status]
cDgHideThm input status =
 do 
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do  
              putStr "\n Error parsing the goal list ! \n"
              return []
   Right param ->
    case status of
     (Env ln libEnv):l  -> 
       case l of 
        (AllGoals allGoals):_ -> 
          case param of
            (Goals ls):_ -> 
               let ll = getEdgeList $ getGoalList ls allGoals
                   result = automaticHideTheoremShiftFromList ln ll  libEnv
                   newGoalList = createAllGoalsList ln result
               in return ((Env ln result):(AllGoals newGoalList):[])
            _   -> return [(OutputErr "Wrong parameters")]
        _:list -> cDgHideThm input ((Env ln libEnv):list)
        _      -> return [(OutputErr "Wrong parameters")]
     (AllGoals allGoals):l -> 
       case l of 
        (Env ln libEnv):_ -> 
           case param of
             (Goals ls):_ -> 
                let ll= getEdgeList $ getGoalList ls allGoals
                    result = automaticHideTheoremShiftFromList ln ll libEnv
                    newGoalList = createAllGoalsList ln result
                in return ((Env ln result):(AllGoals newGoalList):[])
             _   -> return [(OutputErr "Wrong parameters")]
        _:list -> cDgHideThm input ((AllGoals allGoals):list)
        _      -> return [(OutputErr "Wrong parameters")]
     _:l        -> cDgHideThm input l
     []         -> return [(OutputErr "Wrong parameters")]



cDgAllHideThm::String -> [Status] ->IO [Status]
cDgAllHideThm _ arg
  = case arg of
     (Env x y):_ -> 
        let result= (automaticHideTheoremShift x) y 
            newGoalList = createAllGoalsList x result
        in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllHideThm "" l
     []          -> return [(OutputErr "Wrong parameters")]

cDgAllThmHide::String -> [Status] ->IO [Status]
cDgAllThmHide _ arg
  = case arg of
     (Env x y):_ -> 
        let result=(theoremHideShift x) y 
            newGoalList = createAllGoalsList x result
        in  return ((Env x result):(AllGoals newGoalList):[])
     _:l         -> cDgAllThmHide "" l
     []          -> return [(OutputErr "Wrong parameters")]


cDgAllInferBasic::String -> [Status] ->IO [Status]
cDgAllInferBasic _ arg
 = case arg of
    (AllGoals allGoals):_ -> return [Selected allGoals] 
    _:l         -> cDgAllInferBasic "" l
    []          -> return [(OutputErr "Wrong parameters")]



cDgInferBasic::String -> [Status] -> IO [Status]
cDgInferBasic input status =
 do
  let r=runParser (scanCommand ["GOALS"]) (emptyAnnos ()) "" input
  case r of
   Left _ -> do
              putStr "\n Error parsing the goal list ! \n"
              return []
   Right param -> 
    case status of
     (AllGoals allGoals):_ -> 
       case param of
        (Goals ls):_ -> let ll = getGoalList ls allGoals
                        in  return ((Selected ll):[])
        _            -> return [(OutputErr "Wrong parameters")]
     _:l               -> cDgInferBasic input l
     []                -> return [(OutputErr "Wrong parameters")]
                                        

cTranslate::String -> [Status] -> IO [Status]
cTranslate input _
 = do
    let r=runParser (scanCommand ["COMORPHISM"]) (emptyAnnos ()) "" input
    case r of
     Left _ -> do
                putStr "\n Error parsing the comorphism ! \n"
                return []
     Right param ->
       case param of
                 (ParsedComorphism ls):_ -> return [(Comorph ls)] 
                 _                       -> return [(OutputErr "Wrong parameters")]

cProver::String -> [Status] ->IO [Status]
cProver input _
 = do
    let r=runParser (scanCommand ["PROVER"]) (emptyAnnos ()) "" input
    case r of
     Left _ -> do
                putStr "\n Error parsing the prover id \n"
                return []
     Right param  ->
       case param of
                 (UseProver ls ):_ -> return [(Prover ls)]
                 _                 -> return [(OutputErr "Wrong parameters")]

cShowDgGoals::String -> [Status]-> IO [Status]
cShowDgGoals  _ arg
  = do
     case arg of
       (AllGoals allGoals):_ -> do
         printNodeInfoFromList allGoals--putStr ("Goals:" ++ (show allGoals))
         return []
       _:l -> cShowDgGoals "" l
       []  -> do
               putStr "Error, no goal list found!\n "
               return []


cShowTheory::String -> [Status] -> IO [Status]
cShowTheory _ arg
  = case arg of 
     (AllGoals allGoals):_ -> do printNodeTheoryFromList allGoals
                                 return []
     _:l                        -> cShowNodeTheory "" l
     []                         -> do
                                    putStr "Error, no goal list found ! \n"
                                    return []


cShowNodeTheory::String -> [Status] -> IO [Status]
cShowNodeTheory _ arg
  = case arg of 
     (Selected xx):_ -> do 
                         printNodeTheoryFromList xx 
                         return []
     _:l                        -> cShowNodeTheory "" l
     []                         -> do 
                                    putStr "Error, no nodes selected ! \n"
                                    return []

cShowNodeInfo :: String -> [Status] -> IO [Status]
cShowNodeInfo _ arg
  = case arg of
     (Selected xx):_ -> do
                         printNodeInfoFromList xx
                         return []
     _:l             -> cShowNodeInfo "" l
     []              -> do 
                         putStr "Error, no nodes selected ! \n"
                         return []

cShowNodeConcept :: String -> [Status] -> IO [Status]
cShowNodeConcept _ arg
  = case arg of 
     (Selected xx):_ -> do
                         printNodeTaxonomyFromList KConcept xx
                         return []
     _:l             -> cShowNodeConcept "" l
     []              -> do
                         putStr "Error, no nodes selected ! \n"
                         return []

cShowNodeTaxonomy ::String -> [Status] -> IO [Status]
cShowNodeTaxonomy _ arg
  = case arg of
     (Selected xx):_ -> do
                         printNodeTaxonomyFromList KSubsort xx
                         return []
     _:l             -> cShowNodeTaxonomy "" l
     []              -> do 
                         putStr "Error, no nodes selected !\n"
                         return []


cProveAll :: String -> [Status]->IO [Status]
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
