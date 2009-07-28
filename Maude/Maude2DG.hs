

module Maude2DG where

import System.IO
import System.Process

import Static.DevGraph
import Static.GTheory
import Static.AnalysisStructured

import Logic.Prover
import Logic.Grothendieck
import Logic.ExtSign
import Logic.Logic

import Maude.AS_Maude
import Maude.Sign
import Maude.Printing
import Maude.Sentence
import Maude.Morphism
import Maude.Logic_Maude
import qualified Maude.Meta.HasName as HasName

import Data.Maybe
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph

import Common.AS_Annotation
import Common.Result

-- Borrar despues de las pruebas
import GUI.ShowGraph
import Driver.Options
import Common.LibName
import Common.Id

maude_cmd :: String
maude_cmd = "/Applications/maude-darwin/maude.intelDarwin -interactive -no-banner"

data ImportType = Pr | Ex | Inc
type ModExpProc = (Token, Map.Map Token (Node, Sign), Morphism, DGraph)
type ImportProc = (ImportType, Token, Map.Map Token (Node, Sign), Morphism, DGraph)
type NodeSigMap = Map.Map Token (Node, Sign)

get_sign :: ImportProc -> Sign
get_sign (_, _, _, morph, _) = target morph

insertSpecs :: [Spec] -> NodeSigMap -> DGraph -> DGraph
insertSpecs [] _ dg = dg
insertSpecs (s : ss) nsm dg = insertSpecs ss nsm' dg'
              where (nsm', dg') = insertSpec s nsm dg

insertSpec :: Spec -> NodeSigMap -> DGraph -> (NodeSigMap, DGraph)
insertSpec (SpecMod sp_mod) nsm dg = (nsm3, dg3)
              where il = getImports sp_mod
                    ips = processImports nsm dg il
                    (nsm1, dg1) = last_da ips (nsm, dg)
                    sg = sign_union (fromSpec sp_mod) ips
                    ext_sg = makeExtSign Maude sg
                    nm_sns = map (makeNamed "") $ getSentences sp_mod
                    sens = toThSens nm_sns
                    gt = G_theory Maude ext_sg startSigId sens startThId
                    tok = HasName.getName sp_mod
                    name = makeName tok 
                    (ns, dg2) = insGTheory dg1 name DGBasic gt
                    nsm2 = Map.insert tok (getNode ns, sg) nsm1
                    (nsm3, dg3) = createEdges tok ips sg nsm2 dg2
insertSpec (SpecView _) nsm dg = (nsm, dg)

sign_union :: Sign -> [ImportProc] -> Sign
sign_union sign = foldr (union . get_sign) sign

last_da :: [ImportProc] -> (NodeSigMap, DGraph) -> (NodeSigMap, DGraph)
last_da [a] _ = da a
last_da (_ : ips) p = last_da ips p
last_da _ p = p

createEdges :: Token -> [ImportProc] -> Sign -> NodeSigMap -> DGraph
               -> (NodeSigMap, DGraph)
createEdges _ [] _ nsm dg = (nsm, dg)
createEdges tok (ip : ips) sg nsm dg = createEdges tok ips sg nsm' dg'
               where (nsm', dg') = createEdge tok ip sg nsm dg

createEdge :: Token -> ImportProc -> Sign -> NodeSigMap -> DGraph
              -> (NodeSigMap, DGraph)
createEdge tok1 (Pr, tok2, _, morph, _) sg nsm dg = (nsm', dg'')
               where morph' = setTarget sg morph
                     (tok2', nsm', dg') = insertFreeNode tok2 nsm dg
                     (n1, _) = fromJust $ Map.lookup tok1 nsm'
                     (n2, _) = fromJust $ Map.lookup tok2' nsm'
                     dg'' = insertDefEdgeMorphism n1 n2 morph' dg'
createEdge tok1 (Inc, tok2, _, morph, _) sg nsm dg = (nsm, dg')
               where morph' = setTarget sg morph
                     (n1, _) = fromJust $ Map.lookup tok1 nsm
                     (n2, _) = fromJust $ Map.lookup tok2 nsm
                     dg' = insertDefEdgeMorphism n1 n2 morph' dg
createEdge _ _ _ nsm dg = (nsm, dg)

da :: ImportProc -> (NodeSigMap, DGraph)
da (_, _, nsm, _, dg) = (nsm, dg)

processImports :: NodeSigMap -> DGraph -> [Import] -> [ImportProc]
processImports _ _ [] = []
processImports nsm dg (i : il) = ip : processImports nsm' dg' il
         where ip@(_, _, nsm', _, dg') = processImport nsm dg i

processImport :: NodeSigMap -> DGraph -> Import -> ImportProc
processImport nsm dg (Protecting modExp) = (Pr, tok, nsm', morph, dg')
         where (tok, nsm', morph, dg') = processModExp nsm dg modExp
processImport nsm dg (Extending modExp) = (Ex, tok, nsm', morph, dg')
         where (tok, nsm', morph, dg') = processModExp nsm dg modExp
processImport nsm dg (Including modExp) = (Inc, tok, nsm', morph, dg')
         where (tok, nsm', morph, dg') = processModExp nsm dg modExp

processModExp :: NodeSigMap -> DGraph -> ModExp -> ModExpProc
processModExp nsm dg (ModExp modId) = (tok, nsm, morph, dg)
                     where tok = HasName.getName modId
                           (_, sg) = fromJust $ Map.lookup tok nsm
                           morph = createInclMorph sg sg
processModExp nsm dg (SummationModExp modExp1 modExp2) = (tok, nsm3, morph, dg5)
                     where (tok1, nsm1, morph1, dg1) = processModExp nsm dg modExp1
                           (tok2, nsm2, morph2, dg2) = processModExp nsm1 dg1 modExp2
                           tok = mkSimpleId $ "{" ++ show tok1 ++ " + " ++ show tok2 ++ "}"
                           (n1, _) = fromJust $ Map.lookup tok1 nsm2
                           (n2, _) = fromJust $ Map.lookup tok2 nsm2
                           sg1 = target morph1
                           sg2 = target morph2
                           sg = union sg1 sg2
                           morph = createInclMorph sg sg
                           morph1' = setTarget sg morph1
                           morph2' = setTarget sg morph2
                           (nsm3, dg3) = insertNode tok sg nsm2 dg2
                           (n3, _) = fromJust $ Map.lookup tok nsm3
                           dg4 = insertDefEdgeMorphism n3 n1 morph1' dg3
                           dg5 = insertDefEdgeMorphism n3 n2 morph2' dg4
processModExp nsm dg (RenamingModExp modExp rnms) = (tok, nsm', morph', dg')
                     where (tok, nsm', morph, dg') = processModExp nsm dg modExp
                           morph' = fromSignRenamings (target morph) rnms
--                           comp_morph = fromJust $ maybeResult $ compose morph morph'

insertNode :: Token -> Sign -> NodeSigMap -> DGraph -> (NodeSigMap, DGraph)
insertNode tok sg nsm dg = if Map.member tok nsm
                         then (nsm, dg)
                         else let
                                ext_sg = makeExtSign Maude sg
                                gt = G_theory Maude ext_sg startSigId noSens startThId
                                name = makeName tok 
                                (ns, dg') = insGTheory dg name DGBasic gt
                                nsm' = Map.insert tok (getNode ns, sg) nsm
                              in (nsm', dg')

insertDefEdgeMorphism :: Node -> Node -> Morphism -> DGraph -> DGraph
insertDefEdgeMorphism n1 n2 morph dg = insEdgeDG (n2, n1, edg) dg
                     where mor = G_morphism Maude morph startMorId
                           edg = DGLink (gEmbed mor) globalDef SeeTarget $ getNewEdgeId dg

insertFreeEdge :: Token -> Token -> NodeSigMap -> DGraph -> DGraph
insertFreeEdge tok1 tok2 nsm dg = insEdgeDG (n2, n1, edg) dg
                     where (n1, sg1) = fromJust $ Map.lookup tok1 nsm
                           (n2, sg2) = fromJust $ Map.lookup tok2 nsm
                           mor = G_morphism Maude (createInclMorph sg1 sg2) startMorId
                           dgt = FreeOrCofreeDefLink Free $ EmptyNode (Logic Maude)
                           edg = DGLink (gEmbed mor) dgt SeeTarget $ getNewEdgeId dg

insertFreeNode :: Token -> NodeSigMap -> DGraph -> (Token, NodeSigMap, DGraph)
insertFreeNode t nsm dg = (t', nsm', dg'')
               where t' = mkFreeName t
                     (nsm', dg') = if Map.member t' nsm
                                 then (nsm, dg)
                                 else insertFreeNode2 t' nsm (fromJust $ Map.lookup t nsm) dg
                     dg'' = insertFreeEdge t' t nsm' dg'

insertFreeNode2 :: Token -> NodeSigMap -> (Node, Sign) -> DGraph -> (NodeSigMap, DGraph)
insertFreeNode2 t nsm (_, sg) dg = (nsm', dg')
              where ext_sg = makeExtSign Maude sg
                    gt = G_theory Maude ext_sg startSigId noSens startThId
                    name = makeName t
                    (ns, dg') = insGTheory dg name DGBasic gt
                    nsm' = Map.insert t (getNode ns, sg) nsm

mkFreeName :: Token -> Token
mkFreeName = mkSimpleId . (\ x -> x ++ "'") . show

mkSummName :: Token -> Token -> Token
mkSummName t1 t2 = mkSimpleId $ (show t1) ++ (show t2)

getNameModExp :: ModExp -> Token
getNameModExp (ModExp modId) = HasName.getName modId
getNameModExp (SummationModExp mod1 mod2) = mkSimpleId $ nm1 ++ " + " ++ nm2
                 where nm1 = show $ getNameModExp mod1
                       nm2 = show $ getNameModExp mod2
getNameModExp _ = mkSimpleId "Foo"

getImports :: Module -> [Import]
getImports (Module _ _ stmts) = getImportsStmnts stmts

getImportsStmnts :: [Statement] -> [Import]
getImportsStmnts [] = []
getImportsStmnts ((ImportStmnt imp) : stmts) = imp : getImportsStmnts stmts
getImportsStmnts (_ : stmts) = getImportsStmnts stmts

directMaudeParsing :: FilePath -> IO DGraph
directMaudeParsing fp = do
              (hIn, hOut, _, _) <- runInteractiveCommand maude_cmd
              hPutStrLn hIn $ "load " ++ fp
              let ns = traverse fp
              ms <- traverseNames hIn hOut ns -- improveSign fp ns
              hPutStrLn hIn "in /Users/adrian/Hets/Maude/hets.prj"
              psps <- predefinedSpecs hIn hOut
              sps <- traverseSpecs hIn hOut ms
              return $ insertSpecs (psps ++ sps) Map.empty emptyDG

directMaudeParsing2 :: FilePath -> IO ()
directMaudeParsing2 fp = do
    dg <- directMaudeParsing fp
    showGraph fp maudeHetcatsOpts
              (Just (Lib_id (Direct_link "" nullRange),
              Map.singleton (Lib_id (Direct_link "" nullRange)) dg ))


traverse :: FilePath -> [NamedSpec]
traverse _ = [Mod "TEST", Mod "TEST2", Mod "TEST3", Mod "TEST4"]

data NamedSpec = Mod String
               | Views String

traverseSpecs :: Handle -> Handle -> [String] -> IO [Spec]
traverseSpecs _ _ [] = return []
traverseSpecs hIn hOut (m : ms) = do
                 hPutStrLn hIn m
                 hFlush hIn
                 sOutput <- getAllSpec hOut "" False
                 ss <- traverseSpecs hIn hOut ms
                 let stringSpec = getSpec sOutput
                 let spec = read stringSpec :: Spec
                 return $ spec : ss

traverseNames :: Handle -> Handle -> [NamedSpec] -> IO [String]
traverseNames _ _ [] = return []
traverseNames hIn hOut (Mod q : ns) = do
                 hPutStrLn hIn $ "show module " ++ q ++ " ."
                 hFlush hIn
                 sOutput <- getAllOutput hOut "" False -- hGetLine hOut
                 rs <- traverseNames hIn hOut ns
                 return $ sOutput : rs
traverseNames hIn hOut (Views q : ns) = do
                 hPutStrLn hIn $ "show view " ++ q ++ " ."
                 hFlush hIn
                 sOutput <- getAllOutput hOut "" False -- hGetLine hOut
                 rs <- traverseNames hIn hOut ns
                 return $ sOutput : rs

getAllOutput :: Handle -> String -> Bool -> IO String
getAllOutput hOut s False = do
                 ss <- hGetLine hOut
                 getAllOutput hOut (s ++ " " ++ ss) (final ss)
getAllOutput _ s True = return $ prepare s

getAllSpec :: Handle -> String -> Bool -> IO String
getAllSpec hOut s False = do
                 ss <- hGetLine hOut
                 getAllSpec hOut (s ++ " " ++ ss) (finalSpec ss)
getAllSpec _ s True = return s

final :: String -> Bool
final "endfm" = True
final "endm" = True
final "endth" = True
final "endfth" = True
final "endv" = True
final _ = False

prepare :: String -> String
prepare s = "(" ++ (drop 8 s) ++ ")"

finalSpec :: String -> Bool
finalSpec "@#$endHetsSpec$#@" = True
finalSpec _ = False

predefined :: [NamedSpec]
predefined = [Mod "TRUTH-VALUE", Mod "TRUTH", Mod "BOOL"]

predefinedSpecs :: Handle -> Handle -> IO [Spec]
predefinedSpecs hIn hOut = traversePredefined hIn hOut predefined

traversePredefined :: Handle -> Handle -> [NamedSpec] -> IO [Spec]
traversePredefined _ _ [] = return []
traversePredefined hIn hOut (Mod n : ns) = do
                 hPutStrLn hIn $ "(hets " ++ n ++ " .)"
                 hFlush hIn
                 sOutput <- getAllSpec hOut "" False
                 ss <- traversePredefined hIn hOut ns
                 let stringSpec = getSpec sOutput
                 let spec = read stringSpec :: Spec
                 return $ spec : ss
traversePredefined _ _ _ = return []

-- DELETE ONCE TESTS ARE FINISHED

maudeHetcatsOpts :: HetcatsOpts
maudeHetcatsOpts = HcOpt
  { analysis = Basic
  , guiType = UseGui
  , infiles  = []
  , specNames = []
  , transNames = []
  , intype   = GuessIn
  , libdir   = ""
  , modelSparQ = ""
  , outdir   = ""
  , outtypes = [] -- no default
  , recurse  = False
  , defLogic = "Maude"
  , verbose  = 1
  , outputToStdout = True
  , caslAmalg = []
  , interactive = False
  , connectP = -1
  , connectH = ""
  , uncolored = False
  , xmlFlag = False
  , computeNormalForm = False
  , dumpOpts = []
  , listen   = -1 }
