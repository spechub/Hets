{- HetCATS/AnalysisLibrary.hs
   $Id$
   Till Mossakowski

   Analysis of libraries

   Follows the extended static semantic rules in:

   T. Mossakowski, S. Autexier, D. Hutter, P. Hoffman:
   CASL Proof calculus.
   Available from http://www.informatik.uni-bremen.de/~till/calculus.ps
   To appear in the CASL book.

   Todo:

-}


module AnalysisLibrary
where

import Logic
import LogicRepr
import Grothendieck
import Graph
import DevGraph
import qualified AS_Structured
import Parse_AS_Structured (lookupLogic, library)
import Parsec
import AS_Library
import AnalysisStructured
import AS_Annotation
import GlobalAnnotations
import GlobalAnnotationsFunctions
import Result
import Id
import FiniteMap
import Result

ana_file :: LogicGraph -> AnyLogic -> String -> IO DGraph
ana_file logicGraph defaultLogic fname = do
  input <- readFile fname
  putStrLn "Successfully read."
  let ast = case runParser (library logicGraph) defaultLogic fname input of
              Left err -> error (show err)
              Right ast -> ast
  putStrLn "Successfully parsed."
  Result diags res <- ana_LIB_DEFN logicGraph defaultLogic emptyLibEnv ast
  putStrLn "Successfully analyzed."
  sequence (map (putStrLn . show) diags)
  putStrLn "Errors printed."
  return (case res of 
             Just (ln,libenv,dg) -> dg
             Nothing -> empty) 
  

ana_LIB_DEFN :: LogicGraph -> AnyLogic 
                 -> LibEnv -> LIB_DEFN
                 -> IO(Result (LIB_NAME,LibEnv,DGraph))

ana_LIB_DEFN lgraph l libenv (Lib_defn ln libItems pos ans) = 
  foldl ana (return (return (gannos,emptyFM,empty,l))) 
                                   (map item libItems)
  `ioBind` (\(gannos',genv,dg,_) -> return (return (ln,addToFM libenv ln (genv,dg,gannos'),dg)))
  where
  gannos = addGlobalAnnos emptyGlobalAnnos ans
  ana res libItem = do
    res `ioBind` 
      (\(gannos,genv,dg,l) ->
          ana_LIB_ITEM_with_download lgraph libenv gannos genv dg l libItem)

ana_LIB_ITEM_with_download :: LogicGraph -> LibEnv -> GlobalAnnos 
                 -> GlobalEnv -> DGraph -> AnyLogic 
                 -> LIB_ITEM
                 -> IO (Result (GlobalAnnos,GlobalEnv,DGraph,AnyLogic))

ana_LIB_ITEM_with_download lgraph libenv gannos genv dg l (Download_items ln items pos) =
  ana_err "download"

ana_LIB_ITEM_with_download lgraph libenv gannos genv dg l libItem =
  return (ana_LIB_ITEM lgraph libenv gannos genv dg l libItem)


ana_LIB_ITEM :: LogicGraph -> LibEnv -> GlobalAnnos 
                 -> GlobalEnv -> DGraph -> AnyLogic 
                 -> LIB_ITEM
                 -> Result (GlobalAnnos,GlobalEnv,DGraph,AnyLogic)

ana_LIB_ITEM lgraph libenv gannos genv dg l (Spec_defn spn gen asp pos) = do
  ((imp,params,allparams),dg') <- ana_GENERICITY gannos genv dg l gen
  (body,dg'') <- ana_SPEC gannos genv dg' allparams (Just spn) (item asp)
  if elemFM spn genv 
   then plain_error (gannos,genv,dg,l)
                    ("Name "++show spn++" already defined")
                    (head (pos++nullPosList))
   else return (gannos,addToFM genv spn (SpecEntry (imp,params,body)),dg'',l)

ana_LIB_ITEM lgraph libenv gannos genv dg l (View_defn vn gen vt symmap pos) =
  ana_err "views"

ana_LIB_ITEM lgraph libenv gannos genv dg l (Arch_spec_defn asn asp pos) = 
  ana_err "arch spec"

ana_LIB_ITEM lgraph libenv gannos genv dg l (Unit_spec_defn usn usp pos) =
  ana_err "unit spec"

ana_LIB_ITEM lgraph libenv gannos genv dg l (Download_items ln items pos) =
  ana_err "download"

ana_LIB_ITEM lgraph libenv gannos genv dg l (Logic_decl ln pos) = do
  let log = lookupLogic ln lgraph
  return (gannos,genv,dg,log)
