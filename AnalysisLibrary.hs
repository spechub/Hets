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
import Parse_AS_Structured (lookupLogic)
import AS_Library
import AnalysisStructured
import AS_Annotation
import GlobalAnnotations
import GlobalAnnotationsFunctions
import Result
import Id
import FiniteMap

ana_LIB_DEFN :: LogicGraph -> LibEnv  
                 -> AnyLogic 
                 -> LIB_DEFN
                 -> Result (LIB_NAME,LibEnv)

ana_LIB_DEFN lgraph libenv l (Lib_defn ln libItems pos ans) = do
  (gannos',genv,dg,_) <- foldl ana (return (gannos,emptyFM,empty,l)) 
                                   (map item libItems)
  return (ln,addToFM libenv ln (genv,dg,gannos'))
  where
  gannos = addGlobalAnnos emptyGlobalAnnos ans
  ana res libItem = do
    (gannos,genv,dg,l) <- res
    ana_LIB_ITEM lgraph libenv gannos genv dg l libItem

ana_LIB_ITEM :: LogicGraph -> LibEnv -> GlobalAnnos 
                 -> GlobalEnv -> DGraph -> AnyLogic 
                 -> LIB_ITEM
                 -> Result (GlobalAnnos,GlobalEnv,DGraph,AnyLogic)

ana_LIB_ITEM lgraph libenv gannos genv dg l (Spec_defn spn gen asp pos) = do
  ((imp,params,allparams),dg') <- ana_GENERICITY gannos genv dg l gen
  (body,dg'') <- ana_SPEC gannos genv dg' allparams (item asp)
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
