{- |
Module      :  $Header$
Description :  add to all names in the nodes of the libenv a list of paths
Copyright   :  (c) Ewaryst Schulz DFKI Bremen 2010
License     :  GPLv2 or higher
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

the list of all paths by which the name is imported into a node is added
to the name. Additionally we keep the original name.
This pathification is used in the OMDoc facility.
-}

module Proofs.PathifyNames (pathifyLibEnv) where

import Logic.Coerce
import Logic.Comorphism
import Logic.Grothendieck
import Logic.Logic

import Static.DevGraph
import Static.GTheory
import Static.History

import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad

type EdgeNum = Int

-- | adds path-information for each symbol in the libenv
pathifyLibEnv :: LibEnv -> Result LibEnv
pathifyLibEnv libEnv =
    foldM f Map.empty $ getTopsortedLibs libEnv
        where
          f le ln =
              do
                let dg0 = lookupDGraph ln libEnv
                dg <- pathifyDG le (getLibId ln) dg0
                return $ Map.insert ln dg le


-- | adds path-information for each symbol in the devgraph
pathifyDG :: LibEnv -> LibId -> DGraph -> Result DGraph
pathifyDG le li dg = do
  foldM (pathifyLabNode le li) dg $ topsortedNodes dg


-- | adds path-information for each symbol in the nodelabel
pathifyLabNode :: LibEnv -> LibId -> DGraph -> LNode DGNodeLab
               -> Result DGraph
pathifyLabNode le li dg (n, lb) =
   if isDGRef lb then
       do
         -- get referenced labnode from the libenv and update the
         -- pathlist in the refnode
         let rn = labDG (lookupDGraph (dgn_libname lb) le) $ dgn_node lb
         let nlb = lb { dgn_symbolpathlist = dgn_symbolpathlist rn }
         return $ changesDGH dg [SetNodeLab lb (n, nlb)]        
   else case dgn_theory lb of
    G_theory lid (ExtSign sig _) _ _ _ -> do
      -- get the global imports
      innMorphs <- getGlobalImports lid dg $ innDG dg n
      m <- pathifySign lid li sig innMorphs
      let nlb = lb { dgn_symbolpathlist = G_symbolmap lid m }
      return $ changesDGH dg [SetNodeLab lb (n, nlb)]


-- | we search in all incoming links for the symbols in the current signature
-- | in order to compute the path-information of the signature
getGlobalImports :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
          lid -> DGraph -> [LEdge DGLinkLab]
              -> Result [(EdgeNum, morphism, Bool, Map.Map symbol [SLinkPath])]
getGlobalImports lid dg l = fmap catMaybes $ mapR (getGlobalImport lid dg) l

-- | for each link we return the:
-- | 1. source of the link
-- | 2. the signature morphism
-- | 3. a flag signaling if the morphism goes from target to source (for hiding)
-- | 4. the symbol-pathlist-map showing all pathes by which a symbol was
-- |    imported to the target node
getGlobalImport :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
          lid -> DGraph -> LEdge DGLinkLab ->
          Result (Maybe (EdgeNum, morphism, Bool, Map.Map symbol [SLinkPath]))
getGlobalImport lid dg (from, _, llab) =
    let lt = dgl_type llab in
    -- check the type of the linklabel first
    if isDefEdge lt
    then
        if isLocalEdge lt
        then do
          -- local edges aren't supported...
          warning ()
             (unlines
              ["Local link with " ++ show (dgl_id llab)
               ++ " not supported.", 
               "The result of pathify may not be as expected."]) nullRange
          -- and will be skipped
          return Nothing
        else
            -- we have a global edge here
            case (dgl_morphism llab, dgl_id llab) of
              (GMorphism cid (ExtSign sign1 _) _ mor _, EdgeId n) ->
                  do
                    hmor <- coerceMorphism (targetLogic cid) lid
                            "getGlobalImport" mor
                    case dgn_symbolpathlist $ labDG dg from of
                      G_symbolmap lid0 m ->
                          if isIdComorphism (Comorphism cid)
                          then
                          return $ Just (n, hmor, isHidingDef lt
                                        , coerceSymbolmap lid0 lid m)
                          else
                              do
                                warning () ("translating by comorphism "
                                            ++ show cid) nullRange
                                let plmap = Map.mapKeys
                                             (sglElem (show cid)
                                              . map_symbol cid sign1)
                                             $ coerceSymbolmap lid0
                                                  (sourceLogic cid) m
                                return $ Just (n, hmor, isHidingDef lt,
                                                coerceSymbolmap
                                                (targetLogic cid) lid plmap)
    -- theorem links will be skipped
    else return Nothing


pathifySign :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
          lid -> LibId -> sign
             -> [(EdgeNum, morphism, Bool, Map.Map symbol [SLinkPath])]
             -> Result (Map.Map symbol [SLinkPath])
pathifySign lid libid sig l =
    foldM (pathifyImport lid libid)
              (Map.fromList $ map ( \x -> (x,[]) ) $ symlist_of lid sig) l



pathifyImport :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
          lid -> LibId -> Map.Map symbol [SLinkPath]
              -> (EdgeNum, morphism, Bool, Map.Map symbol [SLinkPath])
              -> Result (Map.Map symbol [SLinkPath])
pathifyImport lid libid lpm0 (n, m, b, lpm) =
    let symmap = Map.toList $ symmap_of lid m
        symbMap = if b then map ( \ (x,y) -> (y,x) ) symmap
                  else symmap
    in foldM (pathifySymbol lid libid n lpm) lpm0 symbMap

pathifySymbol :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
          lid -> LibId -> EdgeNum -> Map.Map symbol [SLinkPath]
              -> Map.Map symbol [SLinkPath] -> (symbol, symbol)
              -> Result (Map.Map symbol [SLinkPath])
pathifySymbol lid libid n lpm lpm0 (s, sMapped) = do
  -- get the pathslist for the mapped symbol
  let lp0 = lpm0 Map.! sMapped
  -- get the entries in the linksource to add the current path
  let lp = lpm Map.! s
  let lpNew = lp0 ++
              if null lp
              then [initPath libid n $ show $ sym_name lid sMapped]
              else map (addToPath libid n) lp
  return $ Map.adjust (const lpNew) sMapped lpm0





-- | extracts the single element from singleton sets, fails otherwise
sglElem:: String -> Set.Set a -> a
sglElem s sa
    | Set.size sa > 1 = error $ "PathifyNames: symbol image > 1 in " ++ s
    | Set.null sa = error $ "PathifyNames: empty symbol image in " ++ s
    | otherwise = Set.findMin sa

