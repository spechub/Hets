{- |
Module      :  $Header$
Description :  Exports a development graph to an omdoc structure
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

A given development graph will be exported to an omdoc structure
which can then be output to XML via the XmlInterface.
-}

module OMDoc.Export
    ( exportLibEnv
    ) where

import Logic.Logic
import Logic.Coerce
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism

import Static.DevGraph
import Static.GTheory

import Common.Result
import Common.ExtSign
import Common.Id
import Common.LibName
import Common.AS_Annotation

import OMDoc.DataTypes

import Data.Graph.Inductive.Graph
import Data.Maybe
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set


--------------------- Name Mapping interface ---------------------

dummy :: a
dummy = error "dummy"

-- | Mapping of symbols to unique ids
data SigMap a = SigMap (NameMap a) (NameMap String)

-- | Mapping of Specs to SigMaps
newtype SpecSymNames = SpecSymNames
    (Map.Map (LibName, String) (SigMap G_symbol))

type Env = SpecSymNames

fmapNM :: (Ord a, Ord b) => (a -> b) -> NameMap a -> NameMap b
fmapNM = Map.mapKeys

fmapSM :: (Ord a, Ord b) => (a -> b) -> SigMap a -> SigMap b
fmapSM f (SigMap m1 m2) = SigMap (fmapNM f m1) m2

emptySSN :: SpecSymNames
emptySSN = SpecSymNames $ Map.empty

emptyNM :: SigMap a
emptyNM = SigMap Map.empty Map.empty

fromSignAndNamedSens:: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        lid -> sign -> [Named sentence] -> SigMap symbol
fromSignAndNamedSens lid sig nsens =
    let syms = Set.toAscList $ sym_of lid sig
        updFun _ _ = (1+)
        newName acc s = let (v, acc') = Map.insertLookupWithKey updFun s 1 acc
                        in (acc', (s, fromMaybe 0 v))
        symF acc x = let (acc', nn) = newName acc $ show $ sym_name lid x
                     in (acc', (x, nn))
        sensF acc x = let n = senAttr x
                          (acc', nn) = newName acc n in (acc', (n, nn))
        (cm, symL) = mapAccumL symF Map.empty syms
        (_, sensL) = mapAccumL sensF cm nsens
    in SigMap (Map.fromList symL) (Map.fromList sensL)


-- | Looks up the key in the map and if it doesn't exist it adds the
--   value for this key which results from the sign and sentences given
lookupWithInsert :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree => 
        lid -> sign -> [Named sentence] -> SpecSymNames -> (LibName, String)
             -> (SpecSymNames, SigMap symbol)
lookupWithInsert lid sig sens s@(SpecSymNames m) k =
    case Map.lookup k m of
      Just nm -> (s, fmapSM (\ (G_symbol lid1 sym)
                               -> coerceSymbol lid1 lid sym) nm)
      Nothing -> let nm = fromSignAndNamedSens lid sig sens
                 in ( SpecSymNames $ Map.insert k (fmapSM (G_symbol lid) nm) m
                    , nm)

--------------------- LibEnv traversal ---------------------

{-
foldWithAccu :: Monad m => (stat -> a -> m (stat, b)) -> stat -> [a]
             -> m (stat, b)
foldWithAccu f s l = do
  (s', res) <- foldM (foldFun f) (s, Nothing) l
  case res of Just out -> return (s', out)
              _ -> fail "foldWithAccu: No result"
      where foldFun f (x, _) y = do
                       (x', res) <- f x y
                       return (x', Just res)

mapWithAccu :: Monad m => (stat -> a -> m (stat, b)) -> stat -> [a]
             -> m (stat, [b])
mapWithAccu f s l = do
  foldM (foldFun f) (s, []) l
    where foldFun f (x, l') y = do
                       (x', res) <- f x y
                       return (x', res:l')

mapWithAccu :: (acc -> (x, z) -> m (acc, y)) -- Function of elt of input list
                                    -- and accumulator, returning new
                                    -- accumulator and elt of result list
          -> acc            -- Initial accumulator 
          -> [(x, z)]            -- Input list
          -> m (acc, [(x, y)])     -- Final accumulator and result list
mapWithAccu _ s []        =  return (s, [])
mapWithAccu f s (e@(x, z):xs) = do
  (s', y ) <- f s e
  (s'',ys) <- mapWithAccu f s' xs
  return (s'',(x, y):ys)
-}
                                         

-- first projection is the const function

-- | 2nd projection 
proj2 :: a -> b -> b
proj2 _ y = y

-- | map with accumulator and combine function
mapWithAC :: (Monad m) => (a -> b -> c) -> (s -> a -> m (s, b))
          -> s -> [a] -> m (s, [c])
mapWithAC _  _ s []        =  return (s, [])
mapWithAC g f s (x:xs) = do
  (s', y) <- f s x
  (s'',ys) <- mapWithAC g f s' xs
  return (s'', g x y:ys)


-- | Translates the given LibEnv to a list of OMDocs. If the first argument
--   is false only the DG to the given LibName is translated and returned.
exportLibEnv :: Bool -> LibName -> LibEnv -> Result [(LibName, OMDoc)]
exportLibEnv b ln le =
    let im = emptySSN
        cmbnF (x,_) y = (x,y)
        inputList = if b then Map.toList le else [(ln, lookupDGraph ln le)]
    in mapWithAC cmbnF exportDGraph im inputList >>= return . snd


-- | DGraph to OMDoc translation
exportDGraph :: Env -> (LibName, DGraph)
             -> Result (Env, OMDoc)
exportDGraph s (ln,dg) = do
  (s', theories) <- mapWithAC proj2 (exportNodeLab ln dg) s $ labNodesDG dg
  (s'', views) <- mapWithAC proj2 (exportLinkLab ln dg) s' $ labEdgesDG dg
  return (s'', OMDoc (show ln) $ (catMaybes theories) ++ (catMaybes views))


-- | DGNodeLab to TLTheory translation
exportNodeLab :: LibName -> DGraph -> Env -> LNode DGNodeLab
              -> Result (Env, Maybe TLElement)
exportNodeLab ln dg s (n, lb) =
  if isDGRef lb then return (s, Nothing) else
      case dgn_theory lb of
        G_theory lid (ExtSign sig _) _ sens _ ->
            let specname = getDGNodeName lb
                nsens = toNamedList sens
                -- get the sigmap from the SSM otherwise create and add it
                (s', sigm@(SigMap sm thm)) =
                    lookupWithInsert lid sig nsens s (ln, specname)
            in do
              (s'', imports) <- mapWithAC proj2 (makeImport ln dg) s'
                                $ innDG dg n
              -- create the OMDoc elements for the signature
              consts <- mapR (uncurry $ exportSymbol lid sigm) $ Map.toList sm
              -- create the OMDoc elements for the sentences
              thms <- mapR (exportSentence lid sigm) nsens
              return (s'', Just $ TLTheory specname (omdoc_metatheory lid)
                             $ concatMap concat [imports, consts, thms])


--------------------- Views and Morphisms ---------------------


makeImport :: LibName -> DGraph -> Env -> LEdge DGLinkLab
           -> Result (Env, [TCElement])
makeImport ln dg s (from, _, lbl)
    | isHidingEdge $ dgl_type lbl =
        do
          warning () ("Hiding link with " ++ show (dgl_id lbl) ++ " not exported.")
                  nullRange
          return (s, [])
    | isGlobalDef $ dgl_type lbl =
        do
          warning () ("Link with " ++ show (dgl_id lbl) ++ " exported.") nullRange
          return $ (s, [TCImport (showEdgeId $ dgl_id lbl)
                        (cdFromNode ln $ labDG dg from)
                        -- $ makeMorphism ln $ dgl_morphism lbl
                        dummy
                       ])
    | otherwise = return (s, [])

-- | Given a TheoremLink we output the view
exportLinkLab :: LibName -> DGraph -> Env -> LEdge DGLinkLab
              -> Result (Env, Maybe TLElement)
exportLinkLab ln dg s (from, to, lbl) = return $ case dgl_type lbl of
    ScopedLink Global (ThmLink _) _ ->
       (s, Just $ TLView (showEdgeId $ dgl_id lbl)
             (cdFromNode ln $ labDG dg from)
             (cdFromNode ln $ labDG dg to)
             -- . makeMorphism ln $ dgl_morphism lbl
             dummy
       )
    _ -> (s, Nothing)

makeMorphism :: forall lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
       (Logic lid1 sublogics1
         basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
        Logic lid2 sublogics2
         basic_spec2 sentence2 symb_items2 symb_map_items2
         sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
       (lid1, NameMap symbol1) -> (lid2, NameMap symbol2) -> GMorphism
                               -> Result TCElement
makeMorphism (l1, symM1) (l2, symM2) (GMorphism cid (ExtSign sig _) _ mor _)

-- l1 = logic1
-- l2 = logic2
-- lS = source-logic-cid
-- lT = target-logic-cid

-- metaknowledge: l1 = lS, l2 = lT

-- sigmap1 :: l1
-- sigmap2 :: l2

-- mor :: of target-logic-cid
-- symmap_of lT mor :: EndoMap symbolT

-- comorphism based map:
-- (sglElem (show cid) . map_symbol cid sig . coerceSymbol l1 lS) :: symbol1 -> symbolT

-- we need sigmap1 :: lT
-- we need sigmap2 :: lT
-- for sigmap2 we take a simple coerce
-- for sigmap1 we take a simple coerce if we know that l1 = l2
--             otherwise a comorphism fmap composed with a simple coerce 

    = let lS = sourceLogic cid
          lT = targetLogic cid
          f = if isIdComorphism (Comorphism cid)
              then coerceSymbol l1 lT
              else sglElem (show cid) . map_symbol cid sig . coerceSymbol l1 lS
          symM1' = fmapNM f symM1
          symM2' = fmapNM (coerceSymbol l2 lT) symM2
          morMap = symmap_of lT mor
      in return $ TCMorphism $ map (mapEntry lT symM1' symM2')
             $ Map.toList morMap


mapEntry :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree => 
        lid -> NameMap symbol -> NameMap symbol -> (symbol, symbol)
            -> (OMName, OMElement)
mapEntry lid m1 m2 (s1, s2) =
    let e = error "mapEntry: symbolmapping is missing"
        un1 = Map.findWithDefault e s1 m1
        un2 = Map.findWithDefault e s2 m2
    in (omName un1, simpleOMS un2)


-- | extracts the single element from singleton sets, fails otherwise
sglElem:: String -> Set.Set a -> a
sglElem s sa
    | Set.size sa > 1 =
        error $ "OMDocExport: comorphism symbol image > 1 in " ++ s
    | Set.null sa =
        error $ "OMDocExport: empty comorphism symbol image in " ++ s
    | otherwise = Set.findMin sa


--------------------- Names and CDs ---------------------

cdFromNode :: LibName -> DGNodeLab -> OMCD
cdFromNode ln lb =
-- special handling for library entries !??
    CD (getDGNodeName lb) $
    let omcdbase = show $ if isDGRef lb
                          then ref_libname $ nodeInfo lb
                          else ln
    in if omcdbase == "library" || omcdbase == ""
       then Nothing else Just omcdbase

omName :: UniqName -> OMName
omName = mkSimpleName . nameToString

simpleOMS :: UniqName -> OMElement
simpleOMS un = OMS (CD "" Nothing) $ omName un

--------------------- Symbols and Sentences ---------------------

exportSymbol :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree => 
        lid -> SigMap symbol -> symbol -> UniqName -> Result [TCElement]
exportSymbol lid (SigMap sm _) sym n = do
  let un = nameToString n
  symConst <- export_symToOmdoc lid sm sym un
  return $ [symConst] ++ (maybeToList $ notationFromUniqName n)

exportSentence :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree => 
        lid -> SigMap symbol -> Named sentence -> Result [TCElement]
exportSentence lid (SigMap sm thm) nsen = do
  omobj <- export_senToOmdoc lid sm $ sentence nsen
  let symRole = if isAxiom nsen && not (wasTheorem nsen) then Axiom
                else Theorem
      thmName = senAttr nsen
      un = Map.findWithDefault
           (error $ concat [ "exportSentence: mapping for "
                           , thmName, " is missing!"]) thmName thm
      omname = nameToString un
  return $ [TCSymbol omname omobj symRole Nothing]
             ++ (maybeToList $ notationFromUniqName un)

notationFromUniqName :: UniqName -> Maybe TCElement
notationFromUniqName un =
    let n = nameToString un
        orign = fst un 
    in if n == orign then Nothing else Just $ TCNotation (mkSimpleName n) orign
