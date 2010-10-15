{-# LANGUAGE ExistentialQuantification #-}
{- |
Module      :  $Header$
Description :  Exports a development graph to an omdoc structure
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Export of a given development graph to an OMDoc structure
which can then be stored as xml via the "OMDoc.XmlInterface".

The export requires the following interface functions to be instantiated
for each logic

Sentences:
sym_of (needed for symlist_of), sym_name, symmap_of

Logic:
omdoc_metatheory, export_symToOmdoc, export_senToOmdoc

This function has a default implementation which is sufficient
in many cases:
export_theoryToOmdoc

-}

module OMDoc.Export where

import Logic.Logic ( Logic( omdoc_metatheory, export_theoryToOmdoc
                          , export_symToOmdoc, export_senToOmdoc)
                   , Sentences(sym_name, symmap_of), symlist_of
                   , SyntaxTable, syntaxTable)
import Logic.Coerce
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism

import Static.DevGraph
import Static.GTheory

import Common.Result
import Common.ExtSign
import Common.Id
import Common.Utils
import Common.LibName
import Common.AS_Annotation
import Common.Prec (maxWeight, precMap)

import Driver.Options (downloadExtensions)
import Driver.WriteLibDefn (getFilePrefixGeneric)

import OMDoc.DataTypes

import Data.Graph.Inductive.Graph
import Data.Maybe
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

import System.FilePath

-- * Name Mapping interface

-- | A structure similar to SigMap but with a Grothendieck map instead.
-- The numbered UniqName just stores the original position of the symbol
-- in the signature, and will be exploited in order to output the symbols
-- in the correct dependency order.
data GSigMap = GSigMap (G_symbolmap (Int, UniqName)) (NameMap String)

-- | We need this type to store the original dependency order.
-- This type is the logic dependent analogue to the GSigMap
type NumberedSigMap a = (Map.Map a (Int, UniqName), NameMap String)

-- | Removes the numbering from the symbol map
nSigMapToSigMap :: NumberedSigMap a -> SigMap a
nSigMapToSigMap (nMap, sMap) = SigMap (Map.map snd nMap) sMap

-- | Computes a dependency sorted (symbol - unique name) list
nSigMapToOrderedList :: NumberedSigMap a -> [(a, UniqName)]
nSigMapToOrderedList (nMap, _) = let
    compByPos (_, (pos1, _)) (_, (pos2, _)) = compare pos1 pos2
    sortedList = sortBy compByPos $ Map.toList nMap
    in map (\ (a, x) -> (a, snd x)) sortedList


-- | Mapping of Specs to SigMaps
newtype SpecSymNames = SpecSymNames (Map.Map (LibName, String) GSigMap)


-- | The export environment
data ExpEnv = ExpEnv { getSSN :: SpecSymNames
                     , getInitialLN :: LibName
                     , getFilePathMapping :: Map.Map LibName FilePath }

fmapNM :: (Ord a, Ord b) => (a -> b) -> NameMap a -> NameMap b
fmapNM = Map.mapKeys

emptyEnv :: LibName -> ExpEnv
emptyEnv ln = ExpEnv { getSSN = SpecSymNames $ Map.empty
                     , getInitialLN = ln
                     , getFilePathMapping = Map.empty }

fromSignAndNamedSens :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        lid -> sign -> [Named sentence] -> NumberedSigMap symbol
fromSignAndNamedSens lid sig nsens =
    let syms = symlist_of lid sig
        -- The accumulator var is a map of names to integer values designating
        -- the next identifier to use for this name to make it unique.
        -- acc: Map String Int
        newName acc s =
            let (v, acc') = Map.insertLookupWithKey (const (+)) s 1 acc
            in (acc', (s, fromMaybe 0 v))
        -- We need to store in addition to the name-int-map an integer to
        -- increment in order to remember the original order of the signature
        -- elements after having destroyed it by making a map from the list.
        -- for that reason we use the following accumvar:
        -- acc: (Int, Map String Int)
        symF (i, acc) x = let (acc', nn) = newName acc $ show $ sym_name lid x
                          in ((i + 1, acc'), (x, (i, nn)))
        sensF acc x = let n = senAttr x
                          (acc', nn) = newName acc n in (acc', (n, nn))
        (cm, symL) = mapAccumL symF (0, Map.empty) syms
        (_, sensL) = mapAccumL sensF (snd cm) nsens
    in (Map.fromList symL, Map.fromList sensL)


-- | Looks up the key in the map and if it doesn't exist adds the
-- value for this key which results from the given sign and sentences.
lookupWithInsert :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        lid -> sign -> [Named sentence] -> ExpEnv -> (LibName, String)
             -> (ExpEnv, NumberedSigMap symbol)
lookupWithInsert lid sig sens s k =
    let SpecSymNames m = getSSN s in
    case Map.lookup k m of
      Just (GSigMap (G_symbolmap lid1 sm) nm) ->
          (s, (coerceSymbolmap lid1 lid sm, nm))
      Nothing -> let nsigm@(sm, nm) = fromSignAndNamedSens lid sig sens
                     gsm = GSigMap (G_symbolmap lid sm) nm
                 in ( s { getSSN = SpecSymNames $ Map.insert k gsm m }, nsigm)

-- * LibEnv traversal

-- | Translates the given LibEnv to a list of OMDocs. If the first argument
-- is false only the DG to the given LibName is translated and returned.
exportLibEnv :: Bool -- recursive
             -> FilePath -- outdir
             -> LibName -> LibEnv
             -> Result [(LibName, OMDoc)]
exportLibEnv b odir ln le =
    let cmbnF (x, _) y = (x, y)
        inputList = if b then Map.toList le else [(ln, lookupDGraph ln le)]
        fpm = initFilePathMapping odir le
        im = (emptyEnv ln){ getFilePathMapping = fpm }
        f (ln', o) = let fp = Map.findWithDefault
                              (error $ "exportLibEnv: filepath not mapped")
                              ln' fpm
                         mt = getModTime $ getLibId ln'
                     in (setFilePath fp mt ln', o)
    in do
      l <- mapAccumLCM cmbnF (exportDGraph le) im inputList >>= return . snd
      return $ map f l

initFilePathMapping :: FilePath -> LibEnv -> Map.Map LibName FilePath
initFilePathMapping fp le =
    let f k _ = (snd $ getFilePrefixGeneric downloadExtensions fp
                         $ getFilePath k) ++ ".omdoc"
    in Map.mapWithKey f le

-- | DGraph to OMDoc translation
exportDGraph :: LibEnv -> ExpEnv -> (LibName, DGraph) -> Result (ExpEnv, OMDoc)
exportDGraph le s (ln, dg) = do
  (s', theories) <- mapAccumLM (exportNodeLab le ln dg) s
                    $ topsortedNodes dg
  (s'', views) <- mapAccumLM (exportLinkLab le ln dg) s' $ labEdgesDG dg
  return (s'', OMDoc (show $ getLibId ln)
                 $ (catMaybes theories) ++ (catMaybes views))


-- | DGNodeLab to TLTheory translation
exportNodeLab :: LibEnv -> LibName -> DGraph -> ExpEnv -> LNode DGNodeLab
              -> Result (ExpEnv, Maybe TLElement)
exportNodeLab le ln dg s (n, lb) =
  if isDGRef lb then return (s, Nothing) else
      let (lb', ln') = getNodeData le ln lb in
      case dgn_theory lb' of
        G_theory lid (ExtSign sig _) _ sens _ ->
            do
              let sn = getDGNodeName lb'
                  nsens = toNamedList sens
                  (s', nsigm) = lookupWithInsert lid sig nsens s (ln', sn)
                  sigm@(SigMap nm _) = nSigMapToSigMap nsigm

              -- imports is a list of Maybe (triples, exported-symbol
              -- set) pairs as described in 'makeImportMapping'. We
              -- construct the concrete OMImages later (see
              -- makeImport) in order to prevent multiple imported
              -- constants to be declared by open as a new constant.
              -- We must use open for the first occurence and conass
              -- for the others, i.e., Left resp. Right constructors
              -- of the OMImage datatype
              (s'', imports) <-
                  mapAccumLM (makeImportMapping le ln dg (lid, nm)) s'
                                 $ innDG dg n

              -- mappingL: list of the triples described above
              -- symsetL: used to compute the local symbols (not imported)
              let (mappingL, symsetL) = unzip $ catMaybes imports
                  (_, importL) = mapAccumL makeImport Set.empty mappingL
                  mSynTbl = syntaxTable lid sig
              extra <- export_theoryToOmdoc lid sigm sig nsens
              consts <- mapR (uncurry $ exportSymbol lid sigm mSynTbl symsetL)
                        $ nSigMapToOrderedList nsigm
              -- create the OMDoc elements for the sentences
              thms <- mapR (exportSentence lid sigm) nsens
              return (s'', Just $ TLTheory sn (omdoc_metatheory lid)
                             $ concat
                                   [importL, concat consts, extra, concat thms])


-- * Views and Morphisms

-- Node lookup for handling ref nodes
getNodeData :: LibEnv -> LibName -> DGNodeLab -> (DGNodeLab, LibName)
getNodeData le ln lb =
    if isDGRef lb then
        let ni = nodeInfo lb
            lnRef = ref_libname ni
            dg' = Map.findWithDefault
                  (error $ "getNodeData: Lib not found: " ++ show lnRef)
                  lnRef le
        in (labDG dg' $ ref_node ni, lnRef)
    else (lb, ln)

-- See the comment in exportNodeLab for details about this function.
-- The set is only to accumulate the mapped symbols (the targets, not
-- the sources!) in order to decide whether to just map the symbol to
-- a previously mapped symbol or to create an alias!
makeImport :: Set.Set UniqName -> (String, OMCD, [(OMName, UniqName)])
           -> (Set.Set UniqName, TCElement)
makeImport s (n, cd, mapping) =
    let f s' p@(_, un)
            | Set.notMember un s' =
                (Set.insert un s', makeMorphismEntry True p)
            | otherwise = (s', makeMorphismEntry False p)
        (s'', morph) = mapAccumL f s mapping
    in (s'', TCImport n cd morph)

-- | If the link is a global definition link we compute the Import
-- and return also the set of (by the link) exported symbols.
makeImportMapping :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        LibEnv -> LibName -> DGraph -> (lid, NameMap symbol) -> ExpEnv
               -> LEdge DGLinkLab
               -> Result (ExpEnv
                          -- the triple consists of:
                          --   name of the import
                          --   target CD
                          --   actual mapping as returned by makeMorphism
                         , Maybe ( (String, OMCD, [(OMName, UniqName)])
                                 -- symbols exported by the morphism
                                 , Set.Set symbol))
makeImportMapping le ln dg toInfo s (from, _, lbl)
    | isHidingEdge $ dgl_type lbl =
        warning () (concat [ "Hiding link with ", show (dgl_id lbl)
                           , " not exported."]) nullRange
                    >> return (s, Nothing)
    | isLocalDef $ dgl_type lbl =
        warning () (concat [ "Local def-link with ", show (dgl_id lbl)
                           , " not exported."]) nullRange
                    >> return (s, Nothing)
    | isGlobalDef $ dgl_type lbl =
        let (lb', ln') = getNodeData le ln $ labDG dg from
            edgName = getDGLinkName lbl
            impname = if null edgName
                      then "gn_imp_" ++ showEdgeId (dgl_id lbl)
                      else edgName
        in
         case dgn_theory lb' of
          G_theory lid (ExtSign sig _) _ sens _ ->
              do
                let sn = getDGNodeName lb'
                    nsens = toNamedList sens
                    (s', nsigm) = lookupWithInsert lid sig nsens s (ln', sn)
                    SigMap nm _ = nSigMapToSigMap nsigm
                (morph, expSymbs) <-
                    makeMorphism (lid, nm) toInfo $ dgl_morphism lbl
                cd <- mkCD s' ln ln' sn
                return (s', Just ((impname, cd, morph), expSymbs))
    | otherwise = return (s, Nothing)

-- | Given a TheoremLink we output the view
exportLinkLab :: LibEnv -> LibName -> DGraph -> ExpEnv -> LEdge DGLinkLab
              -> Result (ExpEnv, Maybe TLElement)
exportLinkLab le ln dg s (from, to, lbl) =
    let ltyp = dgl_type lbl
        gmorph = dgl_morphism lbl
        edgName = getDGLinkName lbl
        viewname = if null edgName
                   then "gn_vn_" ++ showEdgeId (dgl_id lbl)
                   else edgName
        (lb1, ln1) = getNodeData le ln $ labDG dg from
        (lb2, ln2) = getNodeData le ln $ labDG dg to
        noExport = return (s, Nothing)
        withWarning lt = warning () (concat [ "exportLinkLab: ", lt
                                           , " link with ", show (dgl_id lbl)
                                           , " not exported."])
                        nullRange >> noExport
    in case (isDefEdge ltyp, isLocalEdge ltyp, isHidingEdge ltyp) of
         (True, _, _) -> noExport
         (_, True, _) -> withWarning "Local"
         (_, _, True) -> withWarning "Hiding"
         _ ->
             case (dgn_theory lb1, dgn_theory lb2) of
               { ((G_theory lid1 (ExtSign sig1 _) _ sens1 _) ,
                  (G_theory lid2 (ExtSign sig2 _) _ sens2 _ )) ->
                 do
                   let sn1 = getDGNodeName lb1
                       sn2 = getDGNodeName lb2
                       nsens1 = toNamedList sens1
                       nsens2 = toNamedList sens2
                       (s', nsigm1) =
                           lookupWithInsert lid1 sig1 nsens1 s (ln1, sn1)
                       (s'', nsigm2) =
                           lookupWithInsert lid2 sig2 nsens2 s' (ln2, sn2)
                       SigMap nm1 _ = nSigMapToSigMap nsigm1
                       SigMap nm2 _ = nSigMapToSigMap nsigm2
                   (preMorph, _) <-
                       makeMorphism (lid1, nm1) (lid2, nm2) gmorph
                   let morph = map (makeMorphismEntry False) preMorph
                   cd1 <- mkCD s'' ln ln1 sn1
                   cd2 <- mkCD s'' ln ln2 sn2
                   return (s'', Just $ TLView viewname cd1 cd2 morph) }


makeMorphismEntry :: Bool -> (OMName, UniqName)
                -> (OMName, OMImage)
makeMorphismEntry useOpen (n, un) =
    (n, if useOpen then Left $ nameToString un else Right $ simpleOMS un)

-- | From the given GMorphism we compute the symbol-mapping and return
-- also the set of (by the morphism) exported symbols (= image of morphism)
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
       (lid1, NameMap symbol1) -> (lid2, NameMap symbol2)
                               -> GMorphism
                               -> Result ([(OMName, UniqName)], Set.Set symbol2)
makeMorphism (l1, symM1) (l2, symM2)
                 (GMorphism cid (ExtSign sig _) _ mor _)

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
-- (sglElem (show cid) . map_symbol cid sig . coerceSymbol l1 lS)
-- :: symbol1 -> symbolT

-- we need sigmap1 :: lT
-- we need sigmap2 :: lT
-- for sigmap2 we take a simple coerce
-- for sigmap1 we take a simple coerce if we know that l1 = l2
-- otherwise a comorphism fmap composed with a simple coerce

    = let lS = sourceLogic cid
          lT = targetLogic cid
          f = if isIdComorphism (Comorphism cid)
              then coerceSymbol l1 lT
              else sglElem (show cid) . map_symbol cid sig . coerceSymbol l1 lS
          symM1' = fmapNM f symM1
          symM2' = fmapNM (coerceSymbol l2 lT) symM2
          mormap = symmap_of lT mor
          expSymbs = Set.fromList $ Map.elems $ coerceMapofsymbol lT l2 mormap
      in return (map (mapEntry lT symM1' symM2')
                         $ Map.toList mormap, expSymbs)


mapEntry :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        lid -> NameMap symbol -> NameMap symbol
            -> (symbol, symbol)
            -> (OMName, UniqName)
mapEntry _ m1 m2 (s1, s2) =
    let e = error "mapEntry: symbolmapping is missing"
        un1 = Map.findWithDefault e s1 m1
        un2 = Map.findWithDefault e s2 m2
    in (omName un1, un2)


-- | extracts the single element from singleton sets, fails otherwise
sglElem :: String -> Set.Set a -> a
sglElem s sa
    | Set.size sa > 1 =
        error $ "OMDocExport: comorphism symbol image > 1 in " ++ s
    | Set.null sa =
        error $ "OMDocExport: empty comorphism symbol image in " ++ s
    | otherwise = Set.findMin sa


-- * Names and CDs
mkCD :: ExpEnv -> LibName -> LibName -> String -> Result OMCD
mkCD s lnCurr ln sn =
    let m = getFilePathMapping s
        fp = Map.findWithDefault
             (error $ "mkCD: no entry for " ++ show ln) ln m
        fpCurr = Map.findWithDefault
                 (error $ "mkCD: no current entry for " ++ show lnCurr) lnCurr m
        -- compute the relative path
        fpRel = makeRelativeDesc (takeDirectory fpCurr) fp
        fpRel' = if isAbsolute fpRel then "file://" ++ fpRel else fpRel
        base = if lnCurr == ln then [] else [fpRel']
    in return $ CD $ [sn] ++ base

-- * Symbols and Sentences
exportSymbol :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        lid -> SigMap symbol -> Maybe SyntaxTable -> [Set.Set symbol] -> symbol
            -> UniqName -> Result [TCElement]
exportSymbol lid (SigMap sm _) mSynTbl sl sym n =
    let symNotation = mkNotation n $ fmap (\ x -> (sym_name lid sym,x)) mSynTbl
    in if all (Set.notMember sym) sl
       then do
         symConst <- export_symToOmdoc lid sm sym $ nameToString n
         return $ [symConst] ++ symNotation
       else return symNotation

exportSentence :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        lid -> SigMap symbol -> Named sentence -> Result [TCElement]
exportSentence lid (SigMap sm thm) nsen = do
  omobjOrAdt <- export_senToOmdoc lid sm $ sentence nsen
  let symRole = if isAxiom nsen && not (wasTheorem nsen) then Axiom
                else Theorem
      thmName = senAttr nsen
      un = Map.findWithDefault
           (error $ concat [ "exportSentence: mapping for "
                           , thmName, " is missing!"]) thmName thm
      omname = nameToString un
  case omobjOrAdt of
    Left adt ->
        warning () ("Name for adt not exported: " ++ show omname) nullRange
                    >> return [adt]
    Right omobj ->
        return $ [TCSymbol omname omobj symRole Nothing]
                   ++ mkNotation un Nothing

-- | We only export simple constant-notations if the OMDoc element name differs
-- from the hets-name.
-- If the placecount of the id (if provided) is nonzero then we export the
-- application-notation elements for pretty printing in OMDoc.
mkNotation :: UniqName -> Maybe (Id, SyntaxTable) -> [TCElement]
mkNotation un mIdSTbl =
    let n = nameToString un
        orign = fst un
        qn = mkSimpleQualName un
        l = if n == orign then []
            else [TCNotation qn orign]
    in case mIdSTbl of
         Just (symid, (pMap, aMap))
             | isMixfix symid ->
                 let p = Map.findWithDefault (maxWeight pMap) symid
                         $ precMap pMap
                     -- we use numbers instead of associativity values
                     a = case Map.lookup symid aMap of
                           Just ALeft -> -1
                           Just ARight -> 1
                           _ -> 0
                 in mkApplicationNotation qn symid p a : l
             | otherwise -> l
         _ -> l

-- | This function requires mixfix Ids as input and generates Notation
-- structures, see 'OMDoc.DataTypes'.
mkApplicationNotation :: OMQualName -> Id -> Int -> Int -> TCElement
mkApplicationNotation qn symid@(Id toks _ _) prec asc
    | placeCount symid == 1 =
        case toks of [a, b]
                         | isPlace a
                             -> mkSmartNotation qn (tokStr b) Postfix prec asc
                         | otherwise
                             -> mkSmartNotation qn (tokStr a) Prefix prec asc
                     _ -> mkFlexibleNotation qn symid prec asc
    | placeCount symid == 2 = 
        case toks of [_, b, _]
                         | not (isPlace b)
                             -> mkSmartNotation qn (tokStr b) Infix prec asc
                         | otherwise
                             -> mkFlexibleNotation qn symid prec asc
                     _ -> mkFlexibleNotation qn symid prec asc
    | otherwise = mkFlexibleNotation qn symid prec asc

-- | See OMDoc.DataTypes for a description of SmartNotation. We set
-- the number of implicit arguments to 0. In presence of associativity
-- and infix we generate flexible notation as described in the
-- Isabelle2009 reference manual §6.1.3: Infixes.
mkSmartNotation :: OMQualName -> String -> Fixity -> Int -> Int -> TCElement
mkSmartNotation qn op fx prec asc =
    let f p1 p2 = TCFlexibleNotation qn prec
                  [ArgComp 1 p1, TextComp op, ArgComp 2 p2]
    in case fx of
         Infix | asc > 0 -> f (prec+1) prec
               | asc < 0 -> f prec (prec+1)
               | otherwise -> TCSmartNotation qn fx prec 0
         _ -> TCSmartNotation qn fx prec 0


mkFlexibleNotation :: OMQualName -> Id -> Int -> Int -> TCElement
mkFlexibleNotation qn opid prec _ =
    let f acc tok = if isPlace tok then (acc+1, ArgComp acc prec)
                    else (acc, TextComp $ tokStr tok)
    in TCFlexibleNotation qn prec $ snd $ mapAccumL f 1 $ getTokens opid

