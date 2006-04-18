{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (overlapping instances, dynamics, existentials)

The Grothendieck logic is defined to be the
   heterogeneous logic over the logic graph.
   This will be the logic over which the data
   structures and algorithms for specification in-the-large
   are built.

   This module heavily works with existential types, see
   <http://haskell.org/hawiki/ExistentialTypes> and chapter 7 of /Heterogeneous
   specification and the heterogeneous tool set/
   (<http://www.tzi.de/~till/papers/habil.ps>).

   References:

   R. Diaconescu:
   Grothendieck institutions
   J. applied categorical structures 10, 2002, p. 383-402.

   T. Mossakowski:
   Comorphism-based Grothendieck institutions.
   In K. Diks, W. Rytter (Eds.), Mathematical foundations of computer science,
   LNCS 2420, pp. 593-604

   T. Mossakowski:
   Heterogeneous specification and the heterogeneous tool set.

   Todo:
   compComorphism: cancellation of id comorphisms if target sublogic is
                   not increased
   gWeaklyAmalgamableCocone
   Transportability for heterogeneous morphisms
-}

module Logic.Grothendieck where

import Logic.Logic
import Logic.Prover
import Logic.Comorphism
import Logic.Morphism
import Logic.Coerce
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Graph as Tree
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Result
import Common.Utils
import Common.DynamicUtils
import qualified Data.List as List
import Data.Maybe
import Control.Monad (foldM, unless)

------------------------------------------------------------------
--"Grothendieck" versions of the various parts of type class Logic
------------------------------------------------------------------

-- | Grothendieck basic specifications
data G_basic_spec = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_basic_spec lid basic_spec

instance Show G_basic_spec where
    show (G_basic_spec _ s) = show s

instance PrettyPrint G_basic_spec where
    printText0 ga (G_basic_spec _ s) = printText0 ga s

-- | Grothendieck signatures
data G_sign = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_sign lid sign

tyconG_sign :: TyCon
tyconG_sign = mkTyCon "Logic.Grothendieck.G_sign"
instance Typeable G_sign where
  typeOf _ = mkTyConApp tyconG_sign []

instance Eq G_sign where
  (G_sign i1 sigma1) == (G_sign i2 sigma2) =
     coerceSign i1 i2 "Eq G_sign" sigma1 == Just sigma2

-- | prefer a faster subsignature test if possible
isHomSubGsign :: G_sign -> G_sign -> Bool
isHomSubGsign (G_sign i1 sigma1) (G_sign i2 sigma2) =
    maybe False (is_subsig i1 sigma1) $ coerceSign i2 i1 "is_subgsign" sigma2

isSubGsign :: LogicGraph -> G_sign -> G_sign -> Bool
isSubGsign lg (G_sign lid1 sigma1) (G_sign lid2 sigma2) =
  Just True ==
  do Comorphism cid <- resultToMaybe $
                         logicInclusion lg (Logic lid1) (Logic lid2)
     sigma1' <- coerceSign lid1 (sourceLogic cid)
                "Grothendieck.isSubGsign: cannot happen" sigma1
     sigma2' <- coerceSign lid2 (targetLogic cid)
                "Grothendieck.isSubGsign: cannot happen" sigma2
     sigma1t <- resultToMaybe $ map_sign cid sigma1'
     return $ is_subsig (targetLogic cid) (fst sigma1t) sigma2'

instance Show G_sign where
    show (G_sign _ s) = show s

instance PrettyPrint G_sign where
    printText0 ga (G_sign _ s) = printText0 ga s

langNameSig :: G_sign -> String
langNameSig (G_sign lid _) = language_name lid

-- | Grothendieck signature lists
data G_sign_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_sign_list lid [sign]

-- | Grothendieck extended signatures
data G_ext_sign = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_ext_sign lid sign (Set.Set symbol)

-- | Grothendieck symbols
data G_symbol = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
  G_symbol lid symbol

instance Show G_symbol where
    show (G_symbol _ s) = show s

instance PrettyPrint G_symbol where
    printText0 ga (G_symbol _ s) = printText0 ga s

instance Eq G_symbol where
  (G_symbol i1 s1) == (G_symbol i2 s2) =
     language_name i1 == language_name i2 && coerceSymbol i1 i2 s1 == s2

-- | Grothendieck symbol lists
data G_symb_items_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
        G_symb_items_list lid [symb_items]

instance Show G_symb_items_list where
    show (G_symb_items_list _ l) = show l

instance PrettyPrint G_symb_items_list where
    printText0 ga (G_symb_items_list _ l) =
        fsep $ punctuate comma $ map (printText0 ga) l

instance Eq G_symb_items_list where
  (G_symb_items_list i1 s1) == (G_symb_items_list i2 s2) =
     coerceSymbItemsList i1 i2 "Eq G_symb_items_list" s1 == Just s2

-- | Grothendieck symbol maps
data G_symb_map_items_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
        G_symb_map_items_list lid [symb_map_items]

instance Show G_symb_map_items_list where
    show (G_symb_map_items_list _ l) = show l

instance PrettyPrint G_symb_map_items_list where
    printText0 ga (G_symb_map_items_list _ l) =
        fsep $ punctuate comma $ map (printText0 ga) l

instance Eq G_symb_map_items_list where
  (G_symb_map_items_list i1 s1) == (G_symb_map_items_list i2 s2) =
     coerceSymbMapItemsList i1 i2 "Eq G_symb_map_items_list" s1 == Just s2

-- | Grothendieck diagrams
data G_diagram = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
        G_diagram lid (Tree.Gr sign morphism)

-- | Grothendieck sublogics
data G_sublogics = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_sublogics lid sublogics

tyconG_sublogics :: TyCon
tyconG_sublogics = mkTyCon "Logic.Grothendieck.G_sublogics"
instance Typeable G_sublogics where
  typeOf _ = mkTyConApp tyconG_sublogics []

instance Show G_sublogics where
    show (G_sublogics lid sub) = case sublogic_names lid sub of
      [] -> error "show G_sublogics"
      h : _ -> show lid ++ "." ++ h

instance Eq G_sublogics where
    (G_sublogics lid1 l1) == (G_sublogics lid2 l2) =
       language_name lid1 == language_name lid2
          && coerceSublogic lid1 lid2 l1 == l2

isProperSublogic :: G_sublogics -> G_sublogics -> Bool
isProperSublogic a@(G_sublogics lid1 l1) b@(G_sublogics lid2 l2) =
    isSubElem (coerceSublogic lid1 lid2 l1) l2 && a /= b

-- | Homogeneous Grothendieck signature morphisms
data G_morphism = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_morphism lid morphism

instance Show G_morphism where
    show (G_morphism _ l) = show l

----------------------------------------------------------------
-- Existential types for the logic graph
----------------------------------------------------------------

--- Comorphisms ----

-- | Existential type for comorphisms
data AnyComorphism = forall cid lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
      Comorphism cid
                 lid1 sublogics1 basic_spec1 sentence1
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      Comorphism cid

instance Eq AnyComorphism where
  Comorphism cid1 == Comorphism cid2 =
     constituents cid1 == constituents cid2
  -- need to be refined, using comorphism translations !!!

instance Show AnyComorphism where
  show (Comorphism cid) =
    language_name cid
    ++" : "++language_name (sourceLogic cid)
    ++" -> "++language_name (targetLogic cid)

tyconAnyComorphism :: TyCon
tyconAnyComorphism = mkTyCon "Logic.Grothendieck.AnyComorphism"
instance Typeable AnyComorphism where
  typeOf _ = mkTyConApp tyconAnyComorphism []

-- | compute the identity comorphism for a logic
idComorphism :: AnyLogic -> AnyComorphism
idComorphism (Logic lid) = Comorphism (IdComorphism lid (top_sublogic lid))

-- | Test whether a comporphism is the identity
isIdComorphism :: AnyComorphism -> Bool
isIdComorphism (Comorphism cid) =
  constituents cid == []

-- | Compose comorphisms
compComorphism :: Monad m => AnyComorphism -> AnyComorphism -> m AnyComorphism
compComorphism (Comorphism cid1) (Comorphism cid2) =
   let l1 = targetLogic cid1
       l2 = sourceLogic cid2 in
   if language_name l1 == language_name l2 then
      if isSubElem (coerceSublogic l1 l2 $ targetSublogic cid1)
            $ sourceSublogic cid2
       then {- case (isIdComorphism cm1,isIdComorphism cm2) of
         (True,_) -> return cm2
         (_,True) -> return cm1
         _ ->  -} return $ Comorphism (CompComorphism cid1 cid2)
       else fail ("Sublogic mismatch in composition of "++language_name cid1++
                  " and "++language_name cid2)
    else fail ("Logic mismatch in composition of "++language_name cid1++
                     " and "++language_name cid2)

-- | check if sublogic fits for comorphism
lessSublogicComor :: G_sublogics -> AnyComorphism -> Bool
lessSublogicComor (G_sublogics lid1 sub1) (Comorphism cid) =
    let lid2 = sourceLogic cid
    in language_name lid2 == language_name lid1
           && isSubElem (coerceSublogic lid1 lid2 sub1) (sourceSublogic cid)

--- Morphisms ---

-- | Existential type for morphisms
data AnyMorphism = forall cid lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
      Morphism cid
                 lid1 sublogics1 basic_spec1 sentence1
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      Morphism cid

{-
instance Eq AnyMorphism where
  Morphism cid1 == Morphism cid2 =
     constituents cid1 == constituents cid2
  -- need to be refined, using morphism translations !!!


instance Show AnyMorphism where
  show (Morphism cid) =
    language_name cid
    ++" : "++language_name (sourceLogic cid)
    ++" -> "++language_name (targetLogic cid)
-}

tyconAnyMorphism :: TyCon
tyconAnyMorphism = mkTyCon "Logic.Grothendieck.AnyMorphism"
instance Typeable AnyMorphism where
  typeOf _ = mkTyConApp tyconAnyMorphism []


-- | Logic graph
data LogicGraph = LogicGraph {
                    logics :: Map.Map String AnyLogic,
                    comorphisms :: Map.Map String AnyComorphism,
                    inclusions :: Map.Map (String,String) AnyComorphism,
                    unions :: Map.Map (String,String) (AnyComorphism,AnyComorphism)
                  }

emptyLogicGraph :: LogicGraph
emptyLogicGraph = LogicGraph Map.empty Map.empty Map.empty Map.empty

-- | find a logic in a logic graph
lookupLogic :: Monad m => String -> String -> LogicGraph -> m AnyLogic
lookupLogic error_prefix logname logicGraph =
    case Map.lookup logname (logics logicGraph) of
    Nothing -> fail (error_prefix++" in LogicGraph logic \""
                      ++logname++"\" unknown")
    Just lid -> return lid

-- | union to two logics
logicUnion :: LogicGraph -> AnyLogic -> AnyLogic -> Result (AnyComorphism,AnyComorphism)
logicUnion lg l1@(Logic lid1) l2@(Logic lid2) =
  case logicInclusion lg l1 l2 of
    Result _ (Just c) -> return (c,idComorphism l2)
    _ -> case logicInclusion lg l2 l1 of
      Result _ (Just c) -> return (idComorphism l1,c)
      _ -> case Map.lookup (ln1,ln2) (unions lg) of
        Just u -> return u
        Nothing -> case Map.lookup (ln2,ln1) (unions lg) of
          Just (c2,c1) -> return (c1,c2)
          Nothing -> fail ("Union of logics "++ln1++" and "++ln2++" does not exist")
   where ln1 = language_name lid1
         ln2 = language_name lid2

-- | find a comorphism in a logic graph
lookupComorphism :: Monad m => String -> LogicGraph -> m AnyComorphism
lookupComorphism coname logicGraph = do
  let nameList = splitOn ';' coname
  cs <- sequence $ map lookupN nameList
  case cs of
    c:cs1 -> foldM compComorphism c cs1
    _ -> fail ("Illgegal comorphism name: "++coname)
  where
  lookupN name =
    case name of
      'i':'d':'_':logic -> do
         let mainLogic = takeWhile (/= '.') logic
         l <- maybe (fail ("Cannot find Logic "++mainLogic)) return
                 $ Map.lookup mainLogic (logics logicGraph)
         return $ idComorphism l
      _ -> maybe (fail ("Cannot find logic comorphism "++name)) return
             $ Map.lookup name (comorphisms logicGraph)

------------------------------------------------------------------
-- The Grothendieck signature category
------------------------------------------------------------------

-- | Grothendieck signature morphisms
data GMorphism = forall cid lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
      Comorphism cid
                 lid1 sublogics1 basic_spec1 sentence1
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
  GMorphism cid sign1 morphism2

instance Eq GMorphism where
  GMorphism cid1 sigma1 mor1 == GMorphism cid2 sigma2 mor2
     = Comorphism cid1 == Comorphism cid2
       && coerceSign (sourceLogic cid1) (sourceLogic cid2)
                  "Eq GMorphism.coerceSign" sigma1 == Just sigma2
       && coerceMorphism (targetLogic cid1) (targetLogic cid2)
                   "Eq GMorphism.coerceMorphism" mor1 == Just mor2

isHomogeneous :: GMorphism -> Bool
isHomogeneous (GMorphism cid _ _) =
  isIdComorphism (Comorphism cid)

data Grothendieck = Grothendieck deriving Show

instance Language Grothendieck

instance Show GMorphism where
    show (GMorphism cid s m) = show cid ++ "(" ++ show s ++ ")" ++ show m

instance PrettyPrint GMorphism where
    printText0 ga (GMorphism cid s m) =
      ptext (show cid)
      <+> -- ptext ":" <+> ptext (show (sourceLogic cid)) <+>
      -- ptext "->" <+> ptext (show (targetLogic cid)) <+>
      ptext "(" <+> printText0 ga s <+> ptext ")"
      $$
      printText0 ga m

instance Category Grothendieck G_sign GMorphism where
  ide _ (G_sign lid sigma) =
    GMorphism (IdComorphism lid (top_sublogic lid)) sigma (ide lid sigma)
  comp _
       (GMorphism r1 sigma1 mor1)
       (GMorphism r2 _sigma2 mor2) =
    do let lid2 = targetLogic r1
           lid3 = sourceLogic r2
           lid4 = targetLogic r2
       mor1' <- coerceMorphism lid2 lid3 "Grothendieck.comp" mor1
       mor1'' <- map_morphism r2 mor1'
       mor <- comp lid4 mor1'' mor2
       return (GMorphism (CompComorphism r1 r2) sigma1 mor)
  dom _ (GMorphism r sigma _mor) =
    G_sign (sourceLogic r) sigma
  cod _ (GMorphism r _sigma mor) =
    G_sign lid2 (cod lid2 mor)
    where lid2 = targetLogic r
  legal_obj _ (G_sign lid sigma) = legal_obj lid sigma
  legal_mor _ (GMorphism r sigma mor) =
    legal_mor lid2 mor &&
    case maybeResult $ map_sign r sigma of
      Just (sigma',_) -> sigma' == cod lid2 mor
      Nothing -> False
    where lid2 = targetLogic r


-- | Embedding of homogeneous signature morphisms as Grothendieck sig mors
gEmbed :: G_morphism -> GMorphism
gEmbed (G_morphism lid mor) =
  GMorphism (IdComorphism lid (top_sublogic lid)) (dom lid mor) mor

-- | Embedding of comorphisms as Grothendieck sig mors
gEmbedComorphism :: AnyComorphism -> G_sign -> Result GMorphism
gEmbedComorphism (Comorphism cid) (G_sign lid sig) = do
  sig' <- coerceSign lid (sourceLogic cid) "gEmbedComorphism" sig
  (sigTar,_) <- map_sign cid sig'
  let lidTar = targetLogic cid
  return (GMorphism cid sig'(ide lidTar sigTar))

-- | heterogeneous union of two Grothendieck signatures
gsigUnion :: LogicGraph -> G_sign -> G_sign -> Result G_sign
gsigUnion lg gsig1@(G_sign lid1 sigma1) gsig2@(G_sign lid2 sigma2) =
  if language_name lid1 == language_name lid2
     then homogeneousGsigUnion gsig1 gsig2
     else do
      (Comorphism cid1,Comorphism cid2) <- logicUnion lg (Logic lid1) (Logic lid2)
      let lidS1 = sourceLogic cid1
          lidS2 = sourceLogic cid2
          lidT1 = targetLogic cid1
          lidT2 = targetLogic cid2
      sigma1' <- coerceSign lid1 lidS1 "Union of signaturesa" sigma1
      sigma2' <- coerceSign lid2 lidS2 "Union of signaturesb" sigma2
      (sigma1'',_) <- map_sign cid1 sigma1'  -- where to put axioms???
      (sigma2'',_) <- map_sign cid2 sigma2'  -- where to put axioms???
      sigma2''' <- coerceSign lidT2 lidT1 "Union of signaturesc" sigma2''
      sigma3 <- signature_union lidT1 sigma1'' sigma2'''
      return (G_sign lidT1 sigma3)


-- | homogeneous Union of two Grothendieck signatures
homogeneousGsigUnion :: G_sign -> G_sign -> Result G_sign
homogeneousGsigUnion (G_sign lid1 sigma1) (G_sign lid2 sigma2) = do
  sigma2' <- coerceSign lid2 lid1 "Union of signaturesd" sigma2
  sigma3 <- signature_union lid1 sigma1 sigma2'
  return (G_sign lid1 sigma3)

-- | union of a list of Grothendieck signatures
gsigManyUnion :: LogicGraph -> [G_sign] -> Result G_sign
gsigManyUnion _ [] =
  fail "union of emtpy list of signatures"
gsigManyUnion lg (gsigma : gsigmas) =
  foldM (gsigUnion lg) gsigma gsigmas

-- | homogeneous Union of a list of morphisms
homogeneousMorManyUnion :: [G_morphism] -> Result G_morphism
homogeneousMorManyUnion [] =
  fail "homogeneous union of emtpy list of morphisms"
homogeneousMorManyUnion (gmor : gmors) =
  foldM ( \ (G_morphism lid2 mor2) (G_morphism lid1 mor1) -> do
            mor1' <- coerceMorphism lid1 lid2  "homogeneousMorManyUnion" mor1
            mor <- morphism_union lid2 mor1' mor2
            return (G_morphism lid2 mor)) gmor gmors

-- | inclusion between two logics
logicInclusion :: LogicGraph -> AnyLogic -> AnyLogic -> Result AnyComorphism
logicInclusion logicGraph l1@(Logic lid1) (Logic lid2) =
     let ln1 = language_name lid1
         ln2 = language_name lid2 in
     if ln1==ln2 then
       return (idComorphism l1)
      else case Map.lookup (ln1,ln2) (inclusions logicGraph) of
           Just (Comorphism i) ->
               return (Comorphism i)
           Nothing ->
               fail ("No inclusion from "++ln1++" to "++ln2++" found")

-- | inclusion morphism between two Grothendieck signatures
ginclusion :: LogicGraph -> G_sign -> G_sign -> Result GMorphism
ginclusion logicGraph (G_sign lid1 sigma1) (G_sign lid2 sigma2) = do
    Comorphism i <- logicInclusion logicGraph (Logic lid1) (Logic lid2)
    sigma1' <- coerceSign lid1 (sourceLogic i) "Inclusion of signatures" sigma1
    (sigma1'',_) <- map_sign i sigma1'
    sigma2' <- coerceSign lid2 (targetLogic i) "Inclusion of signatures" sigma2
    mor <- inclusion (targetLogic i) sigma1'' sigma2'
    return (GMorphism i sigma1' mor)

-- | Composition of two Grothendieck signature morphisms
-- | with itermediate inclusion
compInclusion :: LogicGraph -> GMorphism -> GMorphism -> Result GMorphism
compInclusion lg mor1 mor2 = do
  let sigma1 = cod Grothendieck mor1
      sigma2 = dom Grothendieck mor2
  unless (isSubGsign lg sigma1 sigma2)
         (fail "Logic.Grothendieck.compInclusion: not a subsignature")
  incl <- ginclusion lg sigma1 sigma2
  mor <- comp Grothendieck mor1 incl
  comp Grothendieck mor mor2

-- | Composition of two Grothendieck signature morphisms
-- | with intermediate homogeneous inclusion
compHomInclusion :: GMorphism -> GMorphism -> Result GMorphism
compHomInclusion mor1 mor2 = compInclusion emptyLogicGraph mor1 mor2

-- | Find all (composites of) comorphisms starting from a given logic
findComorphismPaths :: LogicGraph ->  G_sublogics -> [AnyComorphism]
findComorphismPaths lg (G_sublogics lid sub) =
  List.nub $ map fst $ iterateComp (0::Int) [(idc,[idc])]
  where
  idc = Comorphism (IdComorphism lid sub)
  coMors = Map.elems $ comorphisms lg
  -- compute possible compositions, but only up to depth 3
  iterateComp n l = -- (l::[(AnyComorphism,[AnyComorphism])]) =
    if n>3 || l==newL then newL else iterateComp (n+1) newL
    where
    newL = List.nub (l ++ (concat (map extend l)))
    -- extend comorphism list in all directions, but no cylces
    extend (coMor,comps) =
       let addCoMor c =
            case compComorphism coMor c of
              Nothing -> Nothing
              Just c1 -> Just (c1,c:comps)
        in catMaybes $ map addCoMor $ filter (not . (`elem` comps)) $ coMors

-- | finds first comorphism with a matching sublogic
findComorphism ::Monad m => G_sublogics -> [AnyComorphism] -> m AnyComorphism
findComorphism _ [] = fail "No matching comorphism found"
findComorphism gsl@(G_sublogics lid sub) ((Comorphism cid):rest) =
    let l2 = sourceLogic cid
        rec = findComorphism gsl rest in
   if language_name lid == language_name l2
      then if isSubElem (coerceSublogic lid l2 sub) $ sourceSublogic cid
              then return $ Comorphism cid
              else rec
      else rec

-- | check transpotability of Grothendieck signature morphisms
-- | (currently returns false for heterogeneous morphisms)
isTransportable :: GMorphism -> Bool
isTransportable (GMorphism cid _ mor) =
  isIdComorphism (Comorphism cid) && is_transportable (targetLogic cid) mor


------------------------------------------------------------------
-- Provers
------------------------------------------------------------------

-- | provers and consistency checkers for specific logics
data G_prover = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
       G_prover lid (Prover sign sentence proof_tree)

coerceProver ::
  (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic  lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
   Monad m) => lid1 -> lid2 -> String -> Prover sign1 sentence1 proof_tree1
      -> m (Prover sign2 sentence2 proof_tree2)
coerceProver l1 l2 msg m1 = primCoerce l1 l2 msg m1

data G_cons_checker = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
       G_cons_checker lid (ConsChecker sign sentence morphism proof_tree)

coerceConsChecker ::
  (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic  lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
   Monad m) => lid1 -> lid2 -> String
      -> ConsChecker sign1 sentence1 morphism1 proof_tree1
      -> m (ConsChecker sign2 sentence2 morphism2 proof_tree2)
coerceConsChecker l1 l2 msg m1 = primCoerce l1 l2 msg m1
