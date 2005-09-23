{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Central data structure for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}

{-
   References:

   T. Mossakowski, S. Autexier and D. Hutter:
   Extending Development Graphs With Hiding.
   H. Hussmann (ed.): Fundamental Approaches to Software Engineering 2001,
   Lecture Notes in Computer Science 2029, p. 269-283,
   Springer-Verlag 2001.

   T. Mossakowski, S. Autexier, D. Hutter, P. Hoffman:
   CASL Proof calculus. In: CASL reference manual, part IV.
   Available from http://www.cofi.info

todo:

Integrate stuff from Saarbrücken
Should AS be stored in GloblaContext as well?
-}

module Static.DevGraph where

import Logic.Logic
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Prover
import Logic.Coerce

import Syntax.AS_Library

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Tree as Tree

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import Common.Result
import Common.DynamicUtils 

import Data.Dynamic
import Data.List as List
import Control.Monad

getNewNode :: Tree.Gr a b -> Node
getNewNode g = case newNodes 1 g of 
               [n] -> n
               _ -> error "Static.DevGraph.getNewNode" 

-- * Types for structured specification analysis

-- ??? Some info about the theorems already proved for a node
--     should be added
--      or should it be kept separately?
-- what about open theorems of a node???

-- | name of a node in a DG; auxiliary nodes may have extension string
-- | and non-zero number (for these, names are usually hidden)
type NODE_NAME = (SIMPLE_ID, String, Int)

-- | node inscriptions in development graphs           
data DGNodeLab = 
  DGNode {
    dgn_name :: NODE_NAME,  -- name in the input language
    dgn_theory :: G_theory, -- local theory
    dgn_nf :: Maybe Node,   -- normal form, for Theorem-Hide-Shift
    dgn_sigma :: Maybe GMorphism, -- inclusion of signature into nf signature 
    dgn_origin :: DGOrigin,  -- origin in input language
    dgn_cons :: Conservativity,
    dgn_cons_status :: ThmLinkStatus
  }
 | DGRef {  -- reference to node in a different DG
    dgn_renamed :: NODE_NAME,    -- new name of node (in current DG)
    dgn_libname :: LIB_NAME,     -- pointer to DG where ref'd node resides
    dgn_node :: Node,            -- pointer to ref'd node
    dgn_nf :: Maybe Node,        -- normal form, for Theorem-Hide-Shift
    dgn_sigma :: Maybe GMorphism -- inclusion of signature into nf signature 
  } deriving (Show, Eq)

dgn_sign :: DGNodeLab -> G_sign
dgn_sign dn = case dgn_theory dn of
    G_theory lid sig _ -> G_sign lid sig

isInternalNode :: DGNodeLab -> Bool
isInternalNode (DGNode n _ _ _ _ _ _) = isInternal n
isInternalNode _ = False

isRefNode :: DGNodeLab -> Bool
isRefNode (DGNode _ _ _ _ _ _ _) = False
isRefNode _ = True

-- gets the name of a development graph node as a string
getDGNodeName :: DGNodeLab -> String
getDGNodeName (DGNode n _ _ _ _ _ _) = showName n
getDGNodeName (DGRef n _ _ _ _) = showName n

emptyNodeName :: NODE_NAME
emptyNodeName = (mkSimpleId "","",0)

showInt :: Int -> String
showInt i = if i==0 then "" else show i

showName :: NODE_NAME -> String
showName (n,s,i) = show n ++ if ext=="" then "" else "_"++ext
                   where ext = s ++ showInt i

makeName :: SIMPLE_ID -> NODE_NAME
makeName n = (n,"",0)

getName :: NODE_NAME -> SIMPLE_ID
getName (n,_,_) = n

makeMaybeName :: Maybe SIMPLE_ID -> NODE_NAME
makeMaybeName Nothing = emptyNodeName
makeMaybeName (Just n) = makeName n

inc :: NODE_NAME -> NODE_NAME
inc (n,s,i) = (n,s,i+1)

isInternal :: NODE_NAME ->  Bool
isInternal (_,s,i) = (i/=0) || s/=""

extName :: String -> NODE_NAME -> NODE_NAME
extName s (n,s1,i) = (n,s1++showInt i++s,0)

isDGRef :: DGNodeLab -> Bool
isDGRef (DGNode _ _ _ _ _ _ _) = False
isDGRef (DGRef _ _ _ _ _) = True

locallyEmpty ::  DGNodeLab -> Bool
locallyEmpty (DGNode _ (G_theory lid sigma sens) _ _ _ _ _) = 
  Set.null $ Set.filter 
      (\s -> not (isAxiomSenStatus s) && not (isProvenSenStatus s) ) sens 
locallyEmpty (DGRef _ _ _ _ _) = True

-- | link inscriptions in development graphs           
data DGLinkLab = DGLink {
              dgl_morphism :: GMorphism,  -- signature morphism of link
              dgl_type :: DGLinkType,     -- type: local, global, def, thm?
              dgl_origin :: DGOrigin }    -- origin in input language
              deriving (Show, Eq)

instance PrettyPrint DGLinkLab where
  printText0 ga l = printText0 ga (dgl_morphism l)
                    <+> printText0 ga (dgl_type l)
                    <+> printText0 ga (dgl_origin l)

{-
   proof status = (DG0,[(R1,DG1),...,(Rn,DGn)])
   DG0 is the development graph resulting from the static analysis
   Ri is a list of rules that transforms DGi-1 to DGi
   With the list of intermediate proof states, one can easily implement
    an undo operation
-}

{-type ProofStatus = (GlobalContext,LibEnv,[([DGRule],[DGChange])],DGraph)
umstellen auf:-}

type ProofHistory = [([DGRule],[DGChange])]
type ProofStatus = (LIB_NAME,LibEnv,Map.Map LIB_NAME ProofHistory) 

data DGChange = InsertNode (LNode DGNodeLab)
              | DeleteNode (LNode DGNodeLab)
              | InsertEdge (LEdge DGLinkLab)
              | DeleteEdge (LEdge DGLinkLab)
                deriving Eq

instance Show DGChange where
  show (InsertNode (n,_)) = "InsertNode "++show n
  show (DeleteNode (n,_)) = "DeleteNode "++show n
  show (InsertEdge (n,m,_)) = "InsertEdge "++show n++"->"++show m
  show (DeleteEdge (n,m,_)) = "DeleteEdge "++show n++"->"++show m

-- | Link types of development graphs
-- | Sect. IV:4.2 of the CASL Reference Manual explains them in depth
data DGLinkType = LocalDef 
            | GlobalDef
            | HidingDef
            | FreeDef MaybeNode -- the "parameter" node
            | CofreeDef MaybeNode -- the "parameter" node
	    | LocalThm ThmLinkStatus Conservativity ThmLinkStatus
               -- ??? Some more proof information is needed here
               -- (proof tree, ...)
	    | GlobalThm ThmLinkStatus Conservativity ThmLinkStatus
	    | HidingThm GMorphism ThmLinkStatus
            | FreeThm GMorphism Bool
              -- DGLink S1 S2 m2 (DGLinkType m1 p) n
              -- corresponds to a span of morphisms
              -- S1 <--m1-- S --m2--> S2
              deriving (Show, Eq)

instance PrettyPrint DGLinkType where
    printText0 _ t = text $ case t of
        LocalDef -> "LocalDef"
        GlobalDef -> "GlobalDef"
        HidingDef -> "HidingDef"
        FreeDef _ -> "FreeDef"
        CofreeDef _ -> "CofreeDef"
	LocalThm _ _ _ -> "LocalThm"
	GlobalThm _ _ _ -> "GlobalThm"
	HidingThm _ _ -> "HidingThm"
        FreeThm _ _ -> "FreeThm"

-- | Conservativity annotations. For compactness, only the greatest
-- | applicable value is used in a DG
data Conservativity = None | Cons | Mono | Def
              deriving (Eq,Ord)
instance Show Conservativity where
  show None = ""
  show Cons = "Cons"
  show Mono = "Mono"
  show Def = "Def"

-- | Rules in the development graph calculus
-- | Sect. IV:4.4 of the CASL Reference Manual explains them in depth
data DGRule = 
   TheoremHideShift
 | HideTheoremShift (LEdge DGLinkLab)
 | Borrowing
 | ConsShift
 | DefShift 
 | MonoShift
 | DefToMono
 | MonoToCons
 | FreeIsMono
 | MonoIsFree
 | GlobDecomp (LEdge DGLinkLab)  -- edge in the conclusion
 | LocDecomp (LEdge DGLinkLab)
 | LocInference (LEdge DGLinkLab)
 | GlobSubsumption (LEdge DGLinkLab)
 | Composition [LEdge DGLinkLab]
 | LocalInference
 | BasicInference AnyComorphism BasicProof -- coding and proof tree
 | BasicConsInference Edge BasicConsProof
   deriving (Show, Eq)

instance PrettyPrint DGRule where
  printText0 ga r = case r of 
   TheoremHideShift -> text "Theorem-Hide-Shift"
   HideTheoremShift l -> text "Hide-Theorem-Shift; resulting link:" <+> printLEdgeInProof ga l
   Borrowing -> text "Borrowing"
   ConsShift -> text "Cons-Shift"
   DefShift  -> text "Def-Shift"
   MonoShift -> text "Mono-Shift"
   DefToMono -> text "DefToMono"
   MonoToCons -> text "MonoToCons"
   FreeIsMono -> text "FreeIsMono"
   MonoIsFree -> text "MonoIsFree"
   GlobDecomp l -> text "Global Decomposition; resulting link:"  <+> printLEdgeInProof ga l 
   LocDecomp l -> text "Local Decomposition; resulting link:" <+> printLEdgeInProof ga l
   LocInference l -> text "Local Inference; resulting link:" <+> printLEdgeInProof ga l
   GlobSubsumption l -> text "Global Subsumption; resulting link:" <+> printLEdgeInProof ga l
   Composition ls -> 
       text "Composition" <+> vcat (map (printLEdgeInProof ga) ls)
   LocalInference -> text "Local Inference"
   BasicInference c bp -> text "Basic Inference using:" <+> text ("Comorphism: "++show c ++ "Proof tree: "++show bp)
   BasicConsInference _ bp -> text "Basic Cons-Inference using:" <+> text (show bp)

printLEdgeInProof :: GlobalAnnos -> LEdge DGLinkLab -> Doc
printLEdgeInProof ga (s,t,l) = 
  printText0 ga s <> text "-->" <> printText0 ga t <> text ":"
  <+> printLabInProof ga l

printLabInProof :: GlobalAnnos -> DGLinkLab -> Doc
printLabInProof ga l =
  hang(
    printText0 ga (dgl_type l)
    <+> text "with origin: " 
    <> printText0 ga (dgl_origin l)
    <> text ", and morphism: " )
   2 (printText0 ga (dgl_morphism l))


data BasicProof =
  forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        BasicProof lid (Proof_status proof_tree)
     |  Guessed
     |  Conjectured
     |  Handwritten

instance Eq BasicProof where
  Guessed == Guessed = True
  Conjectured == Conjectured = True
  Handwritten == Handwritten = True
  BasicProof lid1 p1 == BasicProof lid2 p2 =
    coerceBasicProof lid1 lid2 "Eq BasicProof" p1 == Just p2
  _ == _ = False

instance Show BasicProof where
  show (BasicProof _ p1) = show p1
  show Guessed = "Guessed"
  show Conjectured = "Conjectured"
  show Handwritten = "Handwritten"

data BasicConsProof = BasicConsProof -- more detail to be added ...
     deriving (Show, Eq)

data ThmLinkStatus = LeftOpen 
		   | Proven DGRule [LEdge DGLinkLab]
                     deriving (Show, Eq)

instance PrettyPrint ThmLinkStatus where
    printText0 ga tls = case tls of 
        LeftOpen -> text "Open"
        Proven r ls -> hang (text "Proven with rule" <+> printText0 ga r
                             $$ text "Proof based on links:")
                       2 (vcat (map (printLEdgeInProof ga) ls))



-- | Data type indicating the origin of nodes and edges in the input language
-- | This is not used in the DG calculus, only may be used in the future
-- | for reconstruction of input and management of change.
data DGOrigin = DGBasic | DGExtension | DGTranslation | DGUnion | DGHiding 
              | DGRevealing | DGRevealTranslation | DGFree | DGCofree 
              | DGLocal | DGClosed | DGClosedLenv | DGLogicQual | DGLogicQualLenv 
              | DGData
              | DGFormalParams | DGImports | DGSpecInst SIMPLE_ID | DGFitSpec 
              | DGView SIMPLE_ID | DGFitView SIMPLE_ID | DGFitViewImp SIMPLE_ID
              | DGFitViewA SIMPLE_ID | DGFitViewAImp SIMPLE_ID | DGProof
              | DGintegratedSCC
              deriving (Show, Eq)

type DGraph = Tree.Gr DGNodeLab DGLinkLab

-- | Node with signature in a DG
data NodeSig = NodeSig Node G_sign deriving (Show, Eq)

-- | NodeSig or possibly the empty sig in a logic
-- | (but since we want to avoid lots of vacuous nodes with empty sig,
-- |  we do not assign a real node in the DG here)
data MaybeNode = JustNode NodeSig | EmptyNode AnyLogic deriving (Show, Eq)

instance PrettyPrint NodeSig where
  printText0 ga (NodeSig n sig) = 
    ptext "node" <+> printText0 ga n <> ptext ":" <> printText0 ga sig

emptyG_sign :: AnyLogic -> G_sign
emptyG_sign (Logic lid) = G_sign lid (empty_signature lid)

getSig :: NodeSig -> G_sign
getSig (NodeSig _ sigma) = sigma

getNode :: NodeSig -> Node
getNode (NodeSig n _) = n

getMaybeSig :: MaybeNode -> G_sign
getMaybeSig (JustNode ns) = getSig ns
getMaybeSig (EmptyNode l) = emptyG_sign l

getLogic :: MaybeNode -> AnyLogic
getLogic (JustNode ns) = getNodeLogic ns
getLogic (EmptyNode l) = l

getNodeLogic :: NodeSig -> AnyLogic
getNodeLogic (NodeSig _ (G_sign lid _)) = Logic lid

-- | Create a node that represents a union of signatures
nodeSigUnion :: LogicGraph -> DGraph -> [MaybeNode] -> DGOrigin
             -> Result (NodeSig, DGraph)
nodeSigUnion lgraph dg nodeSigs orig =
  do sigUnion@(G_sign lid sigU) <- gsigManyUnion lgraph 
                                   $ map getMaybeSig nodeSigs
     let nodeContents = DGNode {dgn_name = emptyNodeName,
				dgn_theory = G_theory lid sigU noSens,
				dgn_nf = Nothing,
				dgn_sigma = Nothing,
				dgn_origin = orig,
				dgn_cons = None,
				dgn_cons_status = LeftOpen}
	 node = getNewNode dg
	 dg' = insNode (node, nodeContents) dg
	 inslink dgres nsig = do 
             dgv <- dgres
	     case nsig of
	         EmptyNode _ -> dgres
		 JustNode (NodeSig n sig) -> do 
                     incl <- ginclusion lgraph sig sigUnion
		     return $ insEdge (n, node, DGLink 
                         {dgl_morphism = incl,
			  dgl_type = GlobalDef,
			  dgl_origin = orig }) dgv
     dg'' <- foldl inslink (return dg') nodeSigs
     return (NodeSig node sigUnion, dg'')

-- | Extend the development graph with given morphism originating
-- from given NodeSig
extendDGraph :: DGraph    -- ^ the development graph to be extended
	     -> NodeSig   -- ^ the NodeSig from which the morphism originates
	     -> GMorphism -- ^ the morphism to be inserted
	     -> DGOrigin  
	     -> Result (NodeSig, DGraph)
-- ^ returns the target signature of the morphism and the resulting DGraph
extendDGraph dg (NodeSig n _) morph orig = case cod Grothendieck morph of
    targetSig@(G_sign lid tar) -> let 
        nodeContents = DGNode {dgn_name = emptyNodeName,
			       dgn_theory = G_theory lid tar noSens,
			       dgn_nf = Nothing,
			       dgn_sigma = Nothing,
			       dgn_origin = orig,
			       dgn_cons = None,
			       dgn_cons_status = LeftOpen}
	linkContents = DGLink {dgl_morphism = morph,
			       dgl_type = GlobalDef, -- TODO: other type
			       dgl_origin = orig}
	node = getNewNode dg
	dg' = insNode (node, nodeContents) dg
	dg'' = insEdge (n, node, linkContents) dg'
        in return (NodeSig node targetSig, dg'')


-- | Extend the development graph with given morphism pointing to 
-- given NodeSig
extendDGraphRev :: DGraph    -- ^ the development graph to be extended
	     -> NodeSig   -- ^ the NodeSig to which the morphism points
	     -> GMorphism -- ^ the morphism to be inserted
	     -> DGOrigin  
	     -> Result (NodeSig, DGraph)
-- ^ returns 1. the source signature of the morphism and 2. the resulting DGraph
extendDGraphRev dg (NodeSig n _) morph orig = case dom Grothendieck morph of
    sourceSig@(G_sign lid src) -> let
        nodeContents = DGNode {dgn_name = emptyNodeName,
			       dgn_theory = G_theory lid src Set.empty,
			       dgn_nf = Nothing,
			       dgn_sigma = Nothing,
			       dgn_origin = orig,
			       dgn_cons = None,
			       dgn_cons_status = LeftOpen}
	linkContents = DGLink {dgl_morphism = morph,
			       dgl_type = GlobalDef, -- TODO: other type
			       dgl_origin = orig}
	node = getNewNode dg
	dg' = insNode (node, nodeContents) dg
	dg'' = insEdge (node, n, linkContents) dg'
        in return (NodeSig node sourceSig, dg'')

-- import, formal parameters andd united signature of formal params
type GenericitySig = (MaybeNode, [NodeSig], MaybeNode)

-- import, formal parameters, united signature of formal params, body
type ExtGenSig = (MaybeNode, [NodeSig], G_sign, NodeSig)

-- source, morphism, parameterized target
type ExtViewSig = (NodeSig,GMorphism,ExtGenSig)


-- * Types for architectural and unit specification analysis
-- (as defined for basic static semantics in Chap. III:5.1)

data UnitSig = Unit_sig NodeSig
             | Par_unit_sig [NodeSig] NodeSig 
               deriving Show

data ImpUnitSigOrSig = Imp_unit_sig MaybeNode UnitSig
                     | Sig NodeSig
                       deriving Show

type StUnitCtx = Map.Map SIMPLE_ID ImpUnitSigOrSig
emptyStUnitCtx :: StUnitCtx
emptyStUnitCtx = Map.empty

data ArchSig = ArchSig StUnitCtx UnitSig deriving Show

-- * Types for global and library environments

data GlobalEntry = SpecEntry ExtGenSig 
                 | ViewEntry ExtViewSig
                 | ArchEntry ArchSig
                 | UnitEntry UnitSig 
                 | RefEntry
                   deriving Show

type GlobalEnv = Map.Map SIMPLE_ID GlobalEntry

type GlobalContext = (GlobalAnnos,GlobalEnv,DGraph)

type LibEnv = Map.Map LIB_NAME GlobalContext


emptyLibEnv :: LibEnv
emptyLibEnv = Map.empty

instance PrettyPrint DGOrigin where
  printText0 _ origin = text $ case origin of
     DGBasic -> "basic specification"
     DGExtension -> "extension"
     DGTranslation -> "translation"
     DGUnion -> "union"
     DGHiding -> "hiding"
     DGRevealing -> "revealing"
     DGRevealTranslation -> "translation part of a revealing"
     DGFree -> "free specification"
     DGCofree -> "cofree specification"
     DGLocal -> "local specification"
     DGClosed -> "closed specification"
     DGClosedLenv -> "closed specification (inclusion of local environment)"
     DGFormalParams -> "formal parameters of a generic specification"
     DGImports -> "imports of a generic specification"
     DGSpecInst n -> ("instantiation of "++showPretty n "")
     DGFitSpec -> "fittig specification"
     DGView n -> ("view "++showPretty n "")
     DGFitView n -> ("fitting view "++showPretty n "")
     DGFitViewImp n -> ("fitting view (imports) "++showPretty n "")
     DGFitViewA n -> ("fitting view (actual parameters) "++showPretty n "")
     DGFitViewAImp n -> ("fitting view (imports and actual parameters) "
                         ++showPretty n "")
     DGProof -> "constructed within a proof"
     _ -> show origin

-- * sentence packing

data SenStatus a = SenStatus
     { value :: Named a
     , order :: Int
     , thmStatus :: [(AnyComorphism,BasicProof)]
     } deriving Show

isProvenSenStatus :: SenStatus a -> Bool
isProvenSenStatus = any isProvenSenStatusAux . thmStatus
  where isProvenSenStatusAux (_,BasicProof _ (Proved _ _ _ _ _)) = True 
        isProvenSenStatusAux _ = False

isAxiomSenStatus :: SenStatus a -> Bool
isAxiomSenStatus = isAxiom . value

instance PrettyPrint a => PrettyPrint (SenStatus a) where
  printText0 ga x =
     printText0 ga (value x)

emptySenStatus :: SenStatus a
emptySenStatus = SenStatus { value = error "emptySenStatus"
                           , order = 0
                           , thmStatus = [] }

instance Eq a => Eq (SenStatus a) where
    d1 == d2 = value d1 == value d2

instance Ord a => Ord (SenStatus a) where
    d1 <= d2 = value d1 <= value d2

decoTc :: TyCon
decoTc = mkTyCon "Static.DevGraph.SenStatus"

instance Typeable s => Typeable (SenStatus s) where 
  typeOf s = mkTyConApp decoTc [typeOf ((undefined :: SenStatus a -> a) s)]

type ThSens a = Set.Set (SenStatus a)

noSens :: ThSens a
noSens = Set.empty

joinSens :: Ord a => ThSens a -> ThSens a -> ThSens a
joinSens s1 s2 = let l1 = Set.toList s1
                     m = foldr (max . order) 0 l1
                     l2 = map ( \ e -> e {order = m + order e }) 
                          $ Set.toList s2 
                 in Set.fromDistinctAscList $ mergeSens l1 l2
    where mergeSens [] l2 = l2
          mergeSens l1 [] = l1
          mergeSens l1@(e1 : r1) l2@(e2 : r2) = case compare e1 e2 of
              LT -> e1 : mergeSens r1 l2
              EQ -> e1 { thmStatus = List.union (thmStatus e1) $ thmStatus e2 }
                    : mergeSens r1 r2
              GT -> e2 : mergeSens l1 r2

mapValue :: (a -> b) -> SenStatus a -> SenStatus b
mapValue f d = d { value = mapNamed f $ value d } 

markAsGoal :: Ord a => ThSens a -> ThSens a
markAsGoal = Set.map (\d -> d { value = (value d) {isAxiom = False}})

toNamedList :: ThSens a -> [Named a]
toNamedList s = let compO d1 d2 = compare (order d1) (order d2)
                in map value $ sortBy compO $ Set.toList s  

toThSens :: Ord a => [Named a] -> ThSens a
toThSens sens = Set.fromList $ zipWith 
    ( \ v i -> emptySenStatus { value = v, order = i })
    sens [1..]

-- * Grothendieck theories

-- | Grothendieck theories
data G_theory = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_theory lid sign (ThSens sentence)

coerceThSens :: 
   (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
   Logic  lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
   Monad m) => lid1 -> lid2 -> String 
            -> ThSens sentence1 -> m (ThSens sentence2)
coerceThSens l1 l2 msg t1 = primCoerce l1 l2 msg t1

instance Eq G_theory where
  G_theory l1 sig1 sens1 == G_theory l2 sig2 sens2 = 
     coerceSign l1 l2 "" sig1 == Just sig2
     && coerceThSens l1 l2 "" sens1 == Just sens2

instance Show G_theory where
  show (G_theory _ sign sens) =
     show sign ++ "\n" ++ show sens

instance PrettyPrint G_theory where
  printText0 ga g = case simplifyTh g of 
     G_theory lid sign sens -> 
         printText0 ga sign $++$ vsep (map (print_named lid ga) 
                                           $ toNamedList sens)

-- | compute sublogic of a theory
sublogicOfTh :: G_theory -> G_sublogics
sublogicOfTh (G_theory lid sigma sens) =
  let sub = Set.fold Logic.Logic.join 
                  (min_sublogic_sign lid sigma)
                  (Set.map (min_sublogic_sentence lid . sentence . value) 
                       sens)
   in G_sublogics lid sub

-- | simplify a theory (throw away qualifications)
simplifyTh :: G_theory -> G_theory
simplifyTh (G_theory lid sigma sens) = G_theory lid sigma $ 
    Set.map (mapValue $ simplify_sen lid sigma) sens

-- | Translation of a G_theory along a GMorphism
translateG_theory :: GMorphism -> G_theory -> Result G_theory
translateG_theory (GMorphism cid _ morphism2)
                           (G_theory lid sign sens) = do
  let tlid = targetLogic cid
  --(sigma2,_) <- map_sign cid sign1
  bTh <- coerceBasicTheory lid (sourceLogic cid) 
                    "translateG_theory" (sign, toNamedList sens)
  (_, sens'') <- map_theory cid bTh
  sens''' <- mapM (mapNamedM $ map_sen tlid morphism2) sens''
  return $ G_theory tlid (cod tlid morphism2) $ toThSens sens'''

-- | Join the sentences of two G_theories
joinG_sentences :: Monad m => G_theory -> G_theory -> m G_theory
joinG_sentences (G_theory lid1 sig1 sens1) (G_theory lid2 _ sens2) = do
  sens2' <- coerceThSens lid2 lid1 "joinG_sentences" sens2
    -- assert (sig1 == sig2') ? 
  return $ G_theory lid1 sig1 $ joinSens sens1 sens2'

-- | flattening the sentences form a list of G_theories
flatG_sentences :: Monad m => G_theory -> [G_theory] -> m G_theory
flatG_sentences th ths = foldM joinG_sentences th ths

-- | Get signature of a theory
signOf :: G_theory -> G_sign
signOf (G_theory lid sign _) = G_sign lid sign

------------------------------------------------------------------
-- Grothendieck diagrams and weakly amalgamable cocones
------------------------------------------------------------------

type GDiagram = Tree.Gr G_theory GMorphism

gWeaklyAmalgamableCocone :: GDiagram 
                         -> Result (G_theory,Map.Map Graph.Node GMorphism)
gWeaklyAmalgamableCocone _ = 
    return (undefined,Map.empty) -- dummy implementation

