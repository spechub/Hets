{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (overlapping instances, dynamics, existentials)

   
   The Grothendieck logic is defined to be the
   heterogeneous logic over the logic graph.
   This will be the logic over which the data 
   structures and algorithms for specification in-the-large
   are built.

   References:

   R. Diaconescu:
   Grothendieck institutions
   J. applied categorical structures 10, 2002, p. 383-402.

   T. Mossakowski: 
   Heterogeneous development graphs and heterogeneous borrowing
   Fossacs 2002, LNCS 2303, p. 326-341

   T. Mossakowski: Foundations of heterogeneous specification
   Submitted

   T. Mossakowski:
   Relating CASL with Other Specification Languages:
        the Institution Level
   Theoretical Computer Science 286, 2002, p. 367-475

   Todo:

-}

module Logic.Grothendieck where

import Logic.Logic
import Logic.Comorphism
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map
import Common.PPUtils 
import Common.Result
import Common.Id
import Common.Named
import Common.ListUtils
import Data.Dynamic
import Control.Monad

import Common.Lib.Parsec.Pos -- for testing purposes

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

    printLatex0 ga (G_basic_spec _ s) = printLatex0 ga s

-- | Grothendieck sentences
data G_sentence = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_sentence lid sentence 

instance Show G_sentence where
    show (G_sentence _ s) = show s

-- | Grothendieck sentence lists
data G_l_sentence_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
  G_l_sentence lid [Named sentence] 

instance Show G_l_sentence_list where
    show (G_l_sentence _ s) = show s

instance Eq G_l_sentence_list where
    (G_l_sentence i1 nl1) == (G_l_sentence i2 nl2) =
     coerce i1 i2 nl1 == Just nl2

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
  typeOf _ = mkAppTy tyconG_sign []

instance Eq G_sign where
  (G_sign i1 sigma1) == (G_sign i2 sigma2) =
     coerce i1 i2 sigma1 == Just sigma2

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

instance Eq G_symbol where
  (G_symbol i1 s1) == (G_symbol i2 s2) =
     coerce i1 i2 s1 == Just s2

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

    printLatex0 ga (G_symb_items_list _ l) = 
        commaT_latex ga l

instance Eq G_symb_items_list where
  (G_symb_items_list i1 s1) == (G_symb_items_list i2 s2) =
     coerce i1 i2 s1 == Just s2

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

    printLatex0 ga (G_symb_map_items_list _ l) = 
        commaT_latex ga l

instance Eq G_symb_map_items_list where
  (G_symb_map_items_list i1 s1) == (G_symb_map_items_list i2 s2) =
     coerce i1 i2 s1 == Just s2

-- | Grothendieck diagrams
data G_diagram = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
        G_diagram lid (Diagram sign morphism) 

-- | Grothendieck sublogics
data G_sublogics = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_sublogics lid sublogics 

instance Show G_sublogics where
    show (G_sublogics _ l) = show l

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

-- | Compose comorphisms
compComorphism :: AnyComorphism -> AnyComorphism -> Result AnyComorphism
compComorphism (Comorphism cid1) (Comorphism cid2) = do
    let lid1 = sourceLogic cid1
        lid2 = targetLogic cid1
        lid3 = sourceLogic cid2
    ComorphismAux cid1' _ _ _ _ <- 
      maybeToResult 
        nullPos 
        ("Cannot compose comorphisms "++language_name cid1++
         " with "++language_name cid2)
        (coerce lid2 lid3 $ ComorphismAux cid1 lid1 lid2 undefined undefined)
    return (Comorphism (CompComorphism cid1' cid2))

-- | Logic graph
data LogicGraph = LogicGraph {
                    logics :: Map.Map String AnyLogic, 
                    comorphisms :: Map.Map String AnyComorphism,
                    inclusions :: Map.Map (String,String) AnyComorphism
                  }

-- | find a logic in a logic graph
lookupLogic :: String -> String -> LogicGraph -> AnyLogic
lookupLogic error_prefix logname logicGraph =
    case Map.lookup logname (logics logicGraph) of
    Nothing -> error (error_prefix++" in LogicGraph logic \""
                      ++logname++"\" unknown")
    Just lid -> lid

-- | find a comorphism in a logic graph
lookupComorphism :: String -> LogicGraph -> Result AnyComorphism
lookupComorphism coname logicGraph = do
  let nameList = splitBy ';' coname
  cs <- sequence $ map lookupN nameList
  case cs of
    c:cs1 -> foldM compComorphism c cs1
    _ -> fail ("Illgegal comorphism name: "++coname)
  where 
  lookupN name = 
    case name of
      'i':'d':'_':logic -> do
         l <- maybeToResult 
                nullPos ("Cannot find logic "++logic)
                 $ Map.lookup logic (logics logicGraph)
         case l of
           Logic lid -> return $ Comorphism $ IdComorphism lid
      _ -> maybeToResult 
            nullPos ("Cannot find logic comorphism "++name) 
             $ Map.lookup name (comorphisms logicGraph)

-- | auxiliary existential type needed for composition of comorphisms
data AnyComorphismAux lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 = 
        forall cid .
      Comorphism cid 
                 lid1 sublogics1 basic_spec1 sentence1 
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2 
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      ComorphismAux cid lid1 lid2 sign1 morphism2

tyconAnyComorphismAux :: TyCon
tyconAnyComorphismAux = mkTyCon "Logic.Grothendieck.AnyComorphismAux"

instance Typeable (AnyComorphismAux lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
  where typeOf _ = mkAppTy tyconG_sign []

instance Show (AnyComorphismAux lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
  where show _ = "<AnyComorphismAux>"


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
  (GMorphism cid1 sigma1 mor1) == 
   (GMorphism cid2 sigma2 mor2)
     = maybe False id
       (do s <- coerce cid1 cid2 "x"
           return (s==Just "x")
           sigma2' <- coerce (sourceLogic cid1) (sourceLogic cid2) sigma2
           mor2' <- coerce (targetLogic cid1) (targetLogic cid2) mor2
           return (sigma1 == sigma2' && mor1==mor2'))


data Grothendieck = Grothendieck deriving Show

instance Language Grothendieck


instance Show GMorphism where
    show (GMorphism cid s m) = show cid ++ "(" ++ show s ++ ")" ++ show m
 
instance PrettyPrint GMorphism where
    printText0 ga (GMorphism cid s m) = 
      ptext (show cid) <+> ptext ":" <+> ptext (show (sourceLogic cid)) <+>
      ptext "->" <+> ptext (show (targetLogic cid)) <+>
      ptext "(" <+> printText0 ga s <+> ptext ")" 
      $$
      printText0 ga m

instance Category Grothendieck G_sign GMorphism where
  ide _ (G_sign lid sigma) = 
    GMorphism (IdComorphism lid) sigma (ide lid sigma)
  comp _ 
       (GMorphism r1 sigma1 mor1) 
       (GMorphism r2 _sigma2 mor2) = 
    do let lid1 = sourceLogic r1
           lid2 = targetLogic r1
           lid3 = sourceLogic r2
           lid4 = targetLogic r2
       ComorphismAux r1' _ _ sigma1' mor1' <- 
         (coerce lid2 lid3 $ ComorphismAux r1 lid1 lid2 sigma1 mor1)
       mor1'' <- map_morphism r2 mor1'
       mor <- comp lid4 mor1'' mor2
       return (GMorphism (CompComorphism r1' r2) sigma1' mor)
  dom _ (GMorphism r sigma _mor) = 
    G_sign (sourceLogic r) sigma
  cod _ (GMorphism r _sigma mor) = 
    G_sign lid2 (cod lid2 mor)
    where lid2 = targetLogic r
  legal_obj _ (G_sign lid sigma) = legal_obj lid sigma 
  legal_mor _ (GMorphism r sigma mor) =
    legal_mor lid2 mor && 
    case map_sign r sigma of
      Just (sigma',_) -> sigma' == cod lid2 mor
      Nothing -> False
    where lid2 = targetLogic r

-- | Embedding of homogeneous signature morphisms as Grothendieck sig mors
gEmbed :: G_morphism -> GMorphism
gEmbed (G_morphism lid mor) =
  GMorphism (IdComorphism lid) (dom lid mor) mor

-- | heterogeneous union of two Grothendieck signatures
--   the left signature determines the result logic
gsigLeftUnion :: LogicGraph -> Pos -> G_sign -> G_sign -> Result G_sign
gsigLeftUnion lg pos gsig1@(G_sign lid1 sigma1) gsig2@(G_sign lid2 sigma2) =
  if language_name lid1 == language_name lid2 
     then homogeneousGsigUnion pos gsig1 gsig2
     else do
      GMorphism incl _ _ <- ginclusion lg 
          (G_sign lid2 (empty_signature lid2))
          (G_sign lid1 (empty_signature lid1))
      let lid1' = targetLogic incl
          lid2' = sourceLogic incl
      sigma1' <- rcoerce lid1 lid1' pos sigma1
      sigma2' <- rcoerce lid2 lid2' pos sigma2
      (sigma2'',_) <- maybeToResult pos "gsigLeftUnion: signature mapping failed" 
                       (map_sign incl sigma2')  -- where to put axioms???
      sigma3 <- signature_union lid1' sigma1' sigma2''
      return (G_sign lid1' sigma3)


-- | homogeneous Union of two Grothendieck signatures
homogeneousGsigUnion :: Pos -> G_sign -> G_sign -> Result G_sign
homogeneousGsigUnion pos (G_sign lid1 sigma1) (G_sign lid2 sigma2) = do
  sigma2' <- rcoerce lid2 lid1 pos sigma2
  sigma3 <- signature_union lid1 sigma1 sigma2'
  return (G_sign lid1 sigma3)

-- | homogeneous Union of a list of Grothendieck signatures
homogeneousGsigManyUnion :: Pos -> [G_sign] -> Result G_sign
homogeneousGsigManyUnion pos [] =
  fatal_error "homogeneous union of emtpy list of signatures" pos
homogeneousGsigManyUnion pos (G_sign lid sigma : gsigmas) = do
  sigmas <- let coerce_lid (G_sign lid1 sigma1) = 
                    rcoerce lid lid1 pos sigma1
             in sequence (map coerce_lid gsigmas)
  bigSigma <- let sig_union s1 s2 = do
                       s1' <- s1
                       signature_union lid s1' s2
                in foldl sig_union (return sigma) sigmas
  return (G_sign lid bigSigma)


-- | homogeneous Union of a list of morphisms
homogeneousMorManyUnion :: Pos -> [G_morphism] -> Result G_morphism
homogeneousMorManyUnion pos [] =
  fatal_error "homogeneous union of emtpy list of morphisms" pos
homogeneousMorManyUnion pos (G_morphism lid mor : gmors) = do
  mors <- let coerce_lid (G_morphism lid1 mor1) = 
                    rcoerce lid lid1 pos mor1
             in sequence (map coerce_lid gmors)
  bigMor <- let mor_union s1 s2 = do
                       s1' <- s1
                       adjustPos pos $ morphism_union lid s1' s2
                in foldl mor_union (return mor) mors
  return (G_morphism lid bigMor)

-- | inclusion morphism between two Grothendieck signatures
ginclusion :: LogicGraph -> G_sign -> G_sign -> Result GMorphism
ginclusion logicGraph (G_sign lid1 sigma1) (G_sign lid2 sigma2) =
  do let ln1 = language_name lid1
         ln2 = language_name lid2
     if ln1==ln2 then do
       sigma2' <- rcoerce lid1 lid2 (newPos "s" 0 0) sigma2
       mor <- inclusion lid1 sigma1 sigma2'
       return (GMorphism (IdComorphism lid1) sigma1 mor)
      else do
       Comorphism i <- 
         maybeToResult (newPos "t" 0 0) 
                       ("No inclusion from "++ln1++" to "++ln2++" found")  
                       (Map.lookup (ln1,ln2) (inclusions logicGraph))
       sigma1' <- rcoerce lid1 (sourceLogic i) (newPos "u" 0 0) sigma1
       sigma2' <- rcoerce lid2 (targetLogic i) (newPos "v" 0 0) sigma2
       (sigma1'',_) <- 
         maybeToResult (newPos "w" 0 0) "ginclusion: signature map failed" 
                       (map_sign i sigma1')
       mor <- inclusion (targetLogic i) sigma1'' sigma2'
       return (GMorphism i sigma1' mor)

