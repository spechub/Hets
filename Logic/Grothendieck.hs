-- needs ghc -fglasgow-exts 

{- HetCATS/Grothendieck.hs
   $Id$
   Till Mossakowski
   
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
import Logic.LogicRepr
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.PPUtils (fsep_latex, comma_latex)
import Common.Result
import Common.Id
import Data.Dynamic

------------------------------------------------------------------
--"Grothendieck" versions of the various parts of type class Logic
------------------------------------------------------------------

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

data G_sentence = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_sentence lid sentence 

instance Show G_sentence where
    show (G_sentence _ s) = show s

data G_l_sentence_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_l_sentence lid [(String,sentence)] 

data G_sign = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_sign lid sign 

instance Typeable G_sign where
  typeOf _ = mkAppTy (mkTyCon "G_sign") []

instance Eq G_sign where
  (G_sign i1 sigma1) == (G_sign i2 sigma2) =
     coerce i1 i2 sigma1 == Just sigma2

instance Show G_sign where
    show (G_sign _ s) = show s

data G_sign_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_sign_list lid [sign] 

data G_symbol = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_symbol lid symbol 

instance Show G_symbol where
  show (G_symbol _ s) = show s

instance Eq G_symbol where
  (G_symbol i1 s1) == (G_symbol i2 s2) =
     coerce i1 i2 s1 == Just s2

data G_symb_items_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_symb_items_list lid [symb_items] 

instance Show G_symb_items_list where
  show (G_symb_items_list _ l) = show l

instance PrettyPrint G_symb_items_list where
    printText0 ga (G_symb_items_list _ l) = 
	fsep $ punctuate comma $ map (printText0 ga) l

    printLatex0 ga (G_symb_items_list _ l) = 
	fsep_latex $ punctuate comma_latex $ map (printLatex0 ga) l

instance Eq G_symb_items_list where
  (G_symb_items_list i1 s1) == (G_symb_items_list i2 s2) =
     coerce i1 i2 s1 == Just s2

data G_symb_map_items_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_symb_map_items_list lid [symb_map_items] 

instance Show G_symb_map_items_list where
  show (G_symb_map_items_list _ l) = show l

instance PrettyPrint G_symb_map_items_list where
    printText0 ga (G_symb_map_items_list _ l) = 
	fsep $ punctuate comma $ map (printText0 ga) l

    printLatex0 ga (G_symb_map_items_list _ l) = 
	fsep_latex $ punctuate comma_latex $ map (printLatex0 ga) l

instance Eq G_symb_map_items_list where
  (G_symb_map_items_list i1 s1) == (G_symb_map_items_list i2 s2) =
     coerce i1 i2 s1 == Just s2

data G_diagram = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_diagram lid (Diagram sign morphism) 

data G_sublogics = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_sublogics lid sublogics 

instance Show G_sublogics where
    show (G_sublogics _ l) = show l


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

data AnyLogic = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        Logic lid

data AnyRepresentation = forall lid1 sublogics1
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
  Repr(LogicRepr lid1 sublogics1 basic_spec1 sentence1 
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2 
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2)


type LogicGraph = ([AnyLogic],[AnyRepresentation])

{- This does not work due to needed ordering:
instance Functor Set where
  fmap = mapSet
instance Monad Set where
  return = unitSet
  m >>= k          = unionManySets (setToList (fmap k m))
-}



------------------------------------------------------------------
-- The Grothendieck signature category
------------------------------------------------------------------

-- composition in diagrammatic order
comp_anyrepr :: AnyRepresentation -> AnyRepresentation -> Maybe AnyRepresentation
comp_anyrepr 
  (Repr (r1 :: LogicRepr lid1 sublogics1 basic_spec1 sentence1 
                symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)) 
  (Repr (r2 :: LogicRepr lid3 sublogics3 basic_spec3 sentence3 
	        symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3
            lid4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4)) =
  do r3 <- coerce (target r1) (source r2) r2 :: Maybe(
	  LogicRepr lid2 sublogics2 basic_spec2 sentence2 
                symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4)
     r4 <- comp_repr r1 r3 
     return (Repr r4)
 
data GMorphism = forall lid1 sublogics1
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
  GMorphism lid1 lid2 
   (LogicRepr lid1 sublogics1 basic_spec1 sentence1 
              symb_items1 symb_map_items1
              sign1 morphism1 symbol1 raw_symbol1 proof_tree1
              lid2 sublogics2 basic_spec2 sentence2 
              symb_items2 symb_map_items2
              sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
   sign1 morphism2 
{-
  | forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
    GMHomInclusion lid sign sign
  | GMHetInclusion G_sign G_sign
-}

instance Eq GMorphism where
  (GMorphism lid1 lid2 r1 sigma1 mor1) == (GMorphism lid3 lid4 r2 sigma2 mor2)
     = maybe False id
       (do r2' <- coerce lid1 lid3 r2
           sigma2' <- coerce lid1 lid3 sigma2
           mor2' <- coerce lid2 lid4 mor2
           return (r1 == r2' && sigma1 == sigma2' && mor1==mor2'))


data Grothendieck = Grothendieck deriving Show

instance Language Grothendieck

instance Show GMorphism where
    show (GMorphism _ _ r s m) = show r ++ "(" ++ show s ++ ")" ++ show m
 
instance Category Grothendieck G_sign GMorphism where
  ide _ (G_sign lid sigma) = 
    GMorphism lid lid (id_repr lid) sigma (ide lid sigma)
  comp _ 
      (GMorphism lid1 lid2 r1 sigma1 mor1) 
      (GMorphism lid3 lid4 r2 _sigma2 mor2) =
    do r2' <- coerce lid2 lid3 r2 
       r3 <- comp_repr r1 r2'
       mor1' <- coerce lid2 lid3 mor1
       mor1'' <- map_morphism r2 mor1' 
       mor <- comp lid4 mor2 mor1''
       return (GMorphism lid1 lid4 r3 sigma1 mor)
  dom _ (GMorphism lid1 _lid2 _r sigma _mor) = G_sign lid1 sigma
  cod _ (GMorphism _lid1 lid2 _r _sigma mor) = G_sign lid2 (cod lid2 mor)
  legal_obj _ (G_sign lid sigma) = legal_obj lid sigma 
  legal_mor _ (GMorphism _lid1 lid2 r sigma mor) =
     legal_mor lid2 mor && case map_sign r sigma of
        Just (sigma',_) -> sigma' == cod lid2 mor
        Nothing -> False

gEmbed :: G_morphism -> GMorphism
gEmbed (G_morphism lid mor) =
  GMorphism lid lid (id_repr lid) (dom lid mor) mor

-- homogeneous Union of two Grothendieck signatures
homogeneousGsigUnion :: Pos -> G_sign -> G_sign -> Result G_sign
homogeneousGsigUnion pos (G_sign lid1 sigma1) (G_sign lid2 sigma2) = do
  sigma2' <- rcoerce lid2 lid1 pos sigma2
  sigma3 <- signature_union lid1 sigma1 sigma2'
  return (G_sign lid1 sigma3)

-- homogeneous Union of a list of Grothendieck signatures
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


-- homogeneous Union of a list of morphisms
homogeneousMorManyUnion :: Pos -> [G_morphism] -> Result G_morphism
homogeneousMorManyUnion pos [] =
  fatal_error "homogeneous union of emtpy list of morphisms" pos
homogeneousMorManyUnion pos (G_morphism lid mor : gmors) = do
  mors <- let coerce_lid (G_morphism lid1 mor1) = 
                    rcoerce lid lid1 pos mor1
             in sequence (map coerce_lid gmors)
  bigMor <- let mor_union s1 s2 = do
                       s1' <- s1
                       morphism_union lid s1' s2
                in foldl mor_union (return mor) mors
  return (G_morphism lid bigMor)

inclusion :: G_sign -> G_sign -> GMorphism
inclusion (G_sign _lid1 _sigma1) (G_sign _lid2 _sigma2) = error "inclusion"
