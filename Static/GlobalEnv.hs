-- needs ghc -fglasgow-exts -package data -package posix

{- HetCATS/AS_Structured.hs
   $Id$
   Till Mossakowski

   Data structure for global environment, representing heterogeneous CASL 
   structured and architectural specifications and libraries. 
   This is based on Logic.hs, providing a logic
   independent interface for data structures for the local environment (signature).
   The structure of the global environment follows the notion
   of global environment in the CASL semantics (study note S-9).
   However, there is a difference: we do not (only) flatten the specifications
   into signatures, but rather keep the structure of the
   specification (while transforming it into a more institution-like
   form, i.e. symbol maps are replaced by the induced signature morphisms).
   The flattened local environment is kept at the outermost level
   of the global environment, but not at the inner nodes (except
   for nodes for basic specifications, of course), since
   this would consume too much space.

   A library environment is a table of global environments,
   one for each library. This table is kept during static analysis,
   in order to avoid re-reading of libraries.  

   References:
   CASL Semantics, version of July 24, 2001
   
   T. Mossakowski, B. Klin:
   Institution Independent Static Analysis for CASL
   15h WADT 2001, LNCS 2267, p. 221-237, 2002.


   todo:
   Should architectural data structures be based on SpecLenvs as well?
   
-}

module GlobalEnv where
import Id
import AS_Annotation
import Grothendieck
import AS_Structured
import AS_Architecture
import AS_Library
import FiniteMap
import Posix
import Common.Lib.Graph

-- Keep structure of specifications, 
-- while replacing basic specs and symbol maps with their static semantics
-- (i.e. signatures, sentences and signature morphisms)
data SpecEnv = Basic_specEnv G_sign G_l_sentence_list
	  | TranslationEnv SpecEnv G_morphism
	  | ReductionEnv SpecEnv G_morphism
	  | UnionEnv [SpecEnv]
	  | ExtensionEnv [(SpecEnv,Annotation)]
	  | Free_spec SpecEnv
          | Cofree SpecEnv  -- covers CoCASL as well
	  | Local_spec SpecEnv SpecEnv G_morphism
	  | Closed_spec SpecEnv 
	  | Spec_instEnv {
                name :: SPEC_NAME,
                body :: SpecEnv,
                fittingMorphism :: G_morphism,
                actualParams :: [SpecEnv]
              }
           -- deriving (Show,Eq)

-- Add flattened Env and sublogic at the outer level
-- for purposes of a quick static analysis
data SpecLenv = SpecLenv {
                    flattenedEnv :: G_sign,
                    hiddenEnv :: G_sign,
                    structuredEnv :: SpecEnv,
                    sublogic :: G_sublogics
                  }
                          
data GenericityEnv = GenericityEnv {
                       allImports :: SpecLenv, 
                       formalParams :: [SpecLenv], 
                       flattenedParams :: G_sign
                  }

-- Follows the semantic domains of the architectural semantics
type CompSigs = G_sign_list
type UnitSig = (CompSigs, G_sign)
type StBasedUnitCtx = FiniteMap UNIT_NAME Node
type BasedParUnitSig = (Node, UnitSig)
type StParUnitCtx = FiniteMap UNIT_NAME BasedParUnitSig
type ExtStUnitCtx = (StParUnitCtx, StBasedUnitCtx, G_diagram)
type ArchSig = (ExtStUnitCtx, UnitSig)

-- The global environment
data GlobalEntry =   
    SpecDefnEnv GenericityEnv SpecLenv
  | ViewDefnEnv GenericityEnv SpecLenv G_morphism SpecLenv
  | ArchSpecDefnEnv ArchSig
  | UnitSpecDefnEnv UnitSig

data GlobalEnv = GlobalEnv (FiniteMap SIMPLE_ID GlobalEntry) [Annotation]
emptyGlobalEnv :: GlobalEnv
emptyGlobalEnv = GlobalEnv emptyFM []


-- Flattened global environment
data FSign = FSign {
        fFlattenedEnv, fHiddenEnv :: G_sign,
        fAxioms :: G_l_sentence_list
      }
data FGenericityEnv  = FGenericityEnv {
                         fAllImports :: FSign, 
                         fFormalParams :: FSign,
                         fFlattenedParams :: FSign
             }

data FGlobalEntry = 
     FSpecDefnEnv FGenericityEnv FSign
   | FViewDefnEnv FGenericityEnv FSign G_morphism FSign
   | FArchSpecDefnEnv ArchSig
   | FUnitSpecDefnEnv UnitSig
			
data FGlobalEnv = FGlobalEnv (FiniteMap SIMPLE_ID FGlobalEntry) [Annotation]
emptyFGlobalEnv :: FGlobalEnv
emptyFGlobalEnv = FGlobalEnv emptyFM []


type LibEnv = FiniteMap String (GlobalEnv, LIB_DEFN, EpochTime)
emptyLibEnv :: LibEnv
emptyLibEnv = emptyFM

