-- needs ghc -fglasgow-exts -package lang

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
   Use better tables
   Should architectural data structures be based on SpecLenvs as well?
   
-}

module GlobalEnv where
import Id
import Grothendieck
import Logic
import AS_Structured
import AS_Architecture
import AS_Library

type Table a b = [(a,b)]  -- very inefficient, improve!

-- Keep structure of specifications, 
-- while replacing basic specs and symbol maps with their static semantics
-- (i.e. signatures, sentences and signature morphisms)
data SpecEnv = Basic_specEnv G_sign G_l_sentence_list
	  | TranslationEnv SpecEnv G_morphism
	  | ReductionEnv SpecEnv G_morphism
	  | UnionEnv [SpecEnv]
	  | ExtensionEnv [(SpecEnv,Anno)]
	  | Free_spec SpecEnv
          | Cofree SpecEnv  -- covers CoCASL as well
	  | Local_spec SpecEnv SpecEnv G_morphism
	  | Closed_spec SpecEnv 
	  | Spec_instEnv {
                Name :: SPEC_NAME,
                Body :: SpecEnv,
                FittingMorphism :: G_morphism,
                ActualParams :: [SpecEnv]
              }
            deriving (Show,Eq)

-- Add flattened Env at the outer level
-- for purposes of a quick static analysis
data SpecLenv = SpecLenv {
                    FlattenedEnv :: G_local_env,
                    HiddenEnv :: G_local_env,
                    StructuredEnv :: SpecEnv
                  }
                          
data GenericityEnv = GenericityEnv {
                       AllImports :: SpecLenv, 
                       FormalParams :: [SpecLenv], 
                       FlattenedParams :: G_local_env
                  }

-- Follows the semantic domains of the architectural semantics
type CompSigs = G_sign_list
type UnitSig = (CompSigs, G_sign)
type StBasedUnitCtx = Table UNIT_NAME Node
type BasedParUnitSig = (Node, UnitSig)
type StParUnitCtx = Table UNIT_NAME BasedParUnitSig
type ExtStUnitCtx = (StParUnitCtx, StBasedUnitCtx, G_diagram)
type ArchSig = (ExtStUnitCtx, UnitSig)

-- The global environment
data GlobalEntry =   
    SpecDefnEnv GenericityEnv SpecLenv
  | ViewDefnEnv GenericityEnv SpecLenv G_morphism SpecLenv
  | ArchSpecDefnEnv ArchSig
  | UnitSpecDefnEnv UnitSig

data GlobalEnv = GlobalEnv (Table SimpleId GlobalEntry) [Anno]
emptyGlobalEnv = []


-- Flattened global environment
data FSign = FSign {
        FFlattenedEnv, FHiddenEnv :: G_local_env,
        Axioms :: G_l_sentence_list
      }
data FGenericityEnv  = FGenericityEnv {
                         FAllImports :: FSign, 
                         FFormalParams :: FSign,
                         FFlattenedParams :: FSign
             }

data FGlobalEntry = 
     FSpecDefnEnv FGenericityEnv FSign
   | FViewDefnEnv FGenericityEnv FSign G_morphism FSign
   | FArchSpecDefnEnv ArchSig
   | FUnitSpecDefnEnv UnitSig
			
data FGlobalEnv = FGlobalEnv (Table SimpleId FGlobalEntry) [Anno]
emptyFGlobalEnv = []


type LibEnv = Table String (GlobalEnv, LIB_DEFN)

emptyLibEnv = []

