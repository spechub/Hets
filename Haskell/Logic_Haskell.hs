{-# OPTIONS -fno-warn-missing-methods #-}
-- needs -package haskell-src

{- HetCATS/Haskell/Logic_Haskell.hs
   $Id$
   Authors: C. Maeder, S. Groening
   Year:    2003

   Here is the place where the class Logic is instantiated for Haskell.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions

-}

module Haskell.Logic_Haskell where

import CASL.AS_Basic_CASL       (SYMB_ITEMS, SYMB_MAP_ITEMS)
-- import CASL.ATC_CASL
-- import CASL.Print_AS_Basic
import CASL.SymbolParser        (symbItems, symbMapItems)
import Logic.ParsecInterface    (toParseFun)
import Logic.Logic              (Language,
                                 Category,
                                 Syntax,
                                 Sentences,
                                 StaticAnalysis,
                                 Logic,
                                 parse_basic_spec,
                                 parse_symb_items,
                                 parse_symb_map_items,
                                 basic_analysis)
import Data.Dynamic             (Typeable)
import Haskell.ATC_Haskell      -- ???

import Common.PrettyPrint       (PrettyPrint)
-- import Common.ATerm.Conversion  -- ???

import GHC.IOBase               (unsafePerformIO)
import Haskell.Hatchet.MultiModule (readModuleInfo)
import Haskell.Hatchet.MultiModuleBasics (ModuleInfo (..),
                                          joinModuleInfo,
                                          getTyconsMembers,
                                          getInfixDecls)
import Haskell.Hatchet.TIModule          (tiModule)
import Haskell.Hatchet.AnnotatedHsSyn    (AHsDecl (..),
                                          AModule (..))
import Haskell.Hatchet.Env               (listToEnv)
import Haskell.Hatchet.HaskellPrelude    (preludeDefs,
                                          tyconsMembersHaskellPrelude,
                                          preludeDataCons,
                                          preludeClasses,
                                          preludeTyconAndClassKinds,
                                          preludeInfixDecls,
                                          preludeSynonyms)
import Haskell.Hatchet.SynConvert        (toAHsModule)
import Haskell.Hatchet.Type              (assumpToPair)
import Haskell.Hatchet.Utils             (getAModuleName)
import Haskell.Hatchet.HsParsePostProcess (fixFunBindsInModule)
import Haskell.Hatchet.HsSyn             (HsModule (..),
                                          Module (..))
import Haskell.HatParser                 (HsDecls,
                                          hatParser)
import Haskell.HaskellUtils              (extractSentences)
import Common.Result                     (Result (..))

instance Typeable ModuleInfo
instance PrettyPrint ModuleInfo
-- instance ATermConvertible ModuleInfo
-- instance ATermConvertible HsModule
-- instance ATermConvertible AHsDecl
-- instance ATermConvertible HsDecls
instance Typeable HsDecls
instance Typeable AHsDecl
instance PrettyPrint HsDecls

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances

data Haskell = Haskell deriving (Show)
instance Language Haskell  -- default definition is okay

type Sign = ModuleInfo 
type Morphism = ()

instance Category Haskell Sign Morphism  

-- abstract syntax, parsing (and printing)

instance Syntax Haskell HsDecls
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec Haskell = Just(toParseFun hatParser ())
	 parse_symb_items Haskell = Just(toParseFun symbItems ())
	 parse_symb_map_items Haskell = Just(toParseFun symbMapItems ())

type Haskell_Sublogics = ()

type Sentence = AHsDecl

type Symbol = ()
type RawSymbol = ()

instance Sentences Haskell Sentence () Sign Morphism Symbol

instance StaticAnalysis Haskell HsDecls
               Sentence () 
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol 


       where
          basic_analysis Haskell = Just(basicAnalysis)
              where basicAnalysis (basicSpec, sig, _) = 	            
  			let basicMod = HsModule (Module "Anonymous") Nothing [] basicSpec

          -- re-group matches into their associated funbinds (patch up the output from the parser)
                            moduleSyntaxFixedFunBinds = fixFunBindsInModule basicMod;

          -- map the abstract syntax into the annotated abstract syntax
  			    annotatedSyntax = toAHsModule moduleSyntaxFixedFunBinds;

          -- this is the ModuleInfo that we were passing into tiModule
          -- earlier (just the Prelude stuff)
                            preludeModInfo = ModuleInfo {
                                  moduleName = AModule "Prelude",
                                  varAssumps = (listToEnv $ map assumpToPair preludeDefs),
                                  tyconsMembers = tyconsMembersHaskellPrelude, 
                                  dconsAssumps = (listToEnv $ map assumpToPair preludeDataCons),
                                  classHierarchy = listToEnv preludeClasses,
                                  kinds = (listToEnv preludeTyconAndClassKinds),
                                  infixDecls = preludeInfixDecls,
                                  synonyms = preludeSynonyms };

  --      -- now we read in the .ti files from the imported
  --      -- modules to pass in to tiModule
                            importedModInfo = unsafePerformIO(readModuleInfo annotatedSyntax)

                            initialModInfo = joinModuleInfo preludeModInfo importedModInfo
  		            (timings,
  			     moduleEnv,
   			     dataConEnv,
   			     newClassHierarchy,
   			     newKindInfoTable,
   			     moduleIds,
   			     moduleRenamed,
   			     moduleSynonyms) = unsafePerformIO (tiModule [] annotatedSyntax sig);
  			     modInfo = ModuleInfo {varAssumps = moduleEnv, 
    				 		  moduleName = getAModuleName annotatedSyntax,
    						  dconsAssumps = dataConEnv, 
    						  classHierarchy = newClassHierarchy,
    						  kinds = newKindInfoTable,
    						  tyconsMembers = getTyconsMembers moduleRenamed,
    						  infixDecls = getInfixDecls moduleRenamed,
    						  synonyms = moduleSynonyms }
  				      in
				       Result {diags = [],
					      maybeResult = Just (basicSpec, sig, sig, 
                                                                  (extractSentences annotatedSyntax)) }

instance Logic Haskell Haskell_Sublogics
               HsDecls Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol ()

