
-- needs ghc -fglasgow-exts -package data

{- HetCATS/CASL2HasCASL.hs
   $Id$
   Till Mossakowski
   
   The embedding comorphism from CASL to HasCASL.

-}

module Comorphisms.CASL2HasCASL where

import Logic.Logic
import Logic.Comorphism

-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
--import CASL.Print_AS_Basic
--import CASL.Parse_AS_Basic
--import CASL.SymbolParser
--import Logic.ParsecInterface
--import Common.AS_Annotation
--import Common.AnnoState(emptyAnnos)
--import Common.Lib.Parsec
--import Common.Lib.Map
--import Logic.Logic
--import Common.Lexer((<<))
import CASL.Sublogic
import CASL.StaticAna
import CASL.Morphism

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.Le
--import HasCASL.PrintLe
--import HasCASL.AsToLe
import HasCASL.Symbol
--import HasCASL.ParseItem
import HasCASL.Morphism

import Common.Lib.Set
import Data.Dynamic

-- Logic comorphisms (possibly also morphisms via adjointness)

data CASL2HasCASL = CASL2HasCASL deriving (Show)
instance Language CASL2HasCASL -- default definition is okay

instance Comorphism CASL2HasCASL
               CASL CASL.Sublogic.CASL_Sublogics
               BASIC_SPEC Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               CASL.Morphism.Morphism
               CASL.Morphism.Symbol CASL.Morphism.RawSymbol ()
               HasCASL HasCASL_Sublogics
               BasicSpec Term SymbItems SymbMapItems
               HasCASL.Le.Env 
               HasCASL.Morphism.Morphism
               HasCASL.Morphism.Symbol HasCASL.Morphism.RawSymbol () where
    sourceLogic _ = CASL
    source_sublogic _ = CASL.Sublogic.top
    targetLogic _ = HasCASL
    target_sublogic _ = ()
    --map_sign _ -> sign1 -> Maybe (sign2,[sentence2])
    --map_morphism _ morphism1 -> Maybe morphism2
    --map_sentence _ sign1 -> sentence1 -> Maybe sentence2
    --map_symbol :: cid -> symbol1 -> Set symbol2

