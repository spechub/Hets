
{- |
Module      :  $Header$
Copyright   :  (c)  Markus Roggenbach, Till Mossakowski and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  non-portable


   Here is the place where the class Logic is instantiated for CspCASL.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions
     - Modul Sign.hs mit CSP-CASL-Signaturen und Morphismen, basiernd auf CASL.Sign
          CSP-CASL-Signatur = (CASL-Sig,Menge von Kanalnamen)
          CSP-CASL-Morphismus = (CASL-Morphismus, Kanalnamenabbildung)
                      oder nur CASL-Morphismus
          SYMB_ITEMS SYMB_MAP_ITEMS: erstmal von CASL (d.h. nur CASL-Morphismus)
     - instance Sentences
        Sätze = entweder CASL-Sätze oder CSP-CASL-Sätze
        Rest soweit wie möglich von CASL übernehmen
     - statische Analyse (gemäß Typ in Logic.Logic) schreiben
       und unten für basic_analysis einhängen

    Kür:
     - Teillogiken (instance LatticeWithTop ...)

-}

module CspCASL.Logic_CspCASL(CspCASL(CspCASL)) where

import CspCASL.AS_CSP_CASL
import CspCASL.Parse_hugo
import CspCASL.LaTeX_AS_CSP_CASL

import CASL.AS_Basic_CASL

import Logic.ParsecInterface
import Common.AS_Annotation
import Common.AnnoState(emptyAnnos)
import Common.Lib.Parsec
import Common.Lib.Map
import Logic.Logic
import Common.Lexer((<<))

import qualified CASL.Sublogic
import CASL.StaticAna
import CASL.SymbolParser
import CASL.Logic_CASL(CASL(CASL))

import Data.Dynamic

import Common.PrettyPrint
import Common.PrintLaTeX
import Common.Lib.Pretty

import CspCASL.ATC_CspCASL

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data CspCASL = CspCASL deriving (Show)
instance Language CspCASL  -- default definition is okay

instance Category CspCASL () ()
    where
         -- ide :: id -> object -> morphism
	 ide CspCASL sigma = fun_err "ide"
         -- o :: id -> morphism -> morphism -> Maybe morphism
	 comp CspCASL sigma1 _sigma2 = fun_err "comp"
         -- dom, cod :: id -> morphism -> object
	 dom CspCASL _ = fun_err "dom"
	 cod CspCASL _ = fun_err "cod"
         -- legal_obj :: id -> object -> Bool
	 legal_obj CspCASL _ = fun_err "legall_obj"
         -- legal_mor :: id -> morphism -> Bool
	 legal_mor CspCASL _ = fun_err "legal_mor"


-- abstract syntax, parsing (and printing)

instance Syntax CspCASL Basic_CSP_CASL_C_SPEC
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec CspCASL = Just(toParseFun basicCspCaslCSpec emptyAnnos)
	 parse_symb_items CspCASL = Just(toParseFun symbItems ())
	 parse_symb_map_items CspCASL = Just(toParseFun symbMapItems ())

-- lattices (for sublogics)

{-
instance LatticeWithTop () where
    -- meet, join :: l -> l -> l
    meet = fun_err "meet"
    join = fun_err "join"
    -- top :: l
    top = fun_err "top"

-}

-- CspCASL logic


instance Sentences CspCASL () () () () ()

instance StaticAnalysis CspCASL Basic_CSP_CASL_C_SPEC () ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               () () () ()  where
         basic_analysis CspCASL = Just(\(bspec,_,_) -> return (bspec,(),(),[]))
         stat_symb_map_items CspCASL = error "Logic_CspCASL.hs"
         stat_symb_items CspCASL = error "Logic_CspCASL.hs"

instance Logic CspCASL ()
               Basic_CSP_CASL_C_SPEC () SYMB_ITEMS SYMB_MAP_ITEMS
               ()
               ()
               () () () where

         data_logic CspCASL = Just (Logic CASL)


cspCaslBasicSpecTc :: TyCon
cspCaslBasicSpecTc = mkTyCon "CspCASL.Basic_CSP_CASL_C_SPEC"

instance Typeable Basic_CSP_CASL_C_SPEC where
    typeOf _ = mkAppTy cspCaslBasicSpecTc []

---- helpers ---------------------------------
fun_err :: String -> a
fun_err fname = 
    error ("*** Function \"" ++ fname ++ "\" is not yet implemented!")

----------------------------------------------
