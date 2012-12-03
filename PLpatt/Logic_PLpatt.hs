module PLpatt.Logic_PLpatt where

import qualified PLpatt.Sign as Sign
import qualified PLpatt.Morphism as Morphism
import qualified PLpatt.AS_BASIC_PLpatt as AS
--import qualified PLpatt.Tools as Tools
--import qualified Generic.Tools as Generic
--import qualified PLpatt.Sublogic as SL

data PLpatt = PLpatt deriving Show

instance Logic PLpatt () Sign.Sign 
         Morphism.Morphism AS.Formulas ()
         AS.Symb_map where
 logic_name = show 
 id lid = Morphism.id
 comp lid = Morphism.comp
-- parse_basic_spec lid = Generic.parseSpec
-- map_sen lid = Morphism.mapSen
-- basic_analysis lid = Tools.theo_from_pt
-- stat_symb_map lid = Tools.mor_from_pt
-- minSublogic lid = SL.minSublogic


