module <LogicName>.Logic_<LogicName> where

import qualified <LogicName>.Sign as Sign
import qualified <LogicName>.Morphism as Morphism
import qualified <LogicName>.AS_BASIC_<LogicName> as AS
import qualified <LogicName>.Tools as Tools
--import qualified Generic.Tools as Generic
--import qualified <LogicName>.Sublogic as SL

data <LogicName> = <LogicName> deriving Show

instance Logic <LogicName> SL.Sublogic Sign.Sign 
         Morphism.Morphism AS.Formulas Generic.ParseTree
         AS.Symb_map where
 logic_name = show 
 id lid = Morphism.id
 comp lid = Morphism.comp
 parse_basic_spec lid = Generic.parseSpec
 map_sen lid = Morphism.mapSen
 basic_analysis lid = Tools.theo_from_pt
 stat_symb_map lid = Tools.mor_from_pt
 minSublogic lid = SL.minSublogic


