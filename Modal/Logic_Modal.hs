{- HetCATS/Modal/Logic_Modal.hs
   $Id$
   Authors: Wiebke Herding
   Year:    2003
-}
module Modal.Logic_Modal where

import Logic.Logic
import Common.Id
import Common.Lib.Map as Map
import Common.Lib.Set as Set
import Logic.ParsecInterface
import Common.AnnoState(emptyAnnos)
-- import Common.AS_Annotation
import Data.Maybe
import Modal.AS_Modal
import Modal.Parse_AS
import Modal.Print_AS

data Modal = Modal deriving (Show)

instance Language Modal where  -- default definition is okay

type Sign = Set Id 
instance Show Sign where

type Morphism = (Sign, EndoMap Id, Sign)


instance Category Modal Sign Morphism  
    where
       -- ide :: id -> object -> morphism
       ide Modal sigma = (sigma, Map.fromList 
			  [(i,i) | i<- Set.toList sigma], sigma)
       -- comp :: id -> morphism -> morphism -> Maybe morphism
       comp Modal (sigma1 ,m1,_) (_,m2,sigma2) =  
	   Just (sigma1,Map.union m1 m2,sigma2)
       -- dom, cod :: id -> morphism -> object
       dom Modal (sigma,_,_) = sigma
       cod Modal (_,_,sigma) = sigma
       -- legal_obj :: id -> object -> Bool
       legal_obj Modal _ = True
       -- legal_mor :: id -> morphism -> Bool
       legal_mor Modal (sigma,m,_)
		| Map.keys m == Set.toList sigma	 = True 
		| True	 = False

-- abstract syntax, parsing (and printing)

instance Syntax Modal BASIC_SPEC 
 		SYMB_ITEMS SYMB_MAP_ITEMS
       where 
--         parse_basic_spec :: id -> Maybe(ParseFun basic_spec)
--         parse_symb_items :: id -> Maybe(ParseFun symb_items)
--         parse_symb_map_items :: id -> Maybe(ParseFun symb_map_items)
	   parse_basic_spec Modal = Just(toParseFun basicSpec emptyAnnos)
--	   parse_symb_items Modal = Just(toParseFun symbItems ())
--	   parse_symb_map_items Modal = Just(toParseFun symbMapItems ())








