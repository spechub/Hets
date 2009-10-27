{- |
Module 		: ./ExtModal/MorphismExtension.hs
Description 	: Morphism extension for modal signature morphisms 
Copyright   	:
License		:
Maintainer	: codruta.liliana@gmail.com
Stability	: experimental
Portability	:
-}

module ExtModal.MorphismExtension where 

import qualified Data.Map as Map
import qualified Data.Set as Set

import CASL.Morphism
import Common.Id

import ExtModal.ExtModalSign

data MorphExtension = MorphExtension
	{ source :: EModalSign
	, target :: EModalSign
	, mod_map :: Map.Map SIMPLE_ID SIMPLE_ID
	, nom_map :: Map.Map SIMPLE_ID SIMPLE_ID
	} deriving (Show, Eq, Ord)

emptyMorphExtension :: MorphExtension 
emptyMorphExtension = MorphExtension emptyEModalSign emptyEModalSign Map.empty Map.empty


instance MorphismExtension EModalSign MorphExtension where 
 
	ideMorphismExtension sgn = 
		let insert_next old_map s_id = Map.insert  s_id s_id old_map in
		MorphExtension sgn sgn 
			(foldl insert_next Map.empty (Map.keys (modalities sgn)))
			(foldl insert_next Map.empty (Set.toList (nominals sgn)))

	composeMorphismExtension _ me1 me2 = 
		if me1 == me2 
		   then let me_compos second_map  old_map (me_k, me_val) = 
		   		if (Map.member me_val second_map) then Map.insert me_k (second_map Map.! me_val) old_map
								  else old_map
		   	in return $ MorphExtension (source me1) (target me2) 
					(foldl (me_compos (mod_map me2)) Map.empty (Map.toList (mod_map me1)))
					(foldl (me_compos (nom_map me2)) Map.empty (Map.toList (nom_map me1)))
		   else return emptyMorphExtension

	inverseMorphismExtension me = 
		let swap_arrows old_map (me_k, me_val) = Map.insert me_val me_k old_map
		    occurs_alt [] once _ = once
		    occurs_alt ((_,me_val1):l) True me_val2 = 
		    	if me_val1 == me_val2 then True else occurs_alt l True me_val2
		    occurs_alt ((_,me_val1):l) False me_val2 = 
		    	if me_val1 == me_val2 then occurs_alt l True me_val2 else occurs_alt l False me_val2
		in if Map.keys (modalities (target me)) == Map.elems (mod_map me) 
			&& Set.toList (nominals (target me)) == Map.elems (nom_map me)
			&& Map.filter (occurs_alt (Map.toList (mod_map me)) False) (mod_map me) == Map.empty
			&& Map.filter (occurs_alt (Map.toList (nom_map me)) False) (nom_map me) == Map.empty 
		      then return $ MorphExtension (target me) (source me) 
				(foldl swap_arrows Map.empty (Map.toList (mod_map me)))
				(foldl swap_arrows Map.empty (Map.toList (nom_map me)))
		      else return emptyMorphExtension

	isInclusionMorphismExtension me = 
		let target_ide = ideMorphismExtension (target me) in
		(Map.isSubmapOf (mod_map me) (mod_map target_ide)) 
			&& (Map.isSubmapOf (nom_map me) (nom_map target_ide)) 

