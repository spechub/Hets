{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

module ATC.Comorphism where

import Logic.Comorphism
import Logic.Logic
import Comorphisms.LogicGraph
import Common.ATerm.Lib
import Common.Lib.Set
import Data.Maybe
import Data.Dynamic
--import ATC.Grothendieck

data IdMonad a = IdMonad a

instance Monad IdMonad where
   return = IdMonad
   IdMonad x >>= f = f x

unpackIdMonad (IdMonad x) = x

{-getLogicId :: (lid -> a) -> AnyLogic -> a
getLogicId constr_fun l =
   unpackIdMonad (
      do Logic lid <- IdMonad l
         return (constr_fun lid)
    )-}


instance (Comorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2, 
          Comorphism cid2
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3) =>
          ATermConvertible (CompComorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1 
            cid2
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3) where
     toShATerm att0 (CompComorphism cid1 cid2) = 
	 let (att1,i1) = toShATerm att0 (language_name cid1)
             (att2,i2) = toShATerm att1 (language_name cid2)
         in addATerm (ShAAppl "CompComorphism" [i1,i2] []) att2
     fromShATerm att =  error "bla" {-
         case aterm of
	    (ShAAppl "CompComorphism" [i1,i2] _) ->
		let i1'  = fromShATerm (getATermByIndex1 i1 att)
                    cid1 = getLogicId $ lookupLogic_in_LG ("couldn't find Logic " ++ i1' ++ " in Logic Graph") i1'
                    i2'  = fromShATerm (getATermByIndex1 i2 att)
		    cid2 = getLogicId $ lookupLogic_in_LG ("couldn't find Logic " ++ i2' ++ " in Logic Graph") i2'
                in (CompComorphism cid1 cid2)
         where
         aterm = getATerm att -}












