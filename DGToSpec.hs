{- HetCATS/DGToSpec.hs
   $Id$
   Till Mossakowski

   Convert development graph back to structured specification

   Todo:

-}


module DGToSpec
where

import Maybe
import Logic
import LogicRepr
import Grothendieck
import Graph
import DevGraph
import AS_Structured
import AS_Annotation
import GlobalAnnotations
import GlobalAnnotationsFunctions
import Result
import Id
import FiniteSet
import FiniteMap
import List
import PrettyPrint

emptyAnno x = Annoted x [] [] []

dgToSpec :: DGraph -> Node -> Result SPEC
dgToSpec dg node = do
  let (_,_,n,preds) = context node dg
  predSps <- sequence (map (dgToSpec dg . snd) preds)
  let apredSps = map emptyAnno predSps
      pos = map (\_ -> nullPos) predSps
  case n of
    (DGNode _ (G_sign lid1 sigma) (G_l_sentence lid2 sen) DGBasic) -> 
      do sen' <- rcoerce lid1 lid2 nullPos sen
         let b = Basic_spec (G_basic_spec lid1 (sign_to_basic_spec lid1 sigma sen'))
         if null apredSps
          then return b
          else return (Extension (apredSps++[emptyAnno b]) pos)
    (DGNode _ _ _ DGExtension) ->
         return (Extension apredSps pos)
    (DGNode _ _ _ DGUnion) ->
         return (Union apredSps pos)
    (DGNode _ _ _ DGTranslation) ->
         return (Translation (head apredSps) (Renaming [] []))
    (DGNode _ _ _ DGHiding) ->
         return (Reduction (head apredSps) (Hidden [] []))
    (DGNode _ _ _ DGRevealing) ->
         return (Reduction (head apredSps) (Hidden [] []))
    (DGNode _ _ _ DGFree) ->
         return (Free_spec (head apredSps) pos)
    (DGNode _ _ _ DGCofree) ->
         return (Cofree_spec (head apredSps) pos)
    (DGNode _ _ _ (DGSpecInst name)) ->
         return (Spec_inst name [] pos)
    (DGRef (Just name) _ _) -> return (Spec_inst name [] pos)
    otherwise -> return (Extension apredSps pos)
