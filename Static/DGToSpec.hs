{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   Convert development graph back to structured specification

-}


module Static.DGToSpec
where

import Data.Maybe
import Logic.Logic
import Logic.Grothendieck
import Common.Lib.Graph
import Static.DevGraph
import Syntax.AS_Structured
import Common.AS_Annotation
import Common.Result
import Common.Id
import Data.List
import Common.PrettyPrint

emptyAnno :: SPEC -> Annoted SPEC
emptyAnno x = Annoted x [] [] []

dgToSpec :: DGraph -> Node -> Result SPEC
dgToSpec dg node = do
  let (_,_,n,preds) = context node dg
  predSps <- sequence (map (dgToSpec dg . snd) preds)
  let apredSps = map emptyAnno predSps
      pos = map (\_ -> nullPos) predSps
  case n of
    (DGNode _ (G_sign lid1 sigma) (G_l_sentence_list lid2 sen) DGBasic) -> 
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
    _ -> return (Extension apredSps pos)
