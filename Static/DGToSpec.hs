{- |
Module      :  $Header$
Description :  Conversion of development graph back to structured specification
Copyright   :  (c) Till Mossakowski, C. Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Convert development graph back to structured specification
  and compute theory
-}

module Static.DGToSpec
    ( dgToSpec
    ) where

import Logic.Logic
import Logic.Grothendieck
import Static.DevGraph
import Static.GTheory

import Syntax.AS_Structured
import Common.AS_Annotation
import Logic.Prover

import Common.Id
import Common.ExtSign
import Data.Graph.Inductive.Graph


import Control.Monad


-- | convert a node of a development graph back into a specification
dgToSpec :: Monad m => DGraph -> Node -> m SPEC
dgToSpec dg = return . dgToSpec0 dg

dgToSpec0 :: DGraph -> Node -> SPEC
dgToSpec0 dg node = case matchDG node dg of
  (Just (preds, _, n, _), subdg) ->
   let apredSps = map (emptyAnno . dgToSpec0 subdg . snd) preds
       myhead l = case l of
                    [x] -> x
                    _ -> error "dgToSpec0.myhead"
   in if isDGRef n then
          Spec_inst (getName $ dgn_name n) [] nullRange
      else if dgn_origin n == DGBasic then case dgn_theory n of
         G_theory lid1 (ExtSign sigma _) _ sen' _ ->
           let b = Basic_spec (G_basic_spec lid1 $
                 sign_to_basic_spec lid1 sigma $ toNamedList sen') nullRange
           in if null apredSps then b
              else Extension (apredSps ++ [emptyAnno b]) nullRange
      else case dgn_origin n of
        DGExtension ->
         (Extension apredSps nullRange)
        DGUnion ->
         (Union apredSps nullRange)
        DGTranslation ->
         (Translation (myhead apredSps) (Renaming [] nullRange))
        DGHiding ->
         (Reduction (myhead apredSps) (Hidden [] nullRange))
        DGRevealing ->
         (Reduction (myhead apredSps) (Hidden [] nullRange))
        DGFree ->
         (Free_spec (myhead apredSps) nullRange)
        DGCofree ->
         (Cofree_spec (myhead apredSps) nullRange)
        DGSpecInst name ->
         (Spec_inst name [] nullRange)
        _ -> (Extension apredSps nullRange)
  _ -> error "dgToSpec0"

