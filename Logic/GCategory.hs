{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Grothendieck)

   
   The Grothendieck signature category
-}

module Logic.GCategory where

import Logic.Logic
import Logic.Comorphism
import Logic.Grothendieck
import Logic.LaTeX_Grothendieck
import ATC.Grothendieck
import Common.Result
import Common.Id

instance Category Grothendieck G_sign GMorphism where
  ide _ (G_sign lid sigma) = 
    GMorphism (IdComorphism lid) sigma (ide lid sigma)
  comp _ 
       (GMorphism r1 sigma1 mor1) 
       (GMorphism r2 _sigma2 mor2) = 
    do let lid1 = sourceLogic r1
           lid2 = targetLogic r1
           lid3 = sourceLogic r2
           lid4 = targetLogic r2
       ComorphismAux r1' _ _ sigma1' mor1' <- 
         (coerce lid2 lid3 $ ComorphismAux r1 lid1 lid2 sigma1 mor1)
       mor1'' <- map_morphism r2 mor1'
       mor <- comp lid4 mor1'' mor2
       return (GMorphism (CompComorphism r1' r2) sigma1' mor)
  dom _ (GMorphism r sigma _mor) = 
    G_sign (sourceLogic r) sigma
  cod _ (GMorphism r _sigma mor) = 
    G_sign lid2 (cod lid2 mor)
    where lid2 = targetLogic r
  legal_obj _ (G_sign lid sigma) = legal_obj lid sigma 
  legal_mor _ (GMorphism r sigma mor) =
    legal_mor lid2 mor && 
    case map_sign r sigma of
      Just (sigma',_) -> sigma' == cod lid2 mor
      Nothing -> False
    where lid2 = targetLogic r

-- | Composition of two Grothendieck signature morphisms 
-- | with intermediate inclusion
compInclusion :: LogicGraph -> GMorphism -> GMorphism -> Result GMorphism
compInclusion lg mor1 mor2 = do
  incl <- ginclusion lg (cod Grothendieck mor1) (dom Grothendieck mor2)
  mor <- maybeToResult nullPos
           "compInclusion: composition falied" $ comp Grothendieck mor1 incl
  maybeToResult nullPos
           "compInclusion: composition falied" $ comp Grothendieck mor mor2


-- | Composition of two Grothendieck signature morphisms 
-- | with intermediate homogeneous inclusion
compHomInclusion :: GMorphism -> GMorphism -> Result GMorphism
compHomInclusion mor1 mor2 = compInclusion emptyLogicGraph mor1 mor2
