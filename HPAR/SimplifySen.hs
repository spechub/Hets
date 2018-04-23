{- |
Module      :  ./HPAR/SimplifySen.hs
Description : simplification of formulas and terms for output after analysis
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  portable

Simplification of formulas and terms for output after analysis

-}

module HPAR.SimplifySen where

import CASL.SimplifySen
import Common.Lib.State

import qualified CASL.Sign as CSign
import qualified HPAR.Sign as HSign
import qualified RigidCASL.Sign as RSign
import qualified HPAR.AS_Basic_HPAR as HBasic

simplifyHPARSen :: HSign.HSign -> HBasic.HFORMULA -> HBasic.HFORMULA
simplifyHPARSen hsig hsen = 
 case hsen of 
  HBasic.Base_formula pfrm r -> 
    let pfrm' = simplifyCASLSen (RSign.caslSign $ HSign.baseSig hsig) pfrm
    in HBasic.Base_formula pfrm' r  
  HBasic.Nominal _ _ _ -> 
    hsen
  HBasic.AtState nom frm r -> 
    HBasic.AtState nom (simplifyHPARSen hsig frm) r
  HBasic.BoxFormula md frm r -> 
    HBasic.BoxFormula md (simplifyHPARSen hsig frm) r
  HBasic.DiamondFormula md frm r -> 
    HBasic.DiamondFormula md (simplifyHPARSen hsig frm) r
  HBasic.Negation frm r -> 
    HBasic.Negation (simplifyHPARSen hsig frm) r
  HBasic.Conjunction xs r -> 
    HBasic.Conjunction (map (simplifyHPARSen hsig) xs) r
  HBasic.Disjunction xs r -> 
    HBasic.Disjunction (map (simplifyHPARSen hsig) xs) r
  HBasic.Implication x y r -> 
    HBasic.Implication (simplifyHPARSen hsig x) (simplifyHPARSen hsig y) r
  HBasic.Equivalence x y r -> 
    HBasic.Equivalence (simplifyHPARSen hsig x) (simplifyHPARSen hsig y) r
  HBasic.QuantRigidVars q vdecls frm r -> 
   let csig = execState (mapM_ CSign.addVars vdecls) $ HSign.baseSig hsig
       hsig' = hsig{HSign.baseSig = csig}
   in HBasic.QuantRigidVars q vdecls (simplifyHPARSen hsig' frm) r
  HBasic.QuantNominals q noms frm r -> 
    HBasic.QuantNominals q noms (simplifyHPARSen hsig frm) r
