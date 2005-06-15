{-| 
Module      :  $Header$
Copyright   :  (c) Sonja Groening, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

   Converts a Haskell module with pure AXIOM-Pragma to a Haskell
   module with AXIOM-Pragmas and corresponding lambda-expressions
-}

module Hatchet.ExtHaskellCvrt where

import Data.Char(toLower)
import Haskell.Hatchet.HsSyn

cvrtHsModule :: HsModule -> HsModule
cvrtHsModule (HsModule name exports imports declList) = 
              HsModule name 
                       exports
                       imports
                       (cvrtHsDeclList declList)

cvrtHsDeclList :: [HsDecl] -> [HsDecl]
cvrtHsDeclList [] = []
cvrtHsDeclList (x:xs) = case x of
                            HsAxiomBind b -> 
                               x:cvrtAxBinding b ++ cvrtHsDeclList xs
                            _             -> x:cvrtHsDeclList xs

cvrtAxBinding :: AxBinding -> [HsDecl]
cvrtAxBinding (AxiomDecl name formula) = 
                 [HsPatBind (SrcLoc (-1) (-1)) 
                            (cvrtAxiomName name) 
                            (cvrtFormula formula) []]
cvrtAxBinding (AndBindings b1 b2) = cvrtAxBinding b1 ++ cvrtAxBinding b2

cvrtFormula :: Formula -> HsRhs
cvrtFormula f = case f of
                    AxQuant quant form -> HsUnGuardedRhs (cvrtWithQuant 
                                                              quant form)
                    _                  -> HsUnGuardedRhs (cvrtWithoutQuant f)

cvrtWithQuant :: Quantifier -> Formula -> HsExp
cvrtWithQuant (AxForall []) f =  cvrtWithoutQuant f
cvrtWithQuant (AxForall (a:axbList)) f = 
                 HsApp (HsVar (UnQual (HsIdent "allof"))) 
                       (HsParen (HsLambda (SrcLoc (-1) (-1)) 
                                          [HsPVar (cvrtAxiomBndr a)] 
                                 (cvrtWithQuant (AxForall axbList) f)))

cvrtWithQuant (AxExists []) f =  cvrtWithoutQuant f
cvrtWithQuant (AxExists (a:axbList)) f = 
                 HsApp (HsVar (UnQual (HsIdent "ex"))) 
                       (HsParen (HsLambda (SrcLoc (-1) (-1)) 
                                [HsPVar (cvrtAxiomBndr a)] 
                                (cvrtWithQuant (AxForall axbList) f)))

cvrtWithQuant (AxExistsOne []) f =  cvrtWithoutQuant f
cvrtWithQuant (AxExistsOne (a:axbList)) f = 
                 HsApp (HsVar (UnQual (HsIdent "exone"))) 
                                            (HsParen (HsLambda (SrcLoc 
                                            (-1) (-1)) [HsPVar 
                                            (cvrtAxiomBndr a)] 
                                            (cvrtWithQuant (AxForall axbList) 
                                                                         f)))

cvrtWithoutQuant :: Formula -> HsExp
cvrtWithoutQuant (AxExp expr) = expr
cvrtWithoutQuant (AxEq form expr _) = HsInfixApp 
                                       (cvrtWithoutQuant form) 
                                       (HsVar (UnQual (HsSymbol "==="))) expr
cvrtWithoutQuant _ = error "cvrtWithoutQuant"


cvrtAxiomBndr :: AxiomBndr -> HsName
cvrtAxiomBndr (AxiomBndr name) = name
cvrtAxiomBndr (AxiomBndrSig name _) = name

cvrtAxiomName :: AxiomName -> HsPat
cvrtAxiomName (n:ame) = HsPVar (HsIdent ((toLower n):ame))
cvrtAxiomName "" = error "cvrtAxiomName"
