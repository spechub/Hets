module Haskell.ExtHaskellTrans where

import Char
import Haskell.Language.Syntax

transform :: HsModule -> HsModule
transform (HsModule src m expr imp rest) = HsModule src m expr ((HsImportDecl 
     (SrcLoc {srcFilename = "dummy", srcLine = (-1), srcColumn = (-1)})
     (Module "Haskell.Logical") False Nothing Nothing):imp) 
     (cvrtHsDeclList rest)

cvrtHsDeclList :: [HsDecl] -> [HsDecl]
cvrtHsDeclList [] = []
cvrtHsDeclList (x:xs) = case x of
                             HsAxiomBind b -> 
                               x:cvrtBinding b ++ cvrtHsDeclList xs
                             _ -> x:cvrtHsDeclList xs

cvrtBinding :: Binding -> [HsDecl]
cvrtBinding (AxiomDecl name formula) = 
                 [HsPatBind (SrcLoc {srcFilename = "dummy", srcLine = -1, 
                 srcColumn = -1}) (cvrtAxiomName name) 
                 (cvrtFormula formula) []]
cvrtBinding (AndBindings b1 b2) = cvrtBinding b1 ++ cvrtBinding b2

cvrtFormula :: Formula -> HsRhs
cvrtFormula f = case f of
                    AxQuant quant form -> HsUnGuardedRhs (cvrtWithQuant 
                                                             quant form)
                    _ -> HsUnGuardedRhs (cvrtWithoutQuant f)

cvrtWithQuant :: Quantifier -> Formula -> HsExp
cvrtWithQuant (AxForall []) f =  cvrtWithoutQuant f
cvrtWithQuant (AxForall (a:axbList)) f = HsApp (HsVar (UnQual 
                                          (HsIdent "allof"))) 
                                          (HsParen (HsLambda (SrcLoc 
                                          {srcFilename = "dummy", srcLine = -1,
                                          srcColumn = -1}) [HsPVar 
                                          (cvrtAxiomBndr a)] 
                                          (cvrtWithQuant (AxForall axbList) 
                                                                         f)))
cvrtWithQuant (AxExists []) f =  cvrtWithoutQuant f
cvrtWithQuant (AxExists (a:axbList)) f = HsApp (HsVar (UnQual 
                                          (HsIdent "ex"))) 
                                          (HsParen (HsLambda (SrcLoc 
                                          {srcFilename = "dummy", srcLine = -1,
                                          srcColumn = -1}) [HsPVar 
                                          (cvrtAxiomBndr a)] 
                                          (cvrtWithQuant (AxForall axbList) 
                                                                         f)))
cvrtWithQuant (AxExistsOne []) f =  cvrtWithoutQuant f
cvrtWithQuant (AxExistsOne (a:axbList)) f = HsApp (HsVar (UnQual 
                                            (HsIdent "exone"))) 
                                            (HsParen (HsLambda (SrcLoc 
                                            {srcFilename = "dummy", srcLine
                                            = -1, srcColumn = -1}) [HsPVar 
                                            (cvrtAxiomBndr a)] 
                                            (cvrtWithQuant (AxForall axbList) 
                                                                         f)))

cvrtWithoutQuant :: Formula -> HsExp
cvrtWithoutQuant (AxExp expr) = expr
cvrtWithoutQuant (AxEq form expr _) = HsInfixApp 
                                       (cvrtWithoutQuant form) 
                                       (HsQConOp (UnQual (HsSymbol "==="))) expr


cvrtAxiomBndr :: AxiomBndr -> HsName
cvrtAxiomBndr (AxiomBndr name) = name
cvrtAxiomBndr (AxiomBndrSig name _) = name

cvrtAxiomName :: AxiomName -> HsPat
cvrtAxiomName (n:ame) = HsPVar (HsIdent ((toLower n):ame))
