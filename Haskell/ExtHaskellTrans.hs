module Haskell.ExtHaskellTrans where

import Char
import Haskell.Language.Syntax

transform :: HsModule -> HsModule
transform (HsModule src m expr imp rest) = HsModule src m expr ((HsImportDecl 
     (SrcLoc {srcFilename = "dummy", srcLine = (-1), srcColumn = (-1)})
     (Module "Haskell.Logical") False Nothing Nothing):imp) 
     (convertHsDeclList rest)

convertHsDeclList :: [HsDecl] -> [HsDecl]
convertHsDeclList [] = []
convertHsDeclList (x:xs) = case x of
                             HsAxiomBind b -> 
                               x:convertBinding b ++ convertHsDeclList xs
                             _ -> x:convertHsDeclList xs

convertBinding :: Binding -> [HsDecl]
convertBinding (AxiomDecl name formula) = 
                 [HsPatBind (SrcLoc {srcFilename = "dummy", srcLine = -1, 
                 srcColumn = -1}) (convertAxiomName name) 
                 (convertFormula formula) []]
convertBinding (AndBindings b1 b2) = convertBinding b1 ++ convertBinding b2

convertFormula :: Formula -> HsRhs
convertFormula f = case f of
                    AxQuant quant form -> HsUnGuardedRhs (convWithQuant 
                                                             quant form)
                    _ -> HsUnGuardedRhs (convWithoutQuant f)

convWithQuant :: Quantifier -> Formula -> HsExp
convWithQuant (AxForall []) f =  convWithoutQuant f
convWithQuant (AxForall (a:axbList)) f = HsApp (HsVar (UnQual 
                                          (HsIdent "allof"))) 
                                          (HsParen (HsLambda (SrcLoc 
                                          {srcFilename = "dummy", srcLine = -1,
                                          srcColumn = -1}) [HsPVar 
                                          (convertAxiomBndr a)] 
                                          (convWithQuant (AxForall axbList) 
                                                                         f)))
convWithQuant (AxExists []) f =  convWithoutQuant f
convWithQuant (AxExists (a:axbList)) f = HsApp (HsVar (UnQual 
                                          (HsIdent "ex"))) 
                                          (HsParen (HsLambda (SrcLoc 
                                          {srcFilename = "dummy", srcLine = -1,
                                          srcColumn = -1}) [HsPVar 
                                          (convertAxiomBndr a)] 
                                          (convWithQuant (AxForall axbList) 
                                                                         f)))
convWithQuant (AxExistsOne []) f =  convWithoutQuant f
convWithQuant (AxExistsOne (a:axbList)) f = HsApp (HsVar (UnQual 
                                            (HsIdent "exone"))) 
                                            (HsParen (HsLambda (SrcLoc 
                                            {srcFilename = "dummy", srcLine
                                            = -1, srcColumn = -1}) [HsPVar 
                                            (convertAxiomBndr a)] 
                                            (convWithQuant (AxForall axbList) 
                                                                         f)))

convWithoutQuant :: Formula -> HsExp
convWithoutQuant (AxExp expr) = expr
convWithoutQuant (AxEq form expr _) = HsInfixApp 
                                       (convWithoutQuant form) 
                                       (HsQConOp (UnQual (HsSymbol "==="))) expr


convertAxiomBndr :: AxiomBndr -> HsName
convertAxiomBndr (AxiomBndr name) = name
convertAxiomBndr (AxiomBndrSig name _) = name

convertAxiomName :: AxiomName -> HsPat
convertAxiomName (n:ame) = HsPVar (HsIdent ((toLower n):ame))

convertTry :: HsName -> Bool
convertTry n 
    | (n == HsIdent "bla") = True
