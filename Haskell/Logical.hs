module Haskell.Logical where

import Char
import Haskell.Language.Syntax

not_implemented :: a
not_implemented = error "not implemented"

data Logical = T | F deriving Show

infix 2 \/
infix 3 /\
infix 1 ==>
infix 1 <=> 
(\/), (/\), (==>), (<=>) :: Logical -> Logical -> Logical
not :: Logical -> Logical

-- unfortunately, already not :: Bool -> Bool
(/\) = not_implemented
(\/) = not_implemented
(==>) = not_implemented
(<=>) = not_implemented
not = not_implemented

infix 4 ===
(===) :: a->a->Logical
(===) = not_implemented

-- for any f which is declared but not defined,
-- f = not_implemented should be addded automatically
-- This allows for loose specifications

allof, ex, exone :: (a->Logical) -> Logical
allof = not_implemented
ex = not_implemented
exone = not_implemented

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


{- 

Syntax of AXIOM pragmas: 

{ -# AXIOMS "map_law" forall f g xs. map f (map g xs) = map (f.g) xs;

       "deMorgan"      forall p q. not p /\ not q <=> not (p\/q) #- }

deMorgan = allof(\p -> allof(\q -> not p /\ not q <=> not (p\/q)))




-- This is syntactical sugar for 

map_law = allof(\f-> allof(\g -> map (g.f) === map g . map f))
deMorgan = allof(\p -> allof(\q -> not p /\ not q <=> not (p\/q)))

-}