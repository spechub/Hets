module ToHaskell.Translate where

import HasCASL.As
import Haskell.Language.Syntax
import Common.AS_Annotation
import Common.Id
import Common.Lib.Parsec.Pos


translate :: BasicSpec -> HsModule
-- From where can I get the Module's name?
translate (BasicSpec []) = 
          HsModule (SrcLoc "NewModul.hs" 1 1) (Module "NewModul") Nothing [] []
translate (BasicSpec annotedBasicItems) = 
          HsModule (SrcLoc "NewModul.hs" 1 1) (Module "NewModul") Nothing [] 
                   (translateBasicItems annotedBasicItems)



translateBasicItems :: [Annoted BasicItem] -> [HsDecl]
translateBasicItems [] = []
translateBasicItems (bi:bis) = 
          ((translateBasicItem (item bi))++(translateBasicItems bis))

translateBasicItem :: BasicItem -> [HsDecl]
translateBasicItem item = 
  case item of
    ProgItems eqList posList -> translateProgEqs eqList
    _ -> error "not yet implemented"




translateProgEqs :: [Annoted ProgEq] -> [HsDecl]
translateProgEqs [] = []
translateProgEqs (eq:eqs) = 
         ((translateProgEq (item eq)):(translateProgEqs eqs))

translateProgEq :: ProgEq -> HsDecl
translateProgEq (ProgEq pat term pos) = 
  case pat of
    MixfixPattern p -> if length p == 1 
                          then patBind pat term pos
		          else funBind pat term pos
    _ -> error "not yet implemented"




patBind :: Pattern -> Term -> Pos -> HsDecl
patBind (MixfixPattern [PatternToken tok]) term pos =
  HsPatBind (SrcLoc {srcFilename = sourceName pos, srcLine = sourceLine pos, srcColumn = sourceColumn pos})
      (HsPVar (HsSymbol (tokStr tok))) (translatePatBindTerm term) []
       -- muss die HsPVar hier symbol oder id sein?


translatePatBindTerm :: Term -> HsRhs
translatePatBindTerm term = 
  case term of
    TermToken tok -> HsUnGuardedRhs (HsVar (UnQual (HsSymbol (tokStr tok))))
    -- ist die HsVar hier qualifiziert oder nicht?
    _ -> error "not yet implemented"



funBind :: Pattern -> Term -> Pos -> HsDecl
funBind pat term pos = HsFunBind []