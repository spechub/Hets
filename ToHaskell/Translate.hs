module ToHaskell.Translate where

import HasCASL.As
import Haskell.Language.Syntax
import Common.AS_Annotation
import Common.Id
import Common.Lib.Parsec.Pos
import Char


translate :: BasicSpec -> HsModule
-- From where can I get the Module's name?
--translate x = error (show x)
translate (BasicSpec annotedBasicItems) = 
          HsModule (SrcLoc "" 1 1) (Module "HasCASLModul") Nothing [] 
                   (translateBasicItems annotedBasicItems)

-------------------------------------------------------------
translateBasicItems :: [Annoted BasicItem] -> [HsDecl]
translateBasicItems ilist = concat $ map translateBasicItem ilist
--translateBasicItems [] = []
--translateBasicItems (bi:bis) = 
--          ((translateBasicItem (item bi))++(translateBasicItems bis))

translateBasicItem :: Annoted BasicItem -> [HsDecl]
translateBasicItem i = 
  case (item i) of
    SigItems si -> translateSigItems si
    ProgItems eqList _posList -> translateProgEqs eqList
    _ -> error ("translateBasicItem: " ++ show i)

-------------------------------------------------------------
translateSigItems :: SigItems -> [HsDecl]
translateSigItems (TypeItems _inst _annotedTypeItems _poslist) = []
translateSigItems _ = []
  
-------------------------------------------------------------
translateProgEqs :: [Annoted ProgEq] -> [HsDecl]
translateProgEqs eqs = map translateProgEq eqs


translateProgEq :: Annoted ProgEq -> HsDecl
translateProgEq (Annoted (ProgEq pat term pos) _ _ _) = 
  case pat of
    PatternToken _ptok -> case term of
                           TermToken _ttok -> patBind pat term pos
			   _ -> error ("translateProgEq " ++ show term)
    MixfixPattern (p:_ps) -> case p of
                              PatternToken ptok -> 
                              -- erstes PatternToken klein deutet auf HsFunBind
                                 if isLower $ head $ tokStr ptok then
                                   funBind pat term pos
		                 else patBind pat term pos
			      _ -> error ("unexpected pattern in " ++
                                          "translateProgEq: " ++ show pat)
    _ -> error ("translateProgEq" ++ show pat)

-------------------------------------------------------------
patBind :: Pattern -> Term -> Pos -> HsDecl
-- x = y
patBind (PatternToken ptok) (TermToken ttok) pos = 
  HsPatBind (SrcLoc {srcFilename = sourceName pos, srcLine = sourceLine pos, 
                     srcColumn = sourceColumn pos}) 
            (HsPVar (HsIdent (tokStr ptok))) 
            (HsUnGuardedRhs (HsVar (UnQual (HsIdent (tokStr ttok))))) 
            []
--
--patBind (MixfixPattern (p:ps)) term pos = error "not yet implemented"
patBind _ _ _ = error "not yet implemented"


-------------------------------------------------------------
funBind :: Pattern -> Term -> Pos -> HsDecl
-- f a b ...  = y
funBind (MixfixPattern (p:ps)) term pos = 
  case p of 
    PatternToken ptok -> 
      HsFunBind [HsMatch (SrcLoc {srcFilename = "", srcLine = sourceLine pos,
                                  srcColumn = sourceColumn pos})
                         (HsIdent (tokStr ptok))
	                 (hsPats ps)
	                 (hsRhs term)
                         []
                ]
    _ -> error ("unexpected pattern: " ++ show p)
funBind _ _ _ = HsFunBind []

-------------------------------------------------------------
hsPats :: [Pattern] -> [HsPat]
hsPats pats = map hsPat pats

hsPat :: Pattern -> HsPat
hsPat p = case p of 
	    PatternToken ptok ->
              if isLower $ head $ tokStr ptok then
		HsPVar (HsIdent (tokStr ptok))
	      else 
	        if isUpper $ head $ tokStr ptok then
                  HsPApp (UnQual (HsIdent (tokStr ptok))) []
		else
		  if and $ map isDigit (tokStr ptok) then
		    HsPLit (HsInt ((read (tokStr ptok))::Integer))
		  -- andere Typen wie z.B. Rational fehlen
		  else error ("unexpected pattern: " ++ show p)
	    _ -> error ("unexpected pattern: " ++ show p)
--BracketPattern fehlen!!

-------------------------------------------------------------
hsRhs :: Term -> HsRhs
hsRhs term = case term of
    TermToken ttok -> if isLower $ head $ tokStr ttok then
		        HsUnGuardedRhs (HsVar (UnQual 
                          (HsIdent (tokStr ttok))))
		      else 
                        if isUpper $ head $ tokStr ttok then
                          HsUnGuardedRhs (HsCon (UnQual 
                            (HsIdent (tokStr ttok))))
			else
			  if and $ map isDigit (tokStr ttok) then
			    HsUnGuardedRhs (HsLit (
                              HsInt ((read (tokStr ttok))::Integer)))
			  else error ("Unexpected term: " ++ show ttok)
    MixfixTerm tlist -> HsUnGuardedRhs (hsExps tlist (length tlist))
    _ -> error "hsRhs is not yet implemented"

-------------------------------------------------------------
hsExps :: [Term] -> Int -> HsExp
hsExps (t:ts) l = case t of
  TermToken ttok -> if l == 1 then
		      if isLower $ head $ tokStr ttok then
			HsVar (UnQual ((HsIdent (tokStr ttok))))
		      else 
		        if isUpper $ head $ tokStr ttok then
			  HsCon (UnQual (HsIdent (tokStr ttok)))
			else
			  if and $ map isDigit (tokStr ttok) then
			    HsLit (HsInt ((read (tokStr ttok))::Integer))
			  -- andere Typen wie z.B. Rational fehlen
			  -- Operationsanwendungen fehlen
			  else error ("Unexpected term: " ++ show ttok)
		    else HsApp (hsExps (t:[]) 1) (hsExps ts (l-1))
  _ -> error "hsExps is not yet implemented"
hsExps [] _ = error "Missing term"
--BracketTerm fehlt!!
		    
