{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 AHsPretty

        Description:            Pretty printer for the Annotated Haskell syntax 
                                - based on HsPretty.hs.

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module Haskell.Hatchet.AHsPretty (render, -- reexport
		ppAHsModule,ppAHsModuleHeader,
		ppAHsDecl,
		ppAHsQualType, ppAHsType,
		ppAHsExp,
                ppMatch,
                ppAHsStmt,
                ppAHsPat,
                ppAHsAlt,
		ppAHsName,
                ppGAlt,
                ppAHsGuardedRhs) where

import Haskell.Hatchet.AnnotatedHsSyn
import Haskell.Hatchet.Docs

-------------------------  Pretty-Print a Module --------------------
ppAHsModule :: AHsModule -> Doc
ppAHsModule (AHsModule mod mbExports imp decls) = 
   topLevel (ppAHsModuleHeader mod mbExports)
            (map ppAHsImportDecl imp ++ map ppAHsDecl decls)

--------------------------  Module Header ------------------------------
ppAHsModuleHeader :: AModule -> Maybe [AHsExportSpec] ->  Doc
ppAHsModuleHeader (AModule modName) mbExportList = mySep [
		 text "module",
		 text modName,
		 maybePP (parenList . map ppAHsExportSpec) mbExportList,
		 text "where"]

ppAHsExportSpec :: AHsExportSpec -> Doc
ppAHsExportSpec (AHsEVar name)                     = ppAHsNameParen name
ppAHsExportSpec (AHsEAbs name)                     = ppAHsName name 
ppAHsExportSpec (AHsEThingAll name)                = ppAHsName name <> text"(..)"
ppAHsExportSpec (AHsEThingWith name nameList)      = ppAHsName name <>
                                                   (parenList . map ppAHsNameParen $ nameList)
ppAHsExportSpec (AHsEModuleContents (AModule name)) = text "module" <+> text name 

ppAHsImportDecl (AHsImportDecl pos (AModule mod) bool mbName mbSpecs) = 
	   mySep [text "import", 
		 if bool then text "qualified" else empty,
		 text mod, 
		 maybePP (\(AModule n) -> text "as" <+> text n) mbName,
		 maybePP exports mbSpecs]
           where
	   exports (b,specList) 
	    | b = text "hiding" <+> (parenList . map ppAHsImportSpec $ specList)
	    | otherwise = parenList . map ppAHsImportSpec $  specList

ppAHsImportSpec :: AHsImportSpec -> Doc
ppAHsImportSpec (AHsIVar name)                     = ppAHsNameParen name
ppAHsImportSpec (AHsIAbs name)                     = ppAHsName name 
ppAHsImportSpec (AHsIThingAll name)                = ppAHsName name <> text"(..)"
ppAHsImportSpec (AHsIThingWith name nameList)      = ppAHsName name <>
                                                   (parenList . map ppAHsNameParen $ nameList)

-------------------------  Declarations ------------------------------
ppAHsDecl :: AHsDecl -> Doc
ppAHsDecl (AHsTypeDecl loc name nameList htype) = 
	   blankline $
	   mySep ( [text "type",ppAHsName name] 
		   ++ map ppAHsName nameList
		   ++ [equals, ppAHsType htype])

ppAHsDecl (AHsDataDecl loc context name nameList constrList derives) = 
	   blankline $
           mySep ([text "data", ppAHsContext context, ppAHsName name] 
                  ++ map ppAHsName nameList)
                  <+> (myVcat (zipWith (<+>) (equals : repeat (char '|'))
                                           (map ppAHsConstr constrList))
                       $$$ ppAHsDeriving derives)

ppAHsDecl (AHsNewTypeDecl pos context name nameList constr derives) =
	   blankline $
           mySep ([text "newtype", ppAHsContext context, ppAHsName name]
                  ++ map ppAHsName nameList)
                  <+> equals <+> (ppAHsConstr constr
                                  $$$ ppAHsDeriving derives)
--m{spacing=False}
-- special case for empty class declaration
ppAHsDecl (AHsClassDecl pos qualType []) =
	   blankline $
	   mySep [text "class", ppAHsQualType qualType]
ppAHsDecl (AHsClassDecl pos qualType declList) =
	   blankline $
	   mySep [text "class", ppAHsQualType qualType, text "where"]
	   $$$ body classIndent (map ppAHsDecl declList)  

-- m{spacing=False}
-- special case for empty instance declaration
ppAHsDecl (AHsInstDecl pos qualType []) = 
	   blankline $
	   mySep [text "instance", ppAHsQualType qualType]
ppAHsDecl (AHsInstDecl pos qualType declList) = 
	   blankline $
	   mySep [text "instance", ppAHsQualType qualType, text "where"]
	   $$$ body classIndent (map ppAHsDecl declList)
		   
ppAHsDecl (AHsDefaultDecl pos htype) = 
	   blankline $ 
	   text "default" <+> ppAHsType htype
 
ppAHsDecl (AHsTypeSig pos nameList qualType) = 
	 blankline $ 
	 mySep ((punctuate comma . map ppAHsNameParen $ nameList)
	       ++ [text "::", ppAHsQualType qualType])

{-
ppAHsDecl (AHsFunBind pos matches) 
   = foldr ($$$) empty (map ppMatch matches)
-}
ppAHsDecl (AHsFunBind matches) 
   = foldr ($$$) empty (map ppMatch matches)

ppAHsDecl (AHsPatBind pos pat rhs whereDecls)
   = myFsep [ppAHsPatOrOp pat, ppAHsRhs rhs] $$$ ppWhere whereDecls
    where
	-- special case for single operators
	ppAHsPatOrOp (AHsPVar n) = ppAHsNameParen n
	ppAHsPatOrOp p = ppAHsPat p

ppAHsDecl (AHsInfixDecl pos assoc prec nameList) =
	   blankline $ 
	   mySep ([ppAssoc assoc, int prec]	
	     ++ (punctuate comma . map ppAHsNameInfix $ nameList))
	    where
	    ppAssoc AHsAssocNone  = text "infix"
	    ppAssoc AHsAssocLeft  = text "infixl"
	    ppAssoc AHsAssocRight = text "infixr"

ppMatch (AHsMatch pos f ps rhs whereDecls)
   =   myFsep (ppAHsNameParen f : map ppAHsPat ps ++ [ppAHsRhs rhs])
   $$$ ppWhere whereDecls

ppWhere [] = empty
ppWhere l = nest 2 (text "where" $$$ body whereIndent (map ppAHsDecl l))
        
------------------------- Data & Newtype Bodies -------------------------
ppAHsConstr :: AHsConDecl -> Doc
ppAHsConstr (AHsRecDecl pos name fieldList) =
	 ppAHsName name
	 <> (braceList . map ppField $ fieldList)
ppAHsConstr (AHsConDecl pos name typeList)
     | isSymbolName name && length typeList == 2 =
	 let [l, r] = typeList in
	 myFsep [ppAHsBangType l, ppAHsName name, ppAHsBangType r]
     | otherwise =
	 mySep $ (ppAHsName name) : 
		 map ppAHsBangType typeList

ppField :: ([AHsName],AHsBangType) -> Doc
ppField (names, ty) = myFsepSimple $  (punctuate comma . map ppAHsName $ names) ++
			      [text "::", ppAHsBangType ty]
	
ppAHsBangType :: AHsBangType -> Doc
ppAHsBangType (AHsBangedTy ty) = char '!' <> ppAHsTypeArg ty
ppAHsBangType (AHsUnBangedTy ty) = ppAHsTypeArg ty

ppAHsDeriving :: [AHsName] -> Doc
ppAHsDeriving []  = empty
ppAHsDeriving [d] = text "deriving" <+> ppAHsName d
ppAHsDeriving ds  = text "deriving" <+> parenList (map ppAHsName ds)

------------------------- Types -------------------------
ppAHsQualType :: AHsQualType -> Doc
ppAHsQualType (AHsQualType context htype) = -- if it's AHsQualType, context is never empty
	     myFsep [ ppAHsContext context, text "=>", ppAHsType htype]
ppAHsQualType (AHsUnQualType htype) = ppAHsType htype

ppAHsType :: AHsType -> Doc
ppAHsType = ppAHsTypePrec 0

ppAHsTypeArg :: AHsType -> Doc
ppAHsTypeArg = ppAHsTypePrec 2

-- precedences:
-- 0: top level
-- 1: left argument of ->
-- 2: argument of constructor

ppAHsTypePrec :: Int -> AHsType -> Doc
ppAHsTypePrec p (AHsTyFun a b) =
	parensIf (p > 0) $
		myFsep [ppAHsTypePrec 1 a, text "->", ppAHsType b]
ppAHsTypePrec p (AHsTyTuple l) = parenList . map ppAHsType $ l
-- special case
ppAHsTypePrec p (AHsTyApp (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "[]"))) b ) =
	brackets $ ppAHsType b
ppAHsTypePrec p (AHsTyApp a b) =
	parensIf (p > 1) $ myFsep[ppAHsType a, ppAHsTypeArg b]
ppAHsTypePrec p (AHsTyVar name) = ppAHsName name
-- special case
-- ppAHsTypePrec p (AHsTyCon (AQual (AModule "Prelude") n)) = ppAHsNameParen n
ppAHsTypePrec p (AHsTyCon name) = ppAHsName name

------------------------- Expressions -------------------------
ppAHsRhs :: AHsRhs -> Doc
ppAHsRhs (AHsUnGuardedRhs exp) = equals <+> ppAHsExp exp
ppAHsRhs (AHsGuardedRhss guardList) = 
	myVcat . map ppAHsGuardedRhs $ guardList

ppAHsGuardedRhs :: AHsGuardedRhs -> Doc
ppAHsGuardedRhs (AHsGuardedRhs pos guard body) = 
	       myFsep [ char '|',
		      ppAHsExp guard,
		      equals,
		      ppAHsExp body]

ppAHsLit :: AHsLiteral -> Doc
ppAHsLit	(AHsInt i)      = integer i
ppAHsLit	(AHsChar c)     = text (show c)
ppAHsLit	(AHsString s)   = text (show s)
ppAHsLit	(AHsFrac r)     = double (fromRational r)
-- GHC unboxed literals:
ppAHsLit (AHsCharPrim c)   = text (show c)           <> char '#'
ppAHsLit (AHsStringPrim s) = text (show s)           <> char '#'
ppAHsLit (AHsIntPrim i)    = integer i               <> char '#'
ppAHsLit (AHsFloatPrim r)  = float  (fromRational r) <> char '#'
ppAHsLit (AHsDoublePrim r) = double (fromRational r) <> text "##"
-- GHC extension:
ppAHsLit (AHsLitLit s)     = text "``" <> text s <> text "''"

ppAHsExp :: AHsExp -> Doc
ppAHsExp (AHsLit l) = ppAHsLit l
-- lambda stuff (XXX get rid of parens for final version)
ppAHsExp (AHsInfixApp a op b) = parens $ myFsep[ppAHsExp a, ppInfix op, ppAHsExp b]
	where 
	ppInfix (AHsVar n) = ppAHsNameInfix n
	ppInfix (AHsCon n) = ppAHsNameInfix n
	ppInfix n = error "illegal infix expression"
ppAHsExp (AHsNegApp e) = myFsep [char '-', ppAHsExp e]
ppAHsExp (AHsApp a b) = myFsep [ppAHsExp a, ppAHsExp b]
-- ppAHsExp (AHsLambda expList body) = myFsep $ 
ppAHsExp (AHsLambda _srcLoc expList body) = myFsep $              -- srcLoc added by Bernie
	(((char '\\' ):) . map ppAHsPat $ expList)
	++ [text "->", ppAHsExp body]
-- keywords
ppAHsExp (AHsLet expList letBody) =
	myFsep [text "let" <+> body letIndent (map ppAHsDecl expList),
		text "in", ppAHsExp letBody]
ppAHsExp (AHsIf cond thenexp elsexp) = 
	myFsep [text "if", ppAHsExp cond,
	      text "then", ppAHsExp thenexp,
	      text "else", ppAHsExp elsexp]
ppAHsExp (AHsCase cond altList) = myFsep[text "case", ppAHsExp cond, text "of"]
			        $$$ body caseIndent (map ppAHsAlt altList)
ppAHsExp (AHsDo stmtList) = text "do" $$$ body doIndent (map ppAHsStmt stmtList)
-- Constructors & Vars
ppAHsExp (AHsVar name) = ppAHsNameParen name
ppAHsExp (AHsCon name) = ppAHsNameParen name
ppAHsExp (AHsTuple expList) = parenList . map ppAHsExp $ expList
-- weird stuff
ppAHsExp (AHsParen exp) = parens . ppAHsExp $ exp
ppAHsExp (AHsLeftSection (AHsVar name) exp) =
	parens (ppAHsExp exp <+> ppAHsNameInfix name)
ppAHsExp (AHsLeftSection (AHsCon name) exp) =
	parens (ppAHsExp exp <+> ppAHsNameInfix name)
ppAHsExp (AHsLeftSection _ _) = error "illegal left section"
ppAHsExp (AHsRightSection exp (AHsVar name)) =
	parens (ppAHsNameInfix name <+> ppAHsExp exp)
ppAHsExp (AHsRightSection exp (AHsCon name)) =
	parens (ppAHsNameInfix name <+> ppAHsExp exp)
ppAHsExp (AHsRightSection _ _) = error "illegal right section"
ppAHsExp (AHsRecConstr c fieldList) = 
	ppAHsName c
        <> (braceList . map ppAHsFieldUpdate  $ fieldList)
ppAHsExp (AHsRecUpdate exp fieldList) = 
	ppAHsExp exp
        <> (braceList . map ppAHsFieldUpdate  $ fieldList)
-- patterns
-- special case that would otherwise be buggy
ppAHsExp (AHsAsPat name (AHsIrrPat exp)) =
	myFsep[ppAHsName name <> char '@', char '~' <> ppAHsExp exp]
ppAHsExp (AHsAsPat name exp) = hcat[ppAHsName name,char '@',ppAHsExp exp]
ppAHsExp AHsWildCard = char '_'
ppAHsExp (AHsIrrPat exp) = char '~' <> ppAHsExp exp
-- Lists
ppAHsExp (AHsList list) = 
	bracketList . punctuate comma . map ppAHsExp $ list
ppAHsExp (AHsEnumFrom exp) =
	bracketList [ppAHsExp exp,text ".."]
ppAHsExp (AHsEnumFromTo from to) =
	bracketList [ppAHsExp from, text "..", ppAHsExp to]
ppAHsExp (AHsEnumFromThen from thenE) = 
	bracketList [ppAHsExp from <> comma, ppAHsExp thenE]
ppAHsExp (AHsEnumFromThenTo from thenE to) = 
	bracketList [ppAHsExp from <> comma, ppAHsExp thenE,
			text "..", ppAHsExp to]
ppAHsExp (AHsListComp exp stmtList) = 
	bracketList ([ppAHsExp exp, char '|']
		++ (punctuate comma . map ppAHsStmt $ stmtList))
ppAHsExp (AHsExpTypeSig pos exp ty) = 
	myFsep[ppAHsExp exp, text "::", ppAHsQualType ty]

------------------------- Patterns -----------------------------

ppAHsPat :: AHsPat -> Doc
ppAHsPat (AHsPVar name) = ppAHsNameParen name
ppAHsPat (AHsPLit lit) = ppAHsLit lit
ppAHsPat (AHsPNeg p) = myFsep [char '-', ppAHsPat p]
ppAHsPat (AHsPInfixApp a op b) = myFsep[ppAHsPat a, ppAHsNameInfix op, ppAHsPat b]
ppAHsPat (AHsPApp n ps) = myFsep (ppAHsName n : map ppAHsPat ps)
ppAHsPat (AHsPTuple ps) = parenList . map ppAHsPat $ ps
ppAHsPat (AHsPList ps) = bracketList . punctuate comma . map ppAHsPat $ ps
ppAHsPat (AHsPParen p) = parens . ppAHsPat $ p
ppAHsPat (AHsPRec c fields) 
    =  ppAHsName c 
    <> (braceList . map ppAHsPatField $ fields)
-- special case that would otherwise be buggy
ppAHsPat (AHsPAsPat name (AHsPIrrPat pat)) =
	myFsep[ppAHsName name <> char '@', char '~' <> ppAHsPat pat]
ppAHsPat	(AHsPAsPat name pat) = hcat[ppAHsName name,char '@',ppAHsPat pat]
ppAHsPat	AHsPWildCard = char '_'
ppAHsPat	(AHsPIrrPat pat) = char '~' <> ppAHsPat pat

ppAHsPatField (AHsPFieldPat name pat) = myFsep[ppAHsName name, equals, ppAHsPat pat]
  
------------------------- Case bodies  -------------------------
ppAHsAlt :: AHsAlt -> Doc
ppAHsAlt (AHsAlt pos exp gAlts decls) = 	
	ppAHsPat exp <+> ppGAlts gAlts $$$ ppWhere decls

ppGAlts :: AHsGuardedAlts -> Doc
ppGAlts (AHsUnGuardedAlt exp) = text "->" <+> ppAHsExp exp
ppGAlts (AHsGuardedAlts altList) = myVcat . map ppGAlt $ altList

ppGAlt (AHsGuardedAlt pos exp body) = 
	 myFsep [char '|', ppAHsExp exp, text "->", ppAHsExp body]

------------------------- Statements in monads & list comprehensions -----
ppAHsStmt :: AHsStmt -> Doc
ppAHsStmt (AHsGenerator _sloc exp from) =                    -- sloc added by Bernie
	 ppAHsPat exp <+> text "<-" <+> ppAHsExp from
ppAHsStmt (AHsQualifier exp) = ppAHsExp exp
ppAHsStmt (AHsLetStmt declList) = text "let" 
				$$$ body letIndent (map ppAHsDecl declList)

------------------------- Record updates
ppAHsFieldUpdate :: AHsFieldUpdate -> Doc
ppAHsFieldUpdate (AHsFieldUpdate name exp) = 
		  myFsep[ppAHsName name,equals,ppAHsExp exp]

------------------------- Names -------------------------
ppAHsName :: AHsName -> Doc
ppAHsName (AUnQual i) = ppAHsIdentifier i
ppAHsName (AQual m@(AModule mod) i) 
   = text mod <> char '.' <> ppAHsIdentifier i 

ppAHsNameParen :: AHsName -> Doc
ppAHsNameParen name = parensIf (isSymbolName name) (ppAHsName name)

ppAHsNameInfix :: AHsName -> Doc
ppAHsNameInfix name
	| isSymbolName name = ppAHsName name
	| otherwise = char '`' <> ppAHsName name <> char '`'

{-
ppAHsName :: AHsName -> Doc
ppAHsName name = text (show name)
-}

ppAHsIdentifier :: AHsIdentifier -> Doc
ppAHsIdentifier i = text (show i)

{-
ppAHsNameParen :: AHsName -> Doc
ppAHsNameParen name = parensIf (isSymbolName name) (ppAHsName name)


ppAHsNameInfix :: AHsName -> Doc
ppAHsNameInfix name
	| isSymbolName name = ppAHsName name
	| otherwise = char '`' <> ppAHsName name <> char '`'
-}

isSymbolName :: AHsName -> Bool
isSymbolName (AQual _ i)
   = case i of 
        AHsSymbol _ -> True
        _           -> False
isSymbolName (AUnQual i)
   = case i of 
        AHsSymbol _ -> True
        _           -> False
{-
isSymbolName (AQual _ (AHsSymbol _)) = True
isSymbolName _ = False
-}

{-
isSpecialName :: AHsName -> Bool
isSpecialName (AHsSpecial _) = True
isSpecialName _ = False
-}

isSpecialName :: AHsName -> Bool
isSpecialName (AQual _ i)
   = case i of 
        AHsSpecial _ -> True
        _            -> False
isSpecialName (AUnQual i)
   = case i of
        AHsSpecial _ -> True
        _            -> False

-- was getName 
getAHsIdentifier :: AHsName -> AHsIdentifier
getAHsIdentifier (AUnQual i) = i
getAHsIdentifier  (AQual _ i) = i

ppAHsContext :: AHsContext -> Doc
ppAHsContext []      = empty
ppAHsContext context = parenList (map ppAHsAsst context)

-- hacked for multi-parameter type classes

ppAHsAsst :: AHsAsst -> Doc
-- ppAHsAsst (a,ts) = myFsep(ppAHsName a : map ppAHsTypeArg ts)
ppAHsAsst (a,b) = myFsep [ppAHsName a, ppAHsName b]
