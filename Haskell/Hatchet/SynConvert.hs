{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 SynConvert

        Description:            Provides functions for converting between the
                                syntax provided by the parser and the annotated 
                                syntax provided by AnnotatedHsSyn.lhs 

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module SynConvert (toAHsModule, 
                   fromAHsModule, 
                   fromAHsDecl) where

import HsSyn          -- everything

import AnnotatedHsSyn -- everything


--------------------------------------------------------------------------------

-- map from HsSyn to AnnotatedHsSyn

toASrcLoc :: SrcLoc -> ASrcLoc
toASrcLoc (SrcLoc i j) = ASrcLoc i j

toAModule :: Module -> AModule
toAModule (Module s) = AModule s

hsNameToAHsIdentifier :: HsName -> AHsIdentifier
hsNameToAHsIdentifier n
   = case n of
        HsIdent s    -> AHsIdent s
        HsSymbol s   -> AHsSymbol s
        HsSpecial s  -> AHsSpecial s

hsQNameToAHsName :: HsQName -> AHsName
hsQNameToAHsName (Qual m n)
{-
   = case n of
        HsIdent s    -> AQual (toAModule m) s 
        HsSymbol s   -> AQual (toAModule m) s 
        HsSpecial s  -> AQual (toAModule m) s 
-}
    = AQual (toAModule m) (hsNameToAHsIdentifier n)

hsQNameToAHsName (UnQual n)
{-
   = case n of
        HsIdent s    -> AUnQual s 
        HsSymbol s   -> AUnQual s 
        HsSpecial s  -> AUnQual s 
-}
   = AUnQual $ hsNameToAHsIdentifier n

toAHsName :: HsName -> AHsName
{-
toAHsName (HsIdent s)   = AUnQual s 
toAHsName (HsSymbol s)  = AUnQual s 
toAHsName (HsSpecial s) = AUnQual s 
-}
toAHsName n = AUnQual $ hsNameToAHsIdentifier n

toAHsModule :: HsModule -> AHsModule
toAHsModule  (HsModule mod Nothing imports decls)
   = AHsModule (toAModule mod) 
               Nothing 
               (map toAHsImportDecl imports) 
               (map (toAHsDecl ) decls)
toAHsModule  (HsModule mod (Just exports) imports decls)
   = AHsModule (toAModule mod) 
               (Just (map toAHsExportSpec exports))
               (map toAHsImportDecl imports) 
               (map (toAHsDecl ) decls)

toAHsExportSpec :: HsExportSpec -> AHsExportSpec
toAHsExportSpec (HsEVar qname) = AHsEVar $ hsQNameToAHsName qname
toAHsExportSpec (HsEAbs qname) = AHsEAbs $ hsQNameToAHsName qname
toAHsExportSpec (HsEThingAll qname) = AHsEThingAll $ hsQNameToAHsName qname
toAHsExportSpec (HsEThingWith n names) = AHsEThingWith (hsQNameToAHsName n) $ map hsQNameToAHsName names
toAHsExportSpec (HsEModuleContents mod) = AHsEModuleContents $ toAModule mod 

toAHsImportDecl :: HsImportDecl -> AHsImportDecl
toAHsImportDecl (HsImportDecl sloc mod1 b mod2 z)
   = AHsImportDecl (toASrcLoc sloc) 
                   (toAModule mod1)
                   b 
                   (case mod2 of
                       Nothing -> Nothing
                       Just m  -> Just (toAModule m)
                   )
                   (case z of
                       Nothing -> Nothing
                       Just (b, importSpecs) -> Just (b, map toAHsImportSpec importSpecs)
                   )

toAHsImportSpec :: HsImportSpec -> AHsImportSpec
toAHsImportSpec (HsIVar name) = AHsIVar $ toAHsName name
toAHsImportSpec (HsIAbs name) = AHsIAbs $ toAHsName name
toAHsImportSpec (HsIThingAll name) = AHsIThingAll $ toAHsName name
toAHsImportSpec (HsIThingWith n names) = AHsIThingWith (toAHsName n) $ map toAHsName names

toAHsAssoc :: HsAssoc -> AHsAssoc
toAHsAssoc HsAssocNone = AHsAssocNone
toAHsAssoc HsAssocLeft = AHsAssocLeft
toAHsAssoc HsAssocRight = AHsAssocRight

toAHsDecl :: HsDecl -> AHsDecl
toAHsDecl  (HsTypeDecl sloc n names t) 
   = AHsTypeDecl (toASrcLoc sloc) 
                 (toAHsName n) 
                 (map toAHsName names)
                 (toAHsType t)
toAHsDecl  (HsDataDecl sloc contxt n vars condecls derives)
   = AHsDataDecl (toASrcLoc sloc)
                 (toAHsContext contxt)
                 (toAHsName n)
                 (map toAHsName vars)
                 (map toAHsConDecl condecls)
                 (map hsQNameToAHsName derives)
toAHsDecl  (HsInfixDecl sloc assoc n names)
   = AHsInfixDecl (toASrcLoc sloc)
                  (toAHsAssoc assoc)
                  n 
                  (map toAHsName names)
toAHsDecl  (HsNewTypeDecl sloc contxt n names condecl derives)
   = AHsNewTypeDecl (toASrcLoc sloc)
                    (toAHsContext contxt)
                    (toAHsName n)
                    (map toAHsName names)
                    (toAHsConDecl condecl)
                    (map hsQNameToAHsName derives)
toAHsDecl  (HsClassDecl sloc qtype decls)
   = AHsClassDecl (toASrcLoc sloc)
                  (toAHsQualType qtype)
                  (map (toAHsDecl ) decls)
toAHsDecl  (HsInstDecl sloc qtype decls)
   = AHsInstDecl (toASrcLoc sloc)
                 (toAHsQualType qtype)
                 (map (toAHsDecl ) decls)
toAHsDecl  (HsDefaultDecl sloc t)
   = AHsDefaultDecl (toASrcLoc sloc)
                    (toAHsType t)
toAHsDecl  (HsTypeSig sloc names qtype)
   = AHsTypeSig (toASrcLoc sloc)
                (map toAHsName names)
                (toAHsQualType qtype)
-- toAHsDecl  (HsFunBind sloc matches)
toAHsDecl  (HsFunBind matches)
--   = AHsFunBind (toASrcLoc sloc)
   = AHsFunBind (map (toAHsMatch ) matches)
toAHsDecl  (HsPatBind sloc pat rhs wheres)
   = AHsPatBind (toASrcLoc sloc)
                (toAHsPat pat)
                (toAHsRhs  rhs)
                (map (toAHsDecl ) wheres)
 
toAHsMatch :: HsMatch -> AHsMatch
toAHsMatch  (HsMatch sloc name pats rhs wheres)
   = AHsMatch (toASrcLoc sloc)
              (hsQNameToAHsName name)
              (map toAHsPat pats)
              (toAHsRhs  rhs)
              (map (toAHsDecl ) wheres)

toAHsConDecl :: HsConDecl -> AHsConDecl
toAHsConDecl (HsConDecl sloc name bangtypes)
   = AHsConDecl (toASrcLoc sloc) 
                (toAHsName name)
                (map toAHsBangType bangtypes)
toAHsConDecl (HsRecDecl sloc name recs)
   = AHsRecDecl (toASrcLoc sloc) 
                (toAHsName name)
                [(map toAHsName ns, toAHsBangType t) | (ns, t) <- recs]

toAHsBangType :: HsBangType -> AHsBangType
toAHsBangType (HsBangedTy t) = AHsBangedTy $ toAHsType t
toAHsBangType (HsUnBangedTy t) = AHsUnBangedTy $ toAHsType t

toAHsRhs :: HsRhs -> AHsRhs
toAHsRhs  (HsUnGuardedRhs e) = AHsUnGuardedRhs $ toAHsExp  e
toAHsRhs  (HsGuardedRhss rhss) = AHsGuardedRhss $ map (toAHsGuardedRhs ) rhss

toAHsGuardedRhs :: HsGuardedRhs -> AHsGuardedRhs
toAHsGuardedRhs  (HsGuardedRhs sloc guard e)
   = AHsGuardedRhs (toASrcLoc sloc)
                   (toAHsExp  guard)
                   (toAHsExp  e)

toAHsQualType :: HsQualType -> AHsQualType
toAHsQualType (HsQualType cntxt t)
   = AHsQualType (toAHsContext cntxt) $ toAHsType t
toAHsQualType (HsUnQualType t)
   = AHsUnQualType $ toAHsType t

toAHsType :: HsType -> AHsType
toAHsType (HsTyFun t1 t2)
   = AHsTyFun (toAHsType t1) (toAHsType t2)
toAHsType (HsTyTuple ts) = AHsTyTuple $ map toAHsType ts
toAHsType (HsTyApp t1 t2) = AHsTyApp (toAHsType t1) (toAHsType t2)
toAHsType (HsTyVar v) = AHsTyVar $ toAHsName v
toAHsType (HsTyCon c) = AHsTyCon $ hsQNameToAHsName c 

toAHsContext :: HsContext -> AHsContext
toAHsContext cntxt = map toAHsAsst cntxt

-- we don't handle multi-param tye classes yet
toAHsAsst :: HsAsst -> AHsAsst
toAHsAsst (qname, [HsTyVar n]) 
   = (hsQNameToAHsName qname, toAHsName n)
toAHsAsst a = error $ "We don't handle this type of class yet :" ++ show a


toAHsLiteral :: HsLiteral -> AHsLiteral
toAHsLiteral (HsInt i) = AHsInt i
toAHsLiteral (HsChar c) = AHsChar c
toAHsLiteral (HsString s) = AHsString s
toAHsLiteral (HsFrac f) = AHsFrac f
toAHsLiteral (HsCharPrim c) = AHsCharPrim c
toAHsLiteral (HsStringPrim s) = AHsStringPrim s
toAHsLiteral (HsIntPrim i) = AHsIntPrim i
toAHsLiteral (HsFloatPrim f) = AHsFloatPrim f
toAHsLiteral (HsDoublePrim d) = AHsDoublePrim d
toAHsLiteral (HsLitLit l) = AHsLitLit l

toAHsExp :: HsExp -> AHsExp
-- toAHsExp  (HsVar name)                  = AHsVar (hsQNameToAHsName name) (Just ())
toAHsExp  (HsVar name)                  = AHsVar $ hsQNameToAHsName name 
toAHsExp  (HsCon name)                  = AHsCon $ hsQNameToAHsName name
toAHsExp  (HsLit lit)                   = AHsLit $ toAHsLiteral lit
toAHsExp  (HsInfixApp e1 e2 e3)         = AHsInfixApp (toAHsExp  e1) (toAHsExp  e2) (toAHsExp  e3)
toAHsExp  (HsApp e1 e2)                 = AHsApp (toAHsExp  e1) (toAHsExp  e2)
toAHsExp  (HsNegApp e)                  = AHsNegApp (toAHsExp  e)
toAHsExp  (HsLambda sloc pats e)        = AHsLambda (toASrcLoc sloc) (map toAHsPat pats) (toAHsExp  e)
toAHsExp  (HsLet decls e)               = AHsLet (map (toAHsDecl ) decls) (toAHsExp  e)
toAHsExp  (HsIf e1 e2 e3)               = AHsIf (toAHsExp  e1) (toAHsExp  e2) (toAHsExp  e3)
toAHsExp  (HsCase e alts)               = AHsCase (toAHsExp  e) (map (toAHsAlt ) alts)
toAHsExp  (HsDo stmts)                  = AHsDo $ map (toAHsStmt ) stmts
toAHsExp  (HsTuple es)                  = AHsTuple $ map (toAHsExp ) es
toAHsExp  (HsList es)                   = AHsList $ map (toAHsExp ) es
toAHsExp  (HsParen e)                   = AHsParen $ toAHsExp  e
toAHsExp  (HsLeftSection e1 e2)         = AHsLeftSection (toAHsExp  e1) (toAHsExp  e2) 
toAHsExp  (HsRightSection e1 e2)        = AHsRightSection (toAHsExp  e1) (toAHsExp  e2) 
toAHsExp  (HsRecConstr name fields)     = AHsRecConstr (hsQNameToAHsName name) (map (toAHsFieldUpdate ) fields) 
toAHsExp  (HsRecUpdate e fields)        = AHsRecUpdate (toAHsExp  e) (map (toAHsFieldUpdate ) fields) 
toAHsExp  (HsEnumFrom e)                = AHsEnumFrom $ toAHsExp  e
toAHsExp  (HsEnumFromTo e1 e2)          = AHsEnumFromTo (toAHsExp  e1) (toAHsExp  e2) 
toAHsExp  (HsEnumFromThen e1 e2)        = AHsEnumFromThen (toAHsExp  e1) (toAHsExp  e2)
toAHsExp  (HsEnumFromThenTo e1 e2 e3)   = AHsEnumFromThenTo (toAHsExp  e1) (toAHsExp  e2) (toAHsExp  e3) 
toAHsExp  (HsListComp e stmts)          = AHsListComp (toAHsExp  e) (map (toAHsStmt ) stmts) 
toAHsExp  (HsExpTypeSig sloc e qtype)   = AHsExpTypeSig (toASrcLoc sloc) (toAHsExp  e) (toAHsQualType qtype) 
toAHsExp  (HsAsPat name e)              = AHsAsPat (toAHsName name) (toAHsExp  e)
toAHsExp  HsWildCard                    = AHsWildCard 
toAHsExp  (HsIrrPat e)                  = AHsIrrPat (toAHsExp  e) 

toAHsPat :: HsPat -> AHsPat 
toAHsPat (HsPVar name)                 = AHsPVar $ toAHsName name
toAHsPat (HsPLit lit)                  = AHsPLit $ toAHsLiteral lit
toAHsPat (HsPNeg pat)                  = AHsPNeg $ toAHsPat pat 
toAHsPat (HsPInfixApp pat1 qname pat2) = AHsPInfixApp (toAHsPat pat1) (hsQNameToAHsName qname) (toAHsPat pat2)
toAHsPat (HsPApp qname pats)           = AHsPApp (hsQNameToAHsName qname) $ map toAHsPat pats 
toAHsPat (HsPTuple pats)               = AHsPTuple $ map toAHsPat pats
toAHsPat (HsPList pats)                = AHsPList $ map toAHsPat pats
toAHsPat (HsPParen pat)                = AHsPParen $ toAHsPat pat 
toAHsPat (HsPRec qname patfields)      = AHsPRec (hsQNameToAHsName qname) $ map toAHsPatField patfields
toAHsPat (HsPAsPat name pat)           = AHsPAsPat (toAHsName name) (toAHsPat pat)
toAHsPat HsPWildCard                   = AHsPWildCard
toAHsPat (HsPIrrPat pat)               = AHsPIrrPat $ toAHsPat pat

toAHsPatField :: HsPatField -> AHsPatField
toAHsPatField (HsPFieldPat qname pat) = AHsPFieldPat (hsQNameToAHsName qname) (toAHsPat pat)

toAHsStmt :: HsStmt -> AHsStmt
toAHsStmt  (HsGenerator sloc pat e) 
   = AHsGenerator (toASrcLoc sloc) 
                  (toAHsPat pat) 
                  (toAHsExp  e)
toAHsStmt  (HsQualifier e) = AHsQualifier (toAHsExp  e)
toAHsStmt  (HsLetStmt decls) = AHsLetStmt $ map (toAHsDecl ) decls

toAHsFieldUpdate :: HsFieldUpdate -> AHsFieldUpdate
toAHsFieldUpdate  (HsFieldUpdate qname e) = AHsFieldUpdate (hsQNameToAHsName qname) (toAHsExp  e)


toAHsAlt :: HsAlt -> AHsAlt
toAHsAlt  (HsAlt sloc pat galts decls)
   = AHsAlt (toASrcLoc sloc)
            (toAHsPat pat)
            (toAHsGuardedAlts  galts)
            (map (toAHsDecl ) decls)

toAHsGuardedAlts :: HsGuardedAlts -> AHsGuardedAlts
toAHsGuardedAlts  (HsUnGuardedAlt e)
   = AHsUnGuardedAlt (toAHsExp  e)
toAHsGuardedAlts  (HsGuardedAlts galts)
   = AHsGuardedAlts $ map (toAHsGuardedAlt ) galts

toAHsGuardedAlt :: HsGuardedAlt -> AHsGuardedAlt
toAHsGuardedAlt  (HsGuardedAlt sloc e1 e2) 
   = AHsGuardedAlt (toASrcLoc sloc) (toAHsExp e1) (toAHsExp e2)

--------------------------------------------------------------------------------

-- map to HsSyn from AnnotatedHsSyn

fromASrcLoc :: ASrcLoc -> SrcLoc
fromASrcLoc (ASrcLoc i j) = SrcLoc i j

fromAModule :: AModule -> Module
fromAModule (AModule s) = Module s

fromAHsIdentifier :: AHsIdentifier -> HsName
fromAHsIdentifier (AHsIdent s) = HsIdent s
fromAHsIdentifier (AHsSpecial s) = HsSpecial s
fromAHsIdentifier (AHsSymbol s) = HsSymbol s

aHsNameToHsQName :: AHsName -> HsQName
aHsNameToHsQName (AQual m i)
   = Qual (fromAModule m) (fromAHsIdentifier i) 

aHsNameToHsQName (AUnQual i)
   = UnQual (fromAHsIdentifier i)            

-- throw away qualifiers if they exist
fromAHsName :: AHsName -> HsName
fromAHsName (AQual m i) = fromAHsIdentifier i 
fromAHsName (AUnQual i) = fromAHsIdentifier i 

fromAHsModule :: AHsModule -> HsModule
fromAHsModule  (AHsModule mod Nothing imports decls)
   = HsModule (fromAModule mod) 
               Nothing 
               (map fromAHsImportDecl imports) 
               (map (fromAHsDecl ) decls)
fromAHsModule  (AHsModule mod (Just exports) imports decls)
   = HsModule  (fromAModule mod) 
               (Just (map fromAHsExportSpec exports))
               (map fromAHsImportDecl imports) 
               (map (fromAHsDecl ) decls)

fromAHsExportSpec :: AHsExportSpec -> HsExportSpec
fromAHsExportSpec (AHsEVar qname) = HsEVar $ aHsNameToHsQName qname
fromAHsExportSpec (AHsEAbs qname) = HsEAbs $ aHsNameToHsQName qname
fromAHsExportSpec (AHsEThingAll qname) = HsEThingAll $ aHsNameToHsQName qname
fromAHsExportSpec (AHsEThingWith n names) = HsEThingWith (aHsNameToHsQName n) $ map aHsNameToHsQName names
fromAHsExportSpec (AHsEModuleContents mod) = HsEModuleContents $ fromAModule mod 

fromAHsImportDecl :: AHsImportDecl -> HsImportDecl
fromAHsImportDecl (AHsImportDecl sloc mod1 b mod2 z)
   = HsImportDecl  (fromASrcLoc sloc) 
                   (fromAModule mod1)
                   b 
                   (case mod2 of
                       Nothing -> Nothing
                       Just m  -> Just (fromAModule m)
                   )
                   (case z of
                       Nothing -> Nothing
                       Just (b, importSpecs) -> Just (b, map fromAHsImportSpec importSpecs)
                   )

fromAHsImportSpec :: AHsImportSpec -> HsImportSpec
fromAHsImportSpec (AHsIVar name) = HsIVar $ fromAHsName name
fromAHsImportSpec (AHsIAbs name) = HsIAbs $ fromAHsName name
fromAHsImportSpec (AHsIThingAll name) = HsIThingAll $ fromAHsName name
fromAHsImportSpec (AHsIThingWith n names) = HsIThingWith (fromAHsName n) $ map fromAHsName names

fromAHsAssoc :: AHsAssoc -> HsAssoc
fromAHsAssoc AHsAssocNone = HsAssocNone
fromAHsAssoc AHsAssocLeft = HsAssocLeft
fromAHsAssoc AHsAssocRight = HsAssocRight

fromAHsDecl :: AHsDecl -> HsDecl
fromAHsDecl  (AHsTypeDecl sloc n names t) 
   = HsTypeDecl (fromASrcLoc sloc) 
                 (fromAHsName n) 
                 (map fromAHsName names)
                 (fromAHsType t)
fromAHsDecl  (AHsDataDecl sloc contxt n vars condecls derives)
   = HsDataDecl (fromASrcLoc sloc)
                 (fromAHsContext contxt)
                 (fromAHsName n)
                 (map fromAHsName vars)
                 (map fromAHsConDecl condecls)
                 (map aHsNameToHsQName derives)
fromAHsDecl  (AHsInfixDecl sloc assoc n names)
   = HsInfixDecl (fromASrcLoc sloc)
                  (fromAHsAssoc assoc)
                  n 
                  (map fromAHsName names)
fromAHsDecl  (AHsNewTypeDecl sloc contxt n names condecl derives)
   = HsNewTypeDecl (fromASrcLoc sloc)
                    (fromAHsContext contxt)
                    (fromAHsName n)
                    (map fromAHsName names)
                    (fromAHsConDecl condecl)
                    (map aHsNameToHsQName derives)
fromAHsDecl  (AHsClassDecl sloc qtype decls)
   = HsClassDecl (fromASrcLoc sloc)
                  (fromAHsQualType qtype)
                  (map (fromAHsDecl ) decls)
fromAHsDecl  (AHsInstDecl sloc qtype decls)
   = HsInstDecl (fromASrcLoc sloc)
                 (fromAHsQualType qtype)
                 (map (fromAHsDecl ) decls)
fromAHsDecl  (AHsDefaultDecl sloc t)
   = HsDefaultDecl (fromASrcLoc sloc)
                    (fromAHsType t)
fromAHsDecl  (AHsTypeSig sloc names qtype)
   = HsTypeSig (fromASrcLoc sloc)
                (map fromAHsName names)
                (fromAHsQualType qtype)
-- fromAHsDecl  (AHsFunBind sloc matches)
fromAHsDecl  (AHsFunBind matches)
--   = HsFunBind (fromASrcLoc sloc)
   = HsFunBind (map (fromAHsMatch ) matches)
fromAHsDecl  (AHsPatBind sloc pat rhs wheres)
   = HsPatBind (fromASrcLoc sloc)
                (fromAHsPat pat)
                (fromAHsRhs  rhs)
                (map (fromAHsDecl ) wheres)
 
fromAHsMatch :: AHsMatch -> HsMatch
fromAHsMatch  (AHsMatch sloc name pats rhs wheres)
   = HsMatch (fromASrcLoc sloc)
              (aHsNameToHsQName name)
              (map fromAHsPat pats)
              (fromAHsRhs  rhs)
              (map (fromAHsDecl ) wheres)

fromAHsConDecl :: AHsConDecl -> HsConDecl
fromAHsConDecl (AHsConDecl sloc name bangtypes)
   = HsConDecl (fromASrcLoc sloc) 
                (fromAHsName name)
                (map fromAHsBangType bangtypes)
fromAHsConDecl (AHsRecDecl sloc name recs)
   = HsRecDecl (fromASrcLoc sloc) 
                (fromAHsName name)
                [(map fromAHsName ns, fromAHsBangType t) | (ns, t) <- recs]

fromAHsBangType :: AHsBangType -> HsBangType
fromAHsBangType (AHsBangedTy t) = HsBangedTy $ fromAHsType t
fromAHsBangType (AHsUnBangedTy t) = HsUnBangedTy $ fromAHsType t

fromAHsRhs :: AHsRhs -> HsRhs
fromAHsRhs  (AHsUnGuardedRhs e) = HsUnGuardedRhs $ fromAHsExp  e
fromAHsRhs  (AHsGuardedRhss rhss) = HsGuardedRhss $ map (fromAHsGuardedRhs ) rhss

fromAHsGuardedRhs :: AHsGuardedRhs -> HsGuardedRhs
fromAHsGuardedRhs  (AHsGuardedRhs sloc guard e)
   = HsGuardedRhs (fromASrcLoc sloc)
                   (fromAHsExp  guard)
                   (fromAHsExp  e)

fromAHsQualType :: AHsQualType -> HsQualType
fromAHsQualType (AHsQualType cntxt t)
   = HsQualType (fromAHsContext cntxt) $ fromAHsType t
fromAHsQualType (AHsUnQualType t)
   = HsUnQualType $ fromAHsType t

fromAHsType :: AHsType -> HsType
fromAHsType (AHsTyFun t1 t2)
   = HsTyFun (fromAHsType t1) (fromAHsType t2)
fromAHsType (AHsTyTuple ts) = HsTyTuple $ map fromAHsType ts
fromAHsType (AHsTyApp t1 t2) = HsTyApp (fromAHsType t1) (fromAHsType t2)
fromAHsType (AHsTyVar v) = HsTyVar $ fromAHsName v
fromAHsType (AHsTyCon c) = HsTyCon $ aHsNameToHsQName c 

fromAHsContext :: AHsContext -> HsContext
fromAHsContext cntxt = map fromAHsAsst cntxt

-- we don't handle multi-param tye classes yet
fromAHsAsst :: AHsAsst -> HsAsst
fromAHsAsst (qname, name) 
   = (aHsNameToHsQName qname, [HsTyVar (fromAHsName name)])


fromAHsLiteral :: AHsLiteral -> HsLiteral
fromAHsLiteral (AHsInt i) = HsInt i
fromAHsLiteral (AHsChar c) = HsChar c
fromAHsLiteral (AHsString s) = HsString s
fromAHsLiteral (AHsFrac f) = HsFrac f
fromAHsLiteral (AHsCharPrim c) = HsCharPrim c
fromAHsLiteral (AHsStringPrim s) = HsStringPrim s
fromAHsLiteral (AHsIntPrim i) = HsIntPrim i
fromAHsLiteral (AHsFloatPrim f) = HsFloatPrim f
fromAHsLiteral (AHsDoublePrim d) = HsDoublePrim d
fromAHsLiteral (AHsLitLit l) = HsLitLit l

fromAHsExp :: AHsExp -> HsExp
-- fromAHsExp  (AHsVar name _annotation)      = HsVar (aHsNameToHsQName name)   -- drop the annotation
fromAHsExp  (AHsVar name)                  = HsVar (aHsNameToHsQName name) 
fromAHsExp  (AHsCon name)                  = HsCon $ aHsNameToHsQName name
fromAHsExp  (AHsLit lit)                   = HsLit $ fromAHsLiteral lit
fromAHsExp  (AHsInfixApp e1 e2 e3)         = HsInfixApp (fromAHsExp  e1) (fromAHsExp  e2) (fromAHsExp  e3)
fromAHsExp  (AHsApp e1 e2)                 = HsApp (fromAHsExp  e1) (fromAHsExp  e2)
fromAHsExp  (AHsNegApp e)                  = HsNegApp (fromAHsExp  e)
fromAHsExp  (AHsLambda sloc pats e)        = HsLambda (fromASrcLoc sloc) (map fromAHsPat pats) (fromAHsExp  e)
fromAHsExp  (AHsLet decls e)               = HsLet (map (fromAHsDecl ) decls) (fromAHsExp  e)
fromAHsExp  (AHsIf e1 e2 e3)               = HsIf (fromAHsExp  e1) (fromAHsExp  e2) (fromAHsExp  e3)
fromAHsExp  (AHsCase e alts)               = HsCase (fromAHsExp  e) (map (fromAHsAlt ) alts)
fromAHsExp  (AHsDo stmts)                  = HsDo $ map (fromAHsStmt ) stmts
fromAHsExp  (AHsTuple es)                  = HsTuple $ map (fromAHsExp ) es
fromAHsExp  (AHsList es)                   = HsList $ map (fromAHsExp ) es
fromAHsExp  (AHsParen e)                   = HsParen $ fromAHsExp  e
fromAHsExp  (AHsLeftSection e1 e2)         = HsLeftSection (fromAHsExp  e1) (fromAHsExp  e2) 
fromAHsExp  (AHsRightSection e1 e2)        = HsRightSection (fromAHsExp  e1) (fromAHsExp  e2) 
fromAHsExp  (AHsRecConstr name fields)     = HsRecConstr (aHsNameToHsQName name) (map (fromAHsFieldUpdate ) fields) 
fromAHsExp  (AHsRecUpdate e fields)        = HsRecUpdate (fromAHsExp  e) (map (fromAHsFieldUpdate ) fields) 
fromAHsExp  (AHsEnumFrom e)                = HsEnumFrom $ fromAHsExp  e
fromAHsExp  (AHsEnumFromTo e1 e2)          = HsEnumFromTo (fromAHsExp  e1) (fromAHsExp  e2) 
fromAHsExp  (AHsEnumFromThen e1 e2)        = HsEnumFromThen (fromAHsExp  e1) (fromAHsExp  e2)
fromAHsExp  (AHsEnumFromThenTo e1 e2 e3)   = HsEnumFromThenTo (fromAHsExp  e1) (fromAHsExp  e2) (fromAHsExp  e3) 
fromAHsExp  (AHsListComp e stmts)          = HsListComp (fromAHsExp  e) (map (fromAHsStmt ) stmts) 
fromAHsExp  (AHsExpTypeSig sloc e qtype)   = HsExpTypeSig (fromASrcLoc sloc) (fromAHsExp  e) (fromAHsQualType qtype) 
fromAHsExp  (AHsAsPat name e)              = HsAsPat (fromAHsName name) (fromAHsExp  e)
fromAHsExp  AHsWildCard                    = HsWildCard 
fromAHsExp  (AHsIrrPat e)                  = HsIrrPat (fromAHsExp  e) 

fromAHsPat :: AHsPat -> HsPat 
fromAHsPat (AHsPVar name)                 = HsPVar $ fromAHsName name
fromAHsPat (AHsPLit lit)                  = HsPLit $ fromAHsLiteral lit
fromAHsPat (AHsPNeg pat)                  = HsPNeg $ fromAHsPat pat 
fromAHsPat (AHsPInfixApp pat1 qname pat2) = HsPInfixApp (fromAHsPat pat1) (aHsNameToHsQName qname) (fromAHsPat pat2)
fromAHsPat (AHsPApp qname pats)           = HsPApp (aHsNameToHsQName qname) $ map fromAHsPat pats 
fromAHsPat (AHsPTuple pats)               = HsPTuple $ map fromAHsPat pats
fromAHsPat (AHsPList pats)                = HsPList $ map fromAHsPat pats
fromAHsPat (AHsPParen pat)                = HsPParen $ fromAHsPat pat 
fromAHsPat (AHsPRec qname patfields)      = HsPRec (aHsNameToHsQName qname) $ map fromAHsPatField patfields
fromAHsPat (AHsPAsPat name pat)           = HsPAsPat (fromAHsName name) (fromAHsPat pat)
fromAHsPat AHsPWildCard                   = HsPWildCard
fromAHsPat (AHsPIrrPat pat)               = HsPIrrPat $ fromAHsPat pat

fromAHsPatField :: AHsPatField -> HsPatField
fromAHsPatField (AHsPFieldPat qname pat) = HsPFieldPat (aHsNameToHsQName qname) (fromAHsPat pat)

fromAHsStmt :: AHsStmt -> HsStmt
fromAHsStmt  (AHsGenerator sloc pat e) 
   = HsGenerator (fromASrcLoc sloc) 
                  (fromAHsPat pat) 
                  (fromAHsExp  e)
fromAHsStmt  (AHsQualifier e) = HsQualifier (fromAHsExp  e)
fromAHsStmt  (AHsLetStmt decls) = HsLetStmt $ map (fromAHsDecl ) decls

fromAHsFieldUpdate :: AHsFieldUpdate -> HsFieldUpdate
fromAHsFieldUpdate  (AHsFieldUpdate qname e) = HsFieldUpdate (aHsNameToHsQName qname) (fromAHsExp  e)

fromAHsAlt :: AHsAlt -> HsAlt
fromAHsAlt  (AHsAlt sloc pat galts decls)
   = HsAlt (fromASrcLoc sloc)
            (fromAHsPat pat)
            (fromAHsGuardedAlts  galts)
            (map (fromAHsDecl ) decls)

fromAHsGuardedAlts :: AHsGuardedAlts -> HsGuardedAlts
fromAHsGuardedAlts  (AHsUnGuardedAlt e)
   = HsUnGuardedAlt (fromAHsExp  e)
fromAHsGuardedAlts  (AHsGuardedAlts galts)
   = HsGuardedAlts $ map (fromAHsGuardedAlt ) galts

fromAHsGuardedAlt :: AHsGuardedAlt -> HsGuardedAlt
fromAHsGuardedAlt  (AHsGuardedAlt sloc e1 e2) 
   = HsGuardedAlt (fromASrcLoc sloc) (fromAHsExp e1) (fromAHsExp e2)

--------------------------------------------------------------------------------
