{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 HsParsePostProcess.hs

        Description:            Post processing for the Haskell Parser suite.

                                The HsParser places each HsMatch equation in 
                                a seperate HsFunbind, even when multiple 
                                HsMatchs should appear in the same HsFunbind.  

                                This code is intended as a post-processor of the
                                output from the parser, that re-groups 
                                associated HsMatch equations into the same 
                                HsFunBind. It has no semantic effect on the code.

                                It requires a single pass over the entire parse
                                tree, some applications might find this expensive.

                                Associated matches are determined by the string
                                name of the variable that is being bound, in
                                _unqualified_ form. This means that:

                                Foo.f w x = ...
                                f y z  = ...

                                are treated as matches for the same variable, 
                                even though I don't think this is possible in 
                                Haskell 98, the parser does allow it, and thus so 
                                does this code.

                                There is plenty of room for static analysis of the
                                parsed code, but that is not the intention of this
                                module.

                                In time, other post-processing tasks may be 
                                placed in this module.

        Primary Authors:        Bernie Pope  

        Notes:                  See the file License for license information 

                                Make the task of crawling over the parse tree more
                                general, to allow for other similar types of
                                code-processing stages. Presently I can't think of
                                how to do this with such a complex data-structure.

-------------------------------------------------------------------------------}

module HsParsePostProcess (fixFunBindsInModule, fixFunBinds) where

import HsSyn            -- import everything

-- applies fixFunBinds to all decls in a Module
fixFunBindsInModule :: HsModule -> HsModule
fixFunBindsInModule (HsModule modName exports imports decls)
   =  HsModule modName exports imports $ fixFunBinds decls

-- collect associated funbind equations (matches) into a single funbind
-- intended as a post-processer for the parser output
fixFunBinds :: [HsDecl] -> [HsDecl]
fixFunBinds [] = []
fixFunBinds (d:ds)
   = case d of
        HsClassDecl sloc qualType decls
           -> HsClassDecl sloc qualType (fixFunBinds decls) : fixFunBinds ds 
        HsInstDecl sloc qualType decls 
           -> HsInstDecl sloc qualType (fixFunBinds decls) : fixFunBinds ds 
        HsFunBind matches@(_:_)                
           -> let funName = matchName $ head matches 
                  (same, different) = span (sameFun funName) (d:ds)
                  newMatches = map fixFunBindsInMatch $ collectMatches same
              in (HsFunBind newMatches) : fixFunBinds different
        HsPatBind sloc pat rhs decls
           -> HsPatBind sloc pat (fixFunBindsInRhs rhs) 
                                 (fixFunBinds decls) : fixFunBinds ds
        _anythingElse -> d : fixFunBinds ds

-- get the variable name bound by a match
matchName :: HsMatch -> String 
matchName (HsMatch _sloc name _pats _rhs _whereDecls) = unQualName name 

-- selects the string identifier from a (possibly)
-- qualified name (ie drops the module name when possible) 
unQualName :: HsQName -> String
unQualName name 
   = case name of
        (Qual _mod ident) -> unHsName ident
        (UnQual ident)    -> unHsName ident
   where
   unHsName (HsIdent s)   = s
   unHsName (HsSymbol s)  = s 
   unHsName (HsSpecial s) = s

-- True if the decl is a HsFunBind and binds the same name as the
-- first argument, False otherwise
sameFun :: String -> HsDecl -> Bool
sameFun name (HsFunBind matches@(_:_))
   | name == (matchName $ head matches) = True
   | otherwise = False
sameFun _name _decl = False

-- collects all the HsMatch equations from any FunBinds
-- from a list of HsDecls
collectMatches :: [HsDecl] -> [HsMatch] 
collectMatches [] = []
collectMatches (d:ds)
   = case d of
        (HsFunBind matches) -> matches ++ collectMatches ds
        _anythingElse             -> collectMatches ds 

-- the rest of the code just crawls tediously over the syntax tree
-- recursively fixing up any decls where they occur
fixFunBindsInMatch :: HsMatch -> HsMatch 
fixFunBindsInMatch (HsMatch sloc name pats rhs wheres)
   = HsMatch sloc name pats (fixFunBindsInRhs rhs) $ fixFunBinds wheres 

fixFunBindsInRhs :: HsRhs -> HsRhs
fixFunBindsInRhs (HsUnGuardedRhs e)
   = HsUnGuardedRhs $ fixFunBindsInExp e

fixFunBindsInRhs (HsGuardedRhss rhss)
   = HsGuardedRhss $ map fixFunBindsInGuardedRhs rhss

fixFunBindsInGuardedRhs :: HsGuardedRhs -> HsGuardedRhs 
fixFunBindsInGuardedRhs (HsGuardedRhs sloc e1 e2)
   = HsGuardedRhs sloc (fixFunBindsInExp e1) (fixFunBindsInExp e2)

fixFunBindsInExp :: HsExp -> HsExp 
fixFunBindsInExp e@(HsVar _) = e 

fixFunBindsInExp e@(HsCon _) = e 

fixFunBindsInExp e@(HsLit _) = e 

fixFunBindsInExp (HsInfixApp e1 e2 e3)
   = HsInfixApp (fixFunBindsInExp e1) 
                 (fixFunBindsInExp e2) 
                 (fixFunBindsInExp e3)

fixFunBindsInExp (HsApp e1 e2)
   = HsApp (fixFunBindsInExp e1) (fixFunBindsInExp e2)

fixFunBindsInExp (HsNegApp e)
   = HsNegApp $ fixFunBindsInExp e 


fixFunBindsInExp (HsLambda sloc pats e)
   = HsLambda sloc pats $ fixFunBindsInExp e 

fixFunBindsInExp (HsLet decls e)
   = HsLet (fixFunBinds decls) $ fixFunBindsInExp e

fixFunBindsInExp (HsIf e1 e2 e3)
   = HsIf (fixFunBindsInExp e1)
          (fixFunBindsInExp e2)
          (fixFunBindsInExp e3)

fixFunBindsInExp (HsCase e alts)
   = HsCase (fixFunBindsInExp e) $ map fixFunBindsInAlt alts

fixFunBindsInExp (HsDo stmts)
   = HsDo $ map fixFunBindsInStmt stmts 

fixFunBindsInExp (HsTuple exps)
   = HsTuple $ map fixFunBindsInExp exps

fixFunBindsInExp (HsList exps)
   = HsList $ map fixFunBindsInExp exps

fixFunBindsInExp (HsParen e)
   = HsParen $ fixFunBindsInExp e

fixFunBindsInExp (HsLeftSection e1 e2)
   = HsLeftSection (fixFunBindsInExp e1)
                   (fixFunBindsInExp e2)

fixFunBindsInExp (HsRightSection e1 e2)
   = HsRightSection (fixFunBindsInExp e1)
                    (fixFunBindsInExp e2)

fixFunBindsInExp e@(HsRecConstr qname fieldUpdates)
   = e 

fixFunBindsInExp (HsRecUpdate e fieldUpdates)
   = HsRecUpdate (fixFunBindsInExp e) fieldUpdates 

fixFunBindsInExp (HsEnumFrom e)
   = HsEnumFrom $ fixFunBindsInExp e

fixFunBindsInExp (HsEnumFromTo e1 e2)
   = HsEnumFromTo (fixFunBindsInExp e1)
                  (fixFunBindsInExp e2)

fixFunBindsInExp (HsEnumFromThen e1 e2)
   = HsEnumFromThen (fixFunBindsInExp e1)
                    (fixFunBindsInExp e2)

fixFunBindsInExp (HsEnumFromThenTo e1 e2 e3)
   = HsEnumFromThenTo (fixFunBindsInExp e1)
                      (fixFunBindsInExp e2)
                      (fixFunBindsInExp e3)

fixFunBindsInExp (HsListComp e stmts)
   = HsListComp (fixFunBindsInExp e) $ map fixFunBindsInStmt stmts

fixFunBindsInExp (HsExpTypeSig sloc e qtype)
   = HsExpTypeSig sloc (fixFunBindsInExp e) qtype

fixFunBindsInExp (HsAsPat name e)
   = HsAsPat name $ fixFunBindsInExp e

fixFunBindsInExp e@HsWildCard = e 

fixFunBindsInExp (HsIrrPat e)
   = HsIrrPat $ fixFunBindsInExp e

fixFunBindsInAlt :: HsAlt -> HsAlt

fixFunBindsInAlt (HsAlt sloc pat (HsUnGuardedAlt e) decls)
   = HsAlt sloc pat (HsUnGuardedAlt (fixFunBindsInExp e)) $ fixFunBinds decls

fixFunBindsInAlt (HsAlt sloc pat (HsGuardedAlts alts) decls)
   = HsAlt sloc pat 
        (HsGuardedAlts $ map fixFunBindsInGuardedAlt alts) $ fixFunBinds decls

fixFunBindsInGuardedAlt :: HsGuardedAlt -> HsGuardedAlt 

fixFunBindsInGuardedAlt (HsGuardedAlt sloc e1 e2)
   = HsGuardedAlt sloc (fixFunBindsInExp e1) 
                       (fixFunBindsInExp e2)

fixFunBindsInStmt :: HsStmt -> HsStmt 

fixFunBindsInStmt (HsGenerator sloc pat e)
   = HsGenerator sloc pat $ fixFunBindsInExp e

fixFunBindsInStmt (HsQualifier e)
   = HsQualifier $ fixFunBindsInExp e

fixFunBindsInStmt (HsLetStmt decls)
   = HsLetStmt $ fixFunBinds decls

--------------------------------------------------------------------------------
