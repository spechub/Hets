{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 Desugar

        Description:            Desugaring of the abstract syntax.

                                The main tasks implemented by this module are:
                                        - pattern bindings are converted
                                          into "simple" pattern bindings
                                          (x, y, z) = foo
                                             becomes
                                          newVal = foo
                                          x = (\(a, _, _) -> a) newVal
                                          y = (\(_, a, _) -> a) newVal
                                          z = (\(_, _, a) -> a) newVal
                                        - do notation is converted into 
                                          expression form, using (>>) and
                                          (>>=)
                                        - type synonyms are removed

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

                                According to the Haskell report a pattern 
                                binding is called "simple" if it consists only 
                                of a single variable - thus we convert all 
                                pattern bindings to simple bindings.

-------------------------------------------------------------------------------}


module Desugar (desugarTidyModule, doToExp) where

import AnnotatedHsSyn           -- everything 

import TypeSynonyms             (removeSynonymsFromType,
                                 removeSynsFromSig)

import TidyModule               (TidyModule (..))


-- (unique int, list of type synoyms)
type PatState = (Int, [AHsDecl])

readUnique :: PatSM Int 
readUnique 
   = do
        state <- readPatSM
        return (fst state) 

readSyns :: PatSM [AHsDecl]
readSyns 
   = do
        state <- readPatSM
        return (snd state)


incUnique :: PatSM () 
incUnique = updatePatSM (\(u, s) -> (u + 1, s))

data PatSM a = PatSM (PatState -> (a, PatState))  -- The monadic type

instance Monad PatSM where
  -- defines state propagation
  PatSM c1 >>= fc2         =  PatSM (\s0 -> let (r,s1) = c1 s0
                                                PatSM c2 = fc2 r in
                                                c2 s1)
  return k                  =  PatSM (\s -> (k,s))

 -- extracts the state from the monad
readPatSM                  :: PatSM PatState 
readPatSM                  =  PatSM (\s -> (s,s))

 -- updates the state of the monad
updatePatSM                :: (PatState -> PatState) -> PatSM ()  -- alters the state
updatePatSM f              =  PatSM (\s -> ((), f s))

-- run a computation in the PatSM monad
runPatSM                   :: PatState -> PatSM a -> (a, PatState)
runPatSM s0 (PatSM c)     =  c s0

{------------------------------------------------------------------------------}


-- a new (unique) name introduced in pattern selector functions
newPatVarName :: AHsName
newPatVarName = AUnQual $ AHsIdent "newPatVar_From_Desugaring"

-- a new (unique) name introduced in expressions 
newVarName :: AHsName
newVarName = AUnQual $ AHsIdent "newVar_From_Desugaring"

remSynsSig :: AHsDecl -> PatSM AHsDecl 
remSynsSig sig 
   = do
        syns <- readSyns
        let newSig = removeSynsFromSig syns sig
        return newSig

remSynsType :: AHsType -> PatSM AHsType
remSynsType t
   = do
        syns <- readSyns
        let newType = removeSynonymsFromType syns t 
        return newType


{-
 this function replaces all constructor-pattern bindings in a module with
 function calls

 ie:

 (x, y) = head $ zip "abc" [1,2,3]

 becomes
 
 x = (\(a, _) -> a) rhs1
 y = (\(_, a) -> a) rhs1
 rhs1 = head $ zip "abc" [1,2,3]
-}

-- first argument is imported synonyms
desugarTidyModule :: [AHsDecl] -> TidyModule -> TidyModule
desugarTidyModule importSyns tidy
   = newTidy
   where
   (newTidy, _) = runPatSM (0::Int, synonyms) $ desugarTidyModuleM tidy 
   synonyms = tidyTyDecls tidy ++ importSyns

desugarTidyModuleM :: TidyModule -> PatSM TidyModule
desugarTidyModuleM tidy
   = do let -- oldTyDecls    = tidyTyDecls tidy
            oldDataDecls  = tidyDataDecls tidy
            oldInFixDecls = tidyInFixDecls tidy
            oldNewTyDecls = tidyNewTyDecls tidy
            oldClassDecls = tidyClassDecls tidy
            oldInstDecls  = tidyInstDecls tidy
            oldDefs       = tidyDefDecls tidy
            oldTySigs     = tidyTySigs tidy
            oldFunBinds   = tidyFunBinds tidy
            oldPatBinds   = tidyPatBinds tidy
     -- newTyDecls    <- desugarDecl oldTyDecls 
        newDataDecls  <- mapM desugarDecl oldDataDecls 
        newInFixDecls <- mapM desugarDecl oldInFixDecls 
        newNewTyDecls <- mapM desugarDecl oldNewTyDecls 
        newClassDecls <- mapM desugarDecl oldClassDecls 
        newInstDecls  <- mapM desugarDecl oldInstDecls 
        newDefs       <- mapM desugarDecl oldDefs 
        newTySigs     <- mapM desugarDecl oldTySigs 
        newFunBinds   <- mapM desugarDecl oldFunBinds 
        newPatBinds   <- mapM desugarDecl oldPatBinds 
        return tidy{tidyTyDecls    = [],  -- return the empty list of synonyms, we don't need them anymore
                    tidyDataDecls  = concat newDataDecls,
                    tidyInFixDecls = concat newInFixDecls,
                    tidyNewTyDecls = concat newNewTyDecls,
                    tidyClassDecls = concat newClassDecls,
                    tidyInstDecls  = concat newInstDecls,
                    tidyDefDecls   = concat newDefs,
                    tidyTySigs     = concat newTySigs,
                    tidyFunBinds   = concat newFunBinds,
                    tidyPatBinds   = concat newPatBinds}



desugarDecl :: AHsDecl -> PatSM [AHsDecl]

-- desugarDecl (AHsFunBind sloc matches)
desugarDecl (AHsFunBind matches)
   = do
        newMatches <- mapM desugarMatch matches  
        -- return [AHsFunBind sloc newMatches]
        return [AHsFunBind newMatches]

-- variable pattern bindings remain unchanged

desugarDecl pb@(AHsPatBind sloc (AHsPVar n) rhs wheres)
--   = return [pb]
   = do
        newRhs <- desugarRhs rhs
        newWheres <- mapM desugarDecl wheres
        return [AHsPatBind sloc (AHsPVar n) newRhs (concat newWheres)]
        

-- constructor and tuple pattern bindings must be changed
-- XXX bjpop: what about nested parenthesised patterns that just bind
-- variables?

desugarDecl pb@(AHsPatBind sloc pat rhs wheres)
   = do
        unique <- readUnique  -- these must be done 
        incUnique             -- together

        let newRhsName = AUnQual $ AHsIdent $ "newPatRhs_From_Desugaring" ++ show unique
        newWheres <- mapM desugarDecl wheres
        let newTopDeclForRhs 
               = AHsPatBind bogusASrcLoc (AHsPVar newRhsName) rhs (concat newWheres)
        let newBinds = genBindsForPat pat sloc newRhsName 
        return (newTopDeclForRhs : newBinds)

desugarDecl (AHsClassDecl sloc qualtype decls)
   = do
        newDecls <- mapM desugarDecl decls 
        return [AHsClassDecl sloc qualtype (concat newDecls)]

desugarDecl (AHsInstDecl sloc qualtype decls)
   = do
        newQualType <- remSynsQualType qualtype
        newDecls <- mapM desugarDecl decls
        return [AHsInstDecl sloc newQualType (concat newDecls)]

desugarDecl sig@(AHsTypeSig _sloc _names _qualType)
   = do
        newSig <- remSynsSig sig 
        return [newSig]


desugarDecl (AHsDataDecl sloc cntxt name args condecls derives)
   = do
        newConDecls <- mapM remSynsFromCondecl condecls
        return [(AHsDataDecl sloc cntxt name args newConDecls derives)]
        
desugarDecl anyOtherDecl = return [anyOtherDecl]

remSynsFromCondecl :: AHsConDecl -> PatSM AHsConDecl
remSynsFromCondecl (AHsConDecl sloc name bangTypes)
   = do
        newBangTypes <- mapM remSynsFromBangType bangTypes
        return (AHsConDecl sloc name newBangTypes)
remSynsFromCondecl (AHsRecDecl _ _ _)
   = error $ "remSynsFromCondecl (AHsRecDecl _ _ _) not implemented"

remSynsFromBangType :: AHsBangType -> PatSM AHsBangType

remSynsFromBangType (AHsBangedTy t)
   = do
        newType <- remSynsType t
        return (AHsBangedTy newType)

remSynsFromBangType (AHsUnBangedTy t)
   = do
        newType <- remSynsType t
        return (AHsUnBangedTy newType)   


desugarMatch :: (AHsMatch) -> PatSM (AHsMatch)
desugarMatch (AHsMatch sloc funName pats rhs wheres)
   = do
        newWheres <- mapM desugarDecl wheres
        newRhs <- desugarRhs rhs
        return (AHsMatch sloc funName pats newRhs (concat newWheres))

-- generate the pattern bindings for each variable in a pattern

genBindsForPat :: AHsPat -> ASrcLoc -> AHsName -> [AHsDecl]
genBindsForPat pat sloc rhsName
   = [AHsPatBind sloc (AHsPVar patName) (AHsUnGuardedRhs (AHsApp selector (AHsVar rhsName))) [] |  (patName, selector) <- selFuns]
   where
   selFuns = getPatSelFuns pat

-- generate selector functions for each of the variables that
-- are bound in a pattern

getPatSelFuns :: AHsPat -> [(AHsName, (AHsExp))]
getPatSelFuns pat
   = [(varName, AHsParen (AHsLambda bogusASrcLoc [replaceVarNamesInPat varName pat] (AHsVar newPatVarName ))) | varName <- patVarNames pat]

-- returns the names of variables bound in a pattern
-- XXX bjpop: do as patterns work properly?
patVarNames :: AHsPat -> [AHsName]
patVarNames (AHsPVar name) = [name]
patVarNames (AHsPLit _) = []
patVarNames (AHsPNeg pat) = patVarNames pat
patVarNames (AHsPInfixApp pat1 conName pat2)
   = patVarNames pat1 ++ patVarNames pat2
patVarNames (AHsPApp conName pats)
   = concatMap patVarNames pats
patVarNames (AHsPTuple pats)
   = concatMap patVarNames pats
patVarNames (AHsPList pats)
   = concatMap patVarNames pats
patVarNames (AHsPParen pat)
   = patVarNames pat
patVarNames (AHsPRec _ _) = error "patVarNames (AHsPRec _ _): not implemented "
patVarNames (AHsPAsPat asName pat)
   = asName : patVarNames pat
patVarNames AHsPWildCard = []
patVarNames (AHsPIrrPat pat)
   = patVarNames pat 

-- replaces all occurrences of a name with a new variable 
-- and every other name with underscore

replaceVarNamesInPat :: AHsName -> AHsPat -> AHsPat

replaceVarNamesInPat name1 (AHsPVar name2)
   | name1 == name2 = AHsPVar $ newPatVarName
   | otherwise = AHsPWildCard
replaceVarNamesInPat _ p@(AHsPLit _) = p
replaceVarNamesInPat name (AHsPNeg pat) 
   = AHsPNeg $ replaceVarNamesInPat name pat 
replaceVarNamesInPat name (AHsPInfixApp pat1 conName pat2) 
   = AHsPInfixApp (replaceVarNamesInPat name pat1) conName (replaceVarNamesInPat name pat2)
replaceVarNamesInPat name (AHsPApp conName pats)
   = AHsPApp conName (map (replaceVarNamesInPat name) pats)
replaceVarNamesInPat name (AHsPTuple pats)
   = AHsPTuple (map (replaceVarNamesInPat name) pats)
replaceVarNamesInPat name (AHsPList pats)
   = AHsPList (map (replaceVarNamesInPat name) pats)
replaceVarNamesInPat name (AHsPParen pat)
   = AHsPParen (replaceVarNamesInPat name pat)
replaceVarNamesInPat name (AHsPRec _ _) 
   = error  "replaceVarNamesInPat name (AHsPRec _ _): not implemented"
replaceVarNamesInPat name (AHsPAsPat asName pat)
   | name == asName = AHsPAsPat newPatVarName (replaceVarNamesInPat name pat)
   | otherwise = replaceVarNamesInPat name pat
replaceVarNamesInPat name AHsPWildCard = AHsPWildCard
replaceVarNamesInPat name (AHsPIrrPat pat)
   = AHsPIrrPat $ replaceVarNamesInPat name pat 


desugarRhs :: (AHsRhs) -> PatSM (AHsRhs)
desugarRhs (AHsUnGuardedRhs e)
   = do
        newE <- desugarExp e
        return (AHsUnGuardedRhs newE)

desugarRhs (AHsGuardedRhss gRhss)
   = do
        newRhss <- mapM desugarGRhs gRhss
        return (AHsGuardedRhss newRhss)

desugarGRhs :: AHsGuardedRhs -> PatSM (AHsGuardedRhs)
desugarGRhs (AHsGuardedRhs sloc e1 e2)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        return (AHsGuardedRhs sloc newE1 newE2)

desugarExp :: (AHsExp) -> PatSM (AHsExp)

desugarExp e@(AHsVar name)
   = return e

desugarExp e@(AHsCon name)
   = return e 

desugarExp e@(AHsLit l)
   = return e

desugarExp (AHsInfixApp e1 e2 e3)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        newE3 <- desugarExp e3
        return (AHsInfixApp newE1 newE2 newE3)

desugarExp (AHsApp e1 e2)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        return (AHsApp newE1 newE2)

desugarExp (AHsNegApp e)
   = do
        newE <- desugarExp e
        return (AHsNegApp newE)

desugarExp (AHsLambda sloc pats e)
   = do
        newE <- desugarExp e
        return (AHsLambda sloc pats newE)

desugarExp (AHsLet decls e)
   = do
        newDecls <- mapM desugarDecl decls    
        newE <- desugarExp e
        return (AHsLet (concat newDecls) newE)

desugarExp (AHsIf e1 e2 e3)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        newE3 <- desugarExp e3
        return (AHsIf newE1 newE2 newE3)

desugarExp (AHsCase e alts)
   = do
        newE <- desugarExp e
        newAlts <- mapM desugarAlt alts
        return (AHsCase newE newAlts)

desugarExp (AHsDo stmts)
   = do
        newStmts <- mapM desugarStmt stmts
        return (doToExp newStmts)

desugarExp (AHsTuple exps)
   = do
        newExps <- mapM desugarExp exps
        return (AHsTuple newExps)

desugarExp (AHsList exps)   
   = do
        newExps <- mapM desugarExp exps
        return (AHsList newExps)

desugarExp (AHsParen e)
   = do
        newE <- desugarExp e
        return (AHsParen newE)

desugarExp (AHsLeftSection e1 e2)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        return (AHsLeftSection newE1 newE2)

desugarExp (AHsRightSection e1 e2)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        return (AHsRightSection newE1 newE2)

desugarExp (AHsRecConstr _ _)
   = error "desugarExp (AHsRecConstr _ _): not implemented"

desugarExp (AHsRecUpdate _ _)
   = error "desugarExp (AHsRecUpdate _ _): not implemented"

desugarExp (AHsEnumFrom e)
   = do
        newE <- desugarExp e
        return (AHsEnumFrom newE)

desugarExp (AHsEnumFromTo e1 e2)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        return (AHsEnumFromTo newE1 newE2)

desugarExp (AHsEnumFromThen e1 e2)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        return (AHsEnumFromThen newE1 newE2)

desugarExp (AHsEnumFromThenTo e1 e2 e3)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        newE3 <- desugarExp e3
        return (AHsEnumFromThenTo newE1 newE2 newE3)

desugarExp (AHsListComp e stmts)
   = do
        newE <- desugarExp e
        newStmts <- mapM desugarStmt stmts
        return (AHsListComp newE newStmts)

-- e :: t  ---> let {v :: t, v = e} in e

{-
desugarExp (AHsExpTypeSig sloc e qualType)
   = do
        newE <- desugarExp e
        newQualType <- remSynsQualType qualType
        return (AHsExpTypeSig sloc newE newQualType)
-}

desugarExp (AHsExpTypeSig sloc e qualType)
   = do 
        newE <- desugarExp e
        newQualType <- remSynsQualType qualType
        let newTypeSig = AHsTypeSig bogusASrcLoc [newVarName] newQualType
        let newVarDecl = AHsPatBind bogusASrcLoc 
                                    (AHsPVar newVarName) 
                                    (AHsUnGuardedRhs newE) []
        return (AHsLet [newTypeSig, newVarDecl] (AHsVar newVarName))


desugarExp (AHsAsPat name e)
   = do
        newE <- desugarExp e
        return (AHsAsPat name e)

desugarExp AHsWildCard
   = return AHsWildCard

desugarExp (AHsIrrPat e)
   = do
        newE <- desugarExp e
        return (AHsIrrPat newE) 


desugarAlt :: (AHsAlt) -> PatSM (AHsAlt)

desugarAlt (AHsAlt sloc pat gAlts wheres)
   = do
        newGAlts <- desugarGAlts gAlts
        newWheres <- mapM desugarDecl wheres
        return (AHsAlt sloc pat newGAlts (concat newWheres))

desugarGAlts :: (AHsGuardedAlts) -> PatSM (AHsGuardedAlts)

desugarGAlts (AHsUnGuardedAlt e)
   = do
        newE <- desugarExp e
        return (AHsUnGuardedAlt newE)

desugarGAlts (AHsGuardedAlts gAlts)
   = do
        newGAlts <- mapM desugarGuardedAlt gAlts
        return (AHsGuardedAlts newGAlts)

desugarGuardedAlt :: (AHsGuardedAlt) -> PatSM (AHsGuardedAlt)

desugarGuardedAlt (AHsGuardedAlt sloc e1 e2)
   = do
        newE1 <- desugarExp e1
        newE2 <- desugarExp e2
        return (AHsGuardedAlt sloc newE1 newE2)

desugarStmt :: (AHsStmt) -> PatSM (AHsStmt)
desugarStmt (AHsGenerator srcLoc pat e)
   = do
        newE <- desugarExp e
        return (AHsGenerator srcLoc pat newE)

desugarStmt (AHsQualifier e)
   = do
        newE <- desugarExp e
        return (AHsQualifier newE)

desugarStmt (AHsLetStmt decls)
   = do
        newDecls <- mapM desugarDecl decls 
        return (AHsLetStmt $ concat newDecls)


remSynsQualType :: AHsQualType -> PatSM AHsQualType
remSynsQualType qualtype
   = case qualtype of
        AHsQualType cntxt t
           -> do
                 newT <- remSynsType t
                 return (AHsQualType cntxt newT)
        AHsUnQualType t
           -> do
                 newT <- remSynsType t
                 return (AHsUnQualType newT)

--------------------------------------------------------------------------------

-- desugar the do-notation

-- flatten out do notation into an expression
-- involving ">>" and ">>="

doToExp :: [AHsStmt] -> AHsExp

doToExp [] = error "doToExp: empty statements in do notation"
doToExp [AHsQualifier e] = e
doToExp [gen@(AHsGenerator srcLoc _pat _e)]
   = error $ "doToExp: last expression n do notation is a generator (srcLoc):" ++ show srcLoc
doToExp [letst@(AHsLetStmt _decls)]
   = error $ "doToExp: last expression n do notation is a let statement"
doToExp ((AHsQualifier e):ss)
   = AHsInfixApp (AHsParen e) (AHsVar (AUnQual (AHsSymbol ">>"))) (doToExp ss)
doToExp ((AHsGenerator _srcLoc pat e):ss)
   = AHsInfixApp (AHsParen e) (AHsVar (AUnQual (AHsSymbol ">>="))) (AHsLambda bogusASrcLoc [pat] (doToExp ss))
doToExp ((AHsLetStmt decls):ss)
   = AHsLet decls (doToExp ss)
