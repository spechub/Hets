{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 TypeSigs

        Description:            Collects all the type signatures from a module

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module TypeSigs (collectSigs,
                 SigEnv,
                 listSigsToSigEnv) where

import Env              (Env,
                         listToEnv)

import Type             (assumpToPair)

import KindInference    (KindEnv)

import Representation   (Kind,
                         Assump (..),
                         Scheme)

import TypeUtils        (aHsTypeSigToAssumps)

import AnnotatedHsSyn            -- everything

--------------------------------------------------------------------------------

collectSigs :: [(AHsDecl)] -> [(AHsDecl)]
collectSigs ds = collectSigsFromDecls ds

collectSigsFromDecls :: [(AHsDecl)] -> [(AHsDecl)]

collectSigsFromDecls [] = []

collectSigsFromDecls (d@(AHsTypeSig _ _ _):ds) 
   = d : collectSigsFromDecls ds

collectSigsFromDecls (d@(AHsPatBind _ _ rhs wheres):ds)
   = collectSigsFromRhs rhs ++ 
     collectSigsFromDecls wheres ++ 
     collectSigsFromDecls ds

collectSigsFromDecls (d@(AHsFunBind matches):ds)
   = concatMap collectSigsFromMatch matches ++
     collectSigsFromDecls ds

collectSigsFromDecls (_:ds)
   = collectSigsFromDecls ds

collectSigsFromMatch :: (AHsMatch) -> [(AHsDecl)]

collectSigsFromMatch (AHsMatch _ _ _ rhs wheres)
   = collectSigsFromRhs rhs ++
     collectSigsFromDecls wheres

collectSigsFromRhs :: (AHsRhs) -> [(AHsDecl)]

collectSigsFromRhs (AHsUnGuardedRhs e)
   = collectSigsFromExp e

collectSigsFromRhs (AHsGuardedRhss rhss)
   = concatMap collectSigsFromGuardedRhs rhss

collectSigsFromGuardedRhs :: (AHsGuardedRhs) -> [(AHsDecl)] 

collectSigsFromGuardedRhs (AHsGuardedRhs _ e1 e2)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2

collectSigsFromExp :: (AHsExp) -> [(AHsDecl)]


collectSigsFromExp (AHsVar _) = []

collectSigsFromExp (AHsCon _) = []

collectSigsFromExp (AHsLit _) = []

collectSigsFromExp (AHsInfixApp e1 e2 e3)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2 ++
     collectSigsFromExp e3

collectSigsFromExp (AHsApp e1 e2)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2

collectSigsFromExp (AHsNegApp e)
   = collectSigsFromExp e

collectSigsFromExp (AHsLambda _sloc _ e)
   = collectSigsFromExp e

collectSigsFromExp (AHsLet decls e)
   = collectSigsFromDecls decls ++
     collectSigsFromExp e

collectSigsFromExp (AHsIf e1 e2 e3)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2 ++
     collectSigsFromExp e3 

collectSigsFromExp (AHsCase e alts)
   = collectSigsFromExp e ++
     concatMap collectSigsFromAlt alts

collectSigsFromExp (AHsDo stmts)
   = concatMap collectSigsFromStmt stmts

collectSigsFromExp (AHsTuple exps)
   = concatMap collectSigsFromExp exps

collectSigsFromExp (AHsList exps)
   = concatMap collectSigsFromExp exps

collectSigsFromExp (AHsParen e)
   = collectSigsFromExp e

collectSigsFromExp (AHsLeftSection e1 e2)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2

collectSigsFromExp (AHsRightSection e1 e2)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2

collectSigsFromExp (AHsRecConstr _ _)
   = error "collectSigsFromExp (AHsRecConstr _ _) not implemented yet"

collectSigsFromExp (AHsRecUpdate _ _)
   = error "collectSigsFromExp (AHsRecUpdate _ _) not implemented yet"

collectSigsFromExp (AHsEnumFrom e)
   = collectSigsFromExp e

collectSigsFromExp (AHsEnumFromTo e1 e2)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2

collectSigsFromExp (AHsEnumFromThen e1 e2)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2

collectSigsFromExp (AHsEnumFromThenTo e1 e2 e3)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2 ++
     collectSigsFromExp e3

collectSigsFromExp (AHsListComp e stmts)
   = collectSigsFromExp e ++
     concatMap collectSigsFromStmt stmts

collectSigsFromExp (AHsExpTypeSig _ e _)
   = collectSigsFromExp e

collectSigsFromExp (AHsAsPat _ e)
   = collectSigsFromExp e

collectSigsFromExp AHsWildCard = []

collectSigsFromExp (AHsIrrPat e)
   = collectSigsFromExp e

collectSigsFromAlt :: (AHsAlt) -> [(AHsDecl)]

collectSigsFromAlt (AHsAlt _ _ (AHsUnGuardedAlt e) decls)
   = collectSigsFromExp e ++
     collectSigsFromDecls decls

collectSigsFromAlt (AHsAlt _ _ (AHsGuardedAlts alts) decls)
   = concatMap collectSigsFromGuardedAlt alts ++
     collectSigsFromDecls decls

collectSigsFromGuardedAlt :: (AHsGuardedAlt) -> [(AHsDecl)]

collectSigsFromGuardedAlt (AHsGuardedAlt _ e1 e2)
   = collectSigsFromExp e1 ++
     collectSigsFromExp e2

collectSigsFromStmt :: (AHsStmt) -> [(AHsDecl)]

collectSigsFromStmt (AHsGenerator _ _ e)
   = collectSigsFromExp e

collectSigsFromStmt (AHsQualifier e)
   = collectSigsFromExp e

collectSigsFromStmt (AHsLetStmt decls)
   = collectSigsFromDecls decls

--------------------------------------------------------------------------------

type SigEnv = Env Scheme

listSigsToSigEnv :: KindEnv -> [AHsDecl] -> SigEnv
listSigsToSigEnv kt sigs
   = listToEnv $ 
        map assumpToPair $
        concatMap (aHsTypeSigToAssumps kt) sigs
        

