{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 DeclsDepends 

        Description:            Collect the names that a variable declaration
                                depends upon, for use in dependency 
                                analysis.

        Primary Authors:        Bernie Pope, Robert Shelton

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module DeclsDepends (getDeclDeps, debugDeclBindGroups) where

import AnnotatedHsSyn           -- almost everything

import DependAnalysis           (debugBindGroups)

import Utils                    (getDeclName, fromAHsName)

import Rename                   (unRename)

--------------------------------------------------------------------------------

-- for printing out decl bindgroups

debugDeclBindGroups :: [[AHsDecl]] -> String
debugDeclBindGroups groups 
   = debugBindGroups groups (fromAHsName . unRename . getDeclName)
                            getDeclName
                            getDeclDeps  

-- AHsDecl getDeps function 


getDeclDeps :: AHsDecl -> [AHsName]

getDeclDeps decl@(AHsPatBind _pat sloc rhs wheres) 
   = getRhsDeps rhs ++ foldr (++) [] (map getLocalDeclDeps wheres)

getDeclDeps decl@(AHsFunBind matches)
   = foldr (++) [] (map getMatchDeps matches)

getDeclDeps _ = []


getMatchDeps :: AHsMatch -> [AHsName]
getMatchDeps (AHsMatch _sloc _name _pats rhs wheres)
   = getRhsDeps rhs ++ foldr (++) [] (map getLocalDeclDeps wheres)

-- get the dependencies from the local definitions in a function

getLocalDeclDeps :: AHsDecl -> [AHsName]
getLocalDeclDeps (AHsFunBind matches)
   = foldr (++) [] (map getMatchDeps matches)
   
getLocalDeclDeps (AHsPatBind _sloc _hspat rhs wheres)
   = getRhsDeps rhs ++ foldr (++) [] (map getLocalDeclDeps wheres) 

getLocalDeclDeps _ = []

-- get the dependencies from the rhs of a function

getRhsDeps :: AHsRhs -> [AHsName]
getRhsDeps (AHsUnGuardedRhs e) 
   = getExpDeps e
getRhsDeps (AHsGuardedRhss rhss)
   = foldr (++) [] (map getGuardedRhsDeps rhss)

getGuardedRhsDeps :: AHsGuardedRhs -> [AHsName]
getGuardedRhsDeps (AHsGuardedRhs _sloc guardExp rhsExp) 
   = getExpDeps guardExp ++ getExpDeps rhsExp 

getExpDeps :: AHsExp -> [AHsName]
getExpDeps (AHsVar name) 
   = [name] 

getExpDeps (AHsCon _)
   = []

getExpDeps (AHsLit _)
   = []

getExpDeps (AHsInfixApp e1 e2 e3)
   = getExpDeps e1 ++
     getExpDeps e2 ++
     getExpDeps e3 

getExpDeps (AHsApp e1 e2) 
   = getExpDeps e1 ++ getExpDeps e2 

getExpDeps (AHsNegApp e) 
   = getExpDeps e 

getExpDeps (AHsLambda _ _ e) 
   = getExpDeps e 

getExpDeps (AHsLet decls e)
   = foldr (++) [] (map getLocalDeclDeps decls) ++
     getExpDeps e 

getExpDeps (AHsIf e1 e2 e3) 
   = getExpDeps e1 ++
     getExpDeps e2 ++
     getExpDeps e3 

getExpDeps (AHsCase e alts)
   = getExpDeps e ++
     foldr (++) [] (map getAltDeps alts)

getExpDeps (AHsDo stmts)
   = foldr (++) [] (map getStmtDeps stmts)

getExpDeps (AHsTuple exps) 
   = foldr (++) [] (map getExpDeps exps)

getExpDeps (AHsList exps) 
   = foldr (++) [] (map getExpDeps exps)

getExpDeps (AHsParen e)
   = getExpDeps e

getExpDeps (AHsLeftSection e1 e2)
   = getExpDeps e1 ++
     getExpDeps e2

getExpDeps (AHsRightSection e1 e2)
   = getExpDeps e1 ++
     getExpDeps e2

getExpDeps (AHsEnumFrom e)
   = getExpDeps e

getExpDeps (AHsEnumFromTo e1 e2)
   = getExpDeps e1 ++
     getExpDeps e2

getExpDeps (AHsEnumFromThen e1 e2)
   = getExpDeps e1 ++
     getExpDeps e2

getExpDeps (AHsEnumFromThenTo e1 e2 e3)
   = getExpDeps e1 ++
     getExpDeps e2 ++
     getExpDeps e3

getExpDeps (AHsListComp e stmts)
   = getExpDeps e ++
     foldr (++) [] (map getStmtDeps stmts)

getExpDeps (AHsExpTypeSig _sloc e _qualtype)
   = getExpDeps e

getExpDeps (AHsAsPat _name e)
   = getExpDeps e

getExpDeps AHsWildCard
   = []

getExpDeps (AHsIrrPat e)
   = getExpDeps e


getAltDeps :: AHsAlt -> [AHsName]

getAltDeps (AHsAlt _sloc _pat guardedAlts wheres)
   = getGuardedAltsDeps guardedAlts ++
     foldr (++) [] (map getLocalDeclDeps wheres) 

getGuardedAltsDeps :: AHsGuardedAlts -> [AHsName]
getGuardedAltsDeps (AHsUnGuardedAlt e)
   = getExpDeps e

getGuardedAltsDeps (AHsGuardedAlts gAlts)
   = foldr (++) [] (map getGAltsDeps gAlts)

getGAltsDeps :: AHsGuardedAlt -> [AHsName]
getGAltsDeps (AHsGuardedAlt _sloc e1 e2)
   = getExpDeps e1 ++
     getExpDeps e2

getStmtDeps :: AHsStmt -> [AHsName]
getStmtDeps (AHsGenerator _srcLoc _pat e)
   = getExpDeps e

getStmtDeps (AHsQualifier e)
   = getExpDeps e

getStmtDeps (AHsLetStmt decls)
   = foldr (++) [] (map getLocalDeclDeps decls)
