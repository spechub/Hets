{-------------------------------------------------------------------------------

        Copyright:              Mark Jones and The Hatchet Team 
                                (see file Contributors)

        Module:                 TIMain

        Description:            The main components of the type inference 
                                algorithm.

        Primary Authors:        Mark Jones, Bernie Pope and Bryn Humberstone

        Notes:                  See the file License for license information

                                Large parts of this module were derived from
                                the work of Mark Jones' "Typing Haskell in
                                Haskell", (http://www.cse.ogi.edu/~mpj/thih/)

-------------------------------------------------------------------------------}

module TIMain (tiProgram,
               makeProgram,
               getFunDeclsBg) where

import List                     ((\\), 
                                 intersect, 
                                 union)

import Desugar                  (doToExp)

import AHsPretty                (render,
                                 ppAHsDecl,  
                                 ppAHsExp,
                                 ppAHsStmt,
                                 ppAHsGuardedRhs,
                                 ppAHsAlt,
                                 ppAHsName,
                                 ppGAlt)

import AnnotatedHsSyn           -- almost everything


import Representation          (Type (..),
                                 Tyvar (..), 
                                 Tycon (..),
                                 Kind (..),
                                 Pred (..),
                                 Qual (..),
                                 Subst,
                                 Scheme (..),
                                 Assump (..))


import Type                     (apply,
                                 (@@),
                                 Types (..),
                                 quantify,
                                 toScheme,
                                 assumpToPair,
                                 find,
                                 makeAssump,
                                 assumpId)

import Monad                    (zipWithM)

import Diagnostic               (Diagnostic(..), 
                                 withASrcLoc,
                                 makeMsg, 
                                 locMsg, 
                                 dumpDiagnostic,
                                 locSimple, 
                                 simpleMsg)

import Class                    (ClassHierarchy,
                                 entails,
                                 split,
                                 topDefaults,
                                 reduce)

import TIMonad                  (runTI,
                                 getSubst,
                                 getErrorContext,
                                 getClassHierarchy,
                                 withContext,
                                 getKindEnv,
                                 getSigEnv,
                                 dConScheme,
                                 newTVar,
                                 unify,
                                 unifyList,
                                 freshInst,
                                 getModName,
                                 TI)

import HaskellPrelude           (fn,
                                 tBool,
                                 cFractional,
                                 tString,
                                 cNum,
                                 cEnum,
                                 tList,
                                 tChar)

import Utils                    (isSigDecl,
                                 isBindDecl,
                                 fromAHsName,
                                 getDeclName,
                                 groupEquations,
                                 Binding (..),
                                 fst3,
                                 snd3,
                                 trd3)

import FiniteMaps               (FiniteMap,
                                 lookupFM,
                                 mapFM,
                                 toListFM,
                                 listToFM)

import KindInference            (KindEnv, 
                                 kiAHsQualType)

import Rename                   (bindOfId,
                                 IdentTable)

import DependAnalysis           (getBindGroups)

import Maybe                    (fromMaybe)

import TypeUtils                (aHsTypeSigToAssumps,
                                 qualifyAssump)

import TypeSigs                 (SigEnv)

import Env                      (showEnv, Env,
                                 emptyEnv,
                                 lookupEnv,
                                 joinEnv,
                                 joinListEnvs,
                                 unitEnv,
                                 addToEnv,
                                 listToEnv)
                                   
import DeclsDepends             (getDeclDeps)                                

-----------------------------------------------------------------------------

-- a TypeEnv maps identifier names to type schemes
type TypeEnv = Env Scheme

instance Types a => Types (AHsName, a) where
   apply s (x, y) = (x, apply s y)
   tv (_, y) = tv y 

instance Types TypeEnv where
   apply s = mapFM (\k e -> apply s e)
   tv env = tv $ map snd $ toListFM env


tiExpr ::  TypeEnv -> (AHsExp) -> TI ([Pred], TypeEnv, Type)

tiExpr env (AHsVar v)
 = do let sc = case lookupEnv v env of
                  Nothing -> error $ "tiExpr: could not find type scheme for: " ++ 
		                     show v ++ " " ++ showEnv env 
                  Just scheme -> scheme
      (ps :=> t) <- freshInst sc
      return (ps, emptyEnv, t)

tiExpr env (AHsCon conName)
 = do 
      sc <- dConScheme conName
      (ps :=> t) <- freshInst sc
      return (ps, emptyEnv, t)

tiExpr _env (AHsLit l)
 = do (ps,t) <- tiLit l
      return (ps, emptyEnv, t)


tiExpr env expr@(AHsInfixApp e1 e2 e3)
 = withContext 
       (makeMsg "in the infix application" $ render $ ppAHsExp expr) $
       do
       (ps, env1, te1) <- tiExpr env e1 
       (qs, env2, te2) <- tiExpr env e2 
       (rs, env3, te3) <- tiExpr env e3 
       tout      <- newTVar Star
       unify (te1 `fn` (te3 `fn` tout)) te2
       return (ps ++ qs ++ rs, env1 `joinEnv` env2 `joinEnv` env3, tout)

tiExpr env expr@(AHsApp e1 e2)
 = withContext
      (makeMsg "in the application" $ render $ ppAHsExp expr) $
      do
      (ps, env1, te1) <- tiExpr env e1
      (qs, env2, te2) <- tiExpr env e2 
      t           <- newTVar Star
      unify (te2 `fn` t) te1
      return (ps++qs, env1 `joinEnv` env2, t)

-- we need to fix the type to to be in the class
-- cNum, just for cases such as:
-- foo = \x -> -x

tiExpr env expr@(AHsNegApp e)
 = withContext
      (makeMsg "in the negative expression" $ render $ ppAHsExp expr) $
      do
        (ps, env1, te) <- tiExpr env e
        return (IsIn cNum te : ps, env1, te) 

tiExpr env expr@(AHsLambda sloc pats e)
 = withContext
      (locSimple sloc $ "in the lambda expression\n   \\" ++ show pats ++ " -> ...") $
      do
        (ps, envP, ts) <- tiPats pats
        (qs, envE, t)  <- tiExpr (envP `joinEnv` env) e
        return (ps++qs, envE, foldr fn t ts)

tiExpr env expr@(AHsLet decls e)
 = withContext 
       (makeMsg "in the let binding" $ render $ ppAHsExp expr) $
         do
         sigEnv <- getSigEnv
         let bgs = getFunDeclsBg sigEnv decls
         (ps, env1) <- tiSeq tiBindGroup env bgs
         (qs, env2, t) <- tiExpr (env1 `joinEnv` env) e
         -- keep the let bound type assumptions in the environment
         return (ps ++ qs, env1 `joinEnv` env2, t) 

tiExpr env (AHsIf e e1 e2)
 = withContext
      (simpleMsg $ 
      "in the conditional expression\n   if " ++ show e ++ "...") $
      do (ps, env1, t)   <- tiExpr env e
         unify t tBool
         (ps1, env2, t1) <- tiExpr env e1
         (ps2, env3, t2) <- tiExpr env e2
         unify t1 t2
         return (ps++ps1++ps2, env1 `joinEnv` env2 `joinEnv` env3, t1)


tiExpr env (AHsCase e alts)
 = withContext
        (simpleMsg $
            "in the case expression\n   case " ++ show e ++ " of ...") $
        do
        (pse, env1, te)    <- tiExpr env e
        psastsAlts     <- mapM (tiAlt env) alts
        let pstsPats = map fst3 psastsAlts
        let psPats   = concatMap fst pstsPats
        let tsPats   = map snd pstsPats
        let pstsEs   = map trd3 psastsAlts
        let psEs     = concatMap fst pstsEs
        let tsEs     = map snd pstsEs
        let envAlts  = joinListEnvs $ map snd3 psastsAlts
        unifyList (te:tsPats)
        unifyList tsEs
        -- the list of rhs alternatives must be non-empty
        -- so it is safe to call head here
        return (pse ++ psPats ++ psEs, env1 `joinEnv` envAlts, head tsEs)


tiExpr env (AHsDo stmts)
   = do
        let newExp = doToExp stmts
        withContext (simpleMsg "in a do expression") 
                    (tiExpr env newExp)

-- tuples can't be empty, () is not a tuple
tiExpr env tuple@(AHsTuple exps@(_:_))
   = withContext                
        (makeMsg "in the tuple" $ render $ ppAHsExp tuple) $
        do
           psasts <- mapM (tiExpr env) exps
           let typeList = map trd3 psasts
           let preds = concatMap fst3 psasts
           let env1 = joinListEnvs $ map snd3 psasts
           return (preds, env1, TTuple typeList)

-- special case for the empty list
tiExpr _env (AHsList [])
   = do
        v <- newTVar Star
        return ([], emptyEnv, TAp tList v)

-- non empty list
tiExpr env expr@(AHsList exps@(_:_))
   = withContext (makeMsg "in the list " $ render $ ppAHsExp expr) $
        do
        psasts <- mapM (tiExpr env) exps
        let typeList = map trd3 psasts
        unifyList typeList 
        let preds = concatMap fst3 psasts
        let env1 = joinListEnvs $ map snd3 psasts
        return (preds, env1, TAp tList (head typeList)) 


        
tiExpr env (AHsParen e)
   = tiExpr env e 

-- e1 :: a -> b
-- e2 :: a
-- e1 e2 :: b

{- XXX: we don't push error contexts for some cases, e.g.
   AHsLeftSection -}
tiExpr env (AHsLeftSection e1 e2)
   = do
        (e1Ps, envE1, e1T) <- tiExpr env e1
        (e2Ps, envE2, e2T) <- tiExpr env e2
        tv          <- newTVar Star
        unify e1T (e2T `fn` tv)
        return (e1Ps ++ e2Ps, envE1 `joinEnv` envE2, tv) 


-- I know this looks weird but it appears to be correct 
-- e1 :: b
-- e2 :: a -> b -> c 
-- e1 e2 :: a -> c

tiExpr env (AHsRightSection e1 e2)
   = do
        (e1Ps, envE1, e1T) <- tiExpr env e1
        (e2Ps, envE2, e2T) <- tiExpr env e2
        tv1         <- newTVar Star
        tv2         <- newTVar Star
        unify e2T (tv1 `fn` (e1T `fn` tv2))
        return (e1Ps ++ e2Ps, envE1 `joinEnv` envE2, tv1 `fn` tv2) 

tiExpr env (AHsRecConstr _ _)
   = error $ "tiExpr env (AHsRecConstr _ _): not implemented"

tiExpr env (AHsRecUpdate _ _)
   = error $ "tiExpr env (AHsRecUpdate _ _): not implemented"

tiExpr env (AHsEnumFrom e)
   = do
        (ePs, envE, eT) <- tiExpr env e
        return (IsIn cEnum eT : ePs, envE, TAp tList eT)

tiExpr env (AHsEnumFromTo e1 e2)
   = do
        (e1Ps, e1Env, e1T) <- tiExpr env e1
        (e2Ps, e2Env, e2T) <- tiExpr env e2
        unify e1T e2T
        return (IsIn cEnum e1T : IsIn cEnum e2T : (e1Ps ++ e2Ps), 
                e1Env `joinEnv` e2Env, 
                TAp tList e1T)

tiExpr env (AHsEnumFromThen e1 e2)
   = do
        (e1Ps, e1Env, e1T) <- tiExpr env e1
        (e2Ps, e2Env, e2T) <- tiExpr env e2
        unify e1T e2T
        return (IsIn cEnum e1T : IsIn cEnum e2T : (e1Ps ++ e2Ps), 
                e1Env `joinEnv` e2Env, 
                TAp tList e1T)

tiExpr env (AHsEnumFromThenTo e1 e2 e3)
   = do
        (e1Ps, e1Env, e1T) <- tiExpr env e1
        (e2Ps, e2Env, e2T) <- tiExpr env e2
        (e3Ps, e3Env, e3T) <- tiExpr env e3
        unifyList [e1T,e2T,e3T]
        return (IsIn cEnum e1T : IsIn cEnum e2T : IsIn cEnum e3T : (e1Ps ++ e2Ps ++ e3Ps), 
                e1Env `joinEnv` e2Env `joinEnv` e3Env, 
                TAp tList e1T)

tiExpr env (AHsListComp e stmts)
   = do
        psEnv <- tiStmts env stmts
        let stmtsPs = fst psEnv
        let stmtsEnv = snd psEnv 
        (ePs, eEnv, eT) <- tiExpr (stmtsEnv `joinEnv` env) e
        return (stmtsPs ++ ePs, eEnv `joinEnv` stmtsEnv, TAp tList eT)

-- This should be desugared already
-- e :: t   ----> let {v::t; v=e} in v
tiExpr env (AHsExpTypeSig _sloc e qt)
   = error $ "tiExpr: unexpected sugared explicitly typed expression " ++ show e

tiExpr _env e
   = error $ "tiExpr: not implemented for: " ++ show e

--------------------------------------------------------------------------------

tiStmts ::  TypeEnv -> [(AHsStmt)] -> TI ([Pred], TypeEnv)

tiStmts = tiStmtsAcc [] emptyEnv 

tiStmtsAcc ::   [Pred] -> TypeEnv -> TypeEnv -> [(AHsStmt)] -> TI ([Pred], TypeEnv)
tiStmtsAcc predAcc envAcc _ [] 
   = return (predAcc, envAcc)

tiStmtsAcc predAcc envAcc env (s:ss)
   = do
        (newPs, newEnv) <- tiStmt (envAcc `joinEnv` env) s
        tiStmtsAcc (newPs ++ predAcc) (newEnv `joinEnv` envAcc) env ss
 
tiStmt :: TypeEnv -> (AHsStmt) -> TI ([Pred], TypeEnv)

-- with lists: 
-- x <- xs
-- xs :: [a]
-- x :: a 

tiStmt env expr@(AHsGenerator srcLoc pat e)
   = withContext
        (locMsg srcLoc "in the generator " $ render $ ppAHsStmt expr) $
        do
        (ePs, eEnv, eT) <- tiExpr env e
        (patPs, patEnv, patT) <- tiPat pat
        unify eT (TAp tList patT)
        return (ePs ++ patPs, eEnv `joinEnv` patEnv)

tiStmt env stmt@(AHsQualifier e)
   = withContext (makeMsg "in " $ render $ ppAHsStmt stmt) $
        do
        (ePs, eEnv, eT) <- tiExpr env e
        unify eT tBool
        return (ePs, eEnv)

tiStmt env stmt@(AHsLetStmt decls)
   = withContext 
         (makeMsg "in let statement" $ render $ ppAHsStmt stmt) $
         do 
         sigEnv <- getSigEnv
         let bgs = getFunDeclsBg sigEnv decls
         tiSeq tiBindGroup env bgs

--------------------------------------------------------------------------------

tiAlt ::  TypeEnv -> (AHsAlt) -> TI (([Pred], Type), TypeEnv, ([Pred], Type))

tiAlt env alt@(AHsAlt sloc pat gAlts wheres)
   = withContext (locMsg sloc "in the alternative" $ render $ ppAHsAlt alt) $
        do
        sigEnv <- getSigEnv
        let wheresBgs = getFunDeclsBg sigEnv wheres
        (psPat, envPat, patT) <- tiPat pat
        (wheresPs, wheresEnv) <- tiSeq tiBindGroup (envPat `joinEnv` env) wheresBgs
        (psAlt, envAlt, tAlt) <- tiGuardedAlts (wheresEnv `joinEnv` envPat  `joinEnv` env) gAlts
        -- not sure about the use of wheresPs below
        return ((psPat, patT), envAlt `joinEnv` wheresEnv, (wheresPs ++ psAlt, tAlt))
                       

tiGuardedAlts env (AHsUnGuardedAlt e)
   = tiExpr env e

-- basically the same as AHsGuardedRhss
tiGuardedAlts env (AHsGuardedAlts gAlts)
   = withContext (simpleMsg "in guarded alternatives") $
     do 
        psEnvTs <- mapM (tiGuardedAlt env) gAlts 
        let guardsPsEnvTs = map fst psEnvTs
        let rhsPsEnvTs    = map snd psEnvTs
        let guardPs    = concatMap fst3 guardsPsEnvTs
        let rhsPs      = concatMap fst3 rhsPsEnvTs
        let guardTs    = map trd3 guardsPsEnvTs
        let rhsTs      = map trd3 rhsPsEnvTs
        let guardEnv   = joinListEnvs $ map snd3 guardsPsEnvTs
        let rhsEnv      = joinListEnvs $ map snd3 rhsPsEnvTs 
        unifyList (tBool:guardTs)                -- make sure these are all booleans
        unifyList rhsTs
        return (guardPs ++ rhsPs, guardEnv `joinEnv` rhsEnv, head rhsTs)


-- basically the same as tiGuardedRhs
tiGuardedAlt ::  TypeEnv  -> (AHsGuardedAlt) -> TI (([Pred], TypeEnv, Type), ([Pred], TypeEnv, Type))
tiGuardedAlt env gAlt@(AHsGuardedAlt sloc eGuard eRhs)
   = withContext (locMsg sloc "in the guarded alternative" $ render $ ppGAlt gAlt) $
     do
        (guardPs, guardEnv, guardT) <- tiExpr env eGuard
        (rhsPs, rhsEnv, rhsT)     <- tiExpr env eRhs 
        return ((guardPs, guardEnv, guardT), (rhsPs, rhsEnv, rhsT))


-----------------------------------------------------------------------------

-- NOTE: there's no need to do tiDecl with error contexts as the unification
--       doesn't happen until after this function is finished with
tiDecl ::  TypeEnv -> AHsDecl -> TI ([Pred], TypeEnv, Type)
tiDecl env (AHsPatBind sloc pat rhs wheres)
   = do
        sigEnv <- getSigEnv
        let wheresBgs = getFunDeclsBg sigEnv wheres
        (ps, env1)     <- tiSeq tiBindGroup env wheresBgs 
        (qs, env2, t)  <- tiRhs (env1 `joinEnv` env) rhs
        return (ps ++ qs, env1 `joinEnv` env2, t)


tiDecl env (AHsFunBind matches)
   = -- withContext (locSimple sloc "in a function binding") $
     do
        psEnvts <- mapM (tiMatch env) matches
        let ps' = concatMap fst3 psEnvts
        let ts' = map trd3 psEnvts
        let matchesEnv = joinListEnvs $ map snd3 psEnvts
        unifyList ts'  -- all matches must have the same type
        return (ps', matchesEnv, head ts') 

declDiagnostic ::  (AHsDecl) -> Diagnostic
declDiagnostic decl@(AHsPatBind sloc pat _ _) 
    = locMsg sloc "in the pattern binding" $ render $ ppAHsDecl decl 
declDiagnostic decl@(AHsFunBind matches)
    = locMsg matchLoc "in the function binding" $ render $ ppAHsDecl decl 
    where
    matchLoc
       = case matches of 
            [] -> bogusASrcLoc  -- this should never happen, there should be no empty match list
            (m:_) -> case m of
                        AHsMatch sloc _name _pats _rhs _decls -> sloc


tiDeclTop ::  TypeEnv -> AHsDecl -> Type -> TI ([Pred], TypeEnv)
tiDeclTop env decl t
   = do psEnvT <- tiDecl env decl 
        unify t (trd3 psEnvT)
        return (fst3 psEnvT, snd3 psEnvT)
 
--------------------------------------------------------------------------------

tiMatch ::  TypeEnv -> (AHsMatch) -> TI ([Pred], TypeEnv, Type)
tiMatch env (AHsMatch sloc funName pats rhs wheres)
   = withContext (locMsg sloc "in" $ render $ ppAHsName funName) $
     do
        -- pats must be done before wheres b/c variables bound in patterns
        -- may be referenced in the where clause
        (patsPs, patsEnv, patsTs) <- tiPats pats
        sigEnv <- getSigEnv
        let wheresBgs = getFunDeclsBg sigEnv wheres 
        (wheresPs, wheresEnv) <- tiSeq tiBindGroup (patsEnv `joinEnv` env) wheresBgs  
        (rhsPs, rhsEnv, rhsT)   <- tiRhs (wheresEnv `joinEnv` patsEnv `joinEnv` env) rhs
        return (wheresPs++patsPs++rhsPs, rhsEnv `joinEnv` wheresEnv, foldr fn rhsT patsTs) 

-----------------------------------------------------------------------------


tiRhs env (AHsUnGuardedRhs e)
   = tiExpr env e


tiRhs env (AHsGuardedRhss rhss)
   = do
        psEnvTs <- mapM (tiGuardedRhs env) rhss
        let guardsPsEnvTs = map fst psEnvTs
        let rhsPsEnvTs    = map snd psEnvTs
        let guardPs    = concatMap fst3 guardsPsEnvTs
        let rhsPs      = concatMap fst3 rhsPsEnvTs 
        let guardTs    = map trd3 guardsPsEnvTs
        let rhsTs      = map trd3 rhsPsEnvTs
        let guardEnv    = joinListEnvs $ map snd3 guardsPsEnvTs
        let rhsEnv      = joinListEnvs $ map snd3 rhsPsEnvTs 
        unifyList (tBool:guardTs)                -- make sure these are all booleans
        unifyList rhsTs
        return (guardPs ++ rhsPs, guardEnv `joinEnv` rhsEnv, head rhsTs)
        

tiGuardedRhs ::  TypeEnv -> (AHsGuardedRhs) -> TI (([Pred], TypeEnv, Type), ([Pred], TypeEnv, Type))
tiGuardedRhs env gRhs@(AHsGuardedRhs sloc eGuard eRhs)
   = withContext (locMsg sloc "in the guarded right hand side" $ render $ ppAHsGuardedRhs gRhs) $
     do
        (guardPs, guardEnv, guardT) <- tiExpr env eGuard
        (rhsPs, rhsEnv, rhsT)       <- tiExpr env eRhs
        return ((guardPs, guardEnv, guardT), (rhsPs, rhsEnv, rhsT)) 

        

-----------------------------------------------------------------------------

-- type check explicitly typed bindings

type Expl = (Scheme, AHsDecl)


tiExpl ::  TypeEnv -> Expl -> TI ([Pred], TypeEnv)
tiExpl env (sc, decl)
 = withContext 
       (makeMsg "in the explicitly typed" $ render $ ppAHsDecl decl) $
    do 
       cHierarchy <- getClassHierarchy
       (qs :=> t) <- freshInst sc
       (ps, env') <- tiDeclTop env decl t
       s          <- getSubst
       let qs'     = apply s qs
           t'      = apply s t
           ps'     = [ p | p <- apply s ps, not (entails cHierarchy qs' p) ]
           fs      = tv (apply s env) 
           gs      = tv t' \\ fs
           (ds,rs) = reduce cHierarchy fs gs ps'
           sc'     = quantify gs (qs':=>t')
       if sc /= sc' then
           error $ "signature too general" ++ "\n" ++ show sc ++ "\n" ++ show sc'
        else if not (null rs) then
           error "context too weak"
        else
           return (ds, env')

-----------------------------------------------------------------------------

-- type check implicitly typed bindings

type Impl = AHsDecl

restricted   :: [Impl] -> Bool
restricted bs 
   = any isSimpleDecl bs
   where 
   isSimpleDecl :: (AHsDecl) -> Bool
   isSimpleDecl (AHsPatBind _sloc _pat _rhs _wheres) = True
   isSimpleDecl _ = False

tiImpls env bs 
 = do 
      cHierarchy <- getClassHierarchy
      ts <- mapM (\_ -> newTVar Star) bs
      let 
          is      = getImplsNames bs
          scs     = map toScheme ts
          newEnv1 = listToEnv $ map assumpToPair $ zipWith makeAssump is scs 
          env'    = newEnv1 `joinEnv` env 
      pssEnvs <- sequence (zipWith (tiDeclTop env') bs ts)
      let pss  = map fst pssEnvs
      let envs = map snd pssEnvs
      s   <- getSubst
      let ps'     = apply s (concat pss)
          ts'     = apply s ts
          fs      = tv (apply s env)  
          vss     = map tv ts'
          gs      = foldr1 union vss \\ fs
          (ds,rs) = reduce cHierarchy fs (foldr1 intersect vss) ps'
      if restricted bs then
          let gs'  = gs \\ tv rs
              scs' = map (quantify gs' . ([]:=>)) ts'
              newEnv2 = listToEnv $ map assumpToPair $ zipWith makeAssump is scs'
          in return (ds++rs, (joinListEnvs envs) `joinEnv` newEnv2)
        else
          let scs' = map (quantify gs . (rs:=>)) ts'
              newEnv3 = listToEnv $ map assumpToPair $ zipWith makeAssump is scs'
          in return (ds, (joinListEnvs envs) `joinEnv` newEnv3)  

getImplsNames :: [Impl] -> [AHsName]
getImplsNames impls
   = map getDeclName impls


-----------------------------------------------------------------------------


-- this is different than the "Typing Haskell in Haskell" paper
-- we do not further sub-divide the implicitly typed declarations in
-- a binding group.
type BindGroup = ([Expl], [Impl])

tiBindGroup env (es, is)
   = do 
     modName <- getModName
     let env1 = listToEnv [assumpToPair $ getDeclName decl :>: sc | (sc,decl) <- es ]
     (implPs, implEnv) <- tiImpls (env1 `joinEnv` env) is
     explPsEnv   <- mapM (tiExpl (implEnv `joinEnv` env1 `joinEnv` env)) es 
     let explPs = concatMap fst explPsEnv
     let explEnv = joinListEnvs $ map snd explPsEnv
     return (implPs ++ explPs, env1 `joinEnv` explEnv `joinEnv` implEnv)

tiSeq ti env []
 = return ([],emptyEnv)
tiSeq ti env (bs:bss)
 = do (ps,env1)  <- ti env bs
      (qs,env2) <- tiSeq ti (env1 `joinEnv` env) bss
      return (ps++qs, env2 `joinEnv` env1)

-----------------------------------------------------------------------------

-- create a Program structure from a list of decls and
-- type sigs. Type sigs are associated with corresponding
-- decls if they exist

getFunDeclsBg :: SigEnv -> [AHsDecl] -> Program
getFunDeclsBg sigEnv decls
   = makeProgram sigEnv equationGroups
   where
   equationGroups :: [[AHsDecl]]
   equationGroups = getBindGroups bindDecls getDeclName getDeclDeps
   -- just make sure we only deal with bindDecls and not others
   bindDecls = collectBindDecls decls

makeProgram :: SigEnv -> [[AHsDecl]] -> Program
makeProgram sigEnv groups
   = map (makeBindGroup sigEnv ) groups


-- reunite decls with their signatures, if ever they had one
 
makeBindGroup :: SigEnv -> [AHsDecl] -> BindGroup
makeBindGroup sigEnv decls
   = (exps, impls)
   where
   (exps, impls) = makeBindGroup' sigEnv decls
makeBindGroup' _ [] = ([], [])
makeBindGroup' sigEnv (d:ds)
   = case lookupFM sigEnv funName of
        Nothing -- no type sig for this equation
           -> (restExpls, d:restImpls)
        Just scheme  -- this one has a type sig
           -> ((scheme, d):restExpls, restImpls) 
   where
   funName = getDeclName d
   (restExpls, restImpls) = makeBindGroup' sigEnv ds

collectBindDecls :: [AHsDecl] ->  [AHsDecl]
collectBindDecls = filter isBindDecl

-----------------------------------------------------------------------------

type Program = [BindGroup]

tiProgram ::  AModule -> SigEnv -> KindEnv -> ClassHierarchy -> TypeEnv -> TypeEnv -> Program -> TypeEnv 
tiProgram modName sEnv kt h dconsEnv env bgs = runTI dconsEnv h kt sEnv modName $
  do (ps, env1) <- tiSeq tiBindGroup env bgs 
     s         <- getSubst
     let ([], rs) = split h [] (apply s ps)
     case topDefaults h rs of
       Just s' -> return (apply (s'@@s) env1) 
       Nothing -> error "top-level ambiguity"


--------------------------------------------------------------------------------

-- Typing Literals 

tiLit            :: AHsLiteral -> TI ([Pred],Type)
tiLit (AHsChar _) = return ([], tChar)
tiLit (AHsInt _)  
   = do 
        v <- newTVar Star
        return ([IsIn cNum v], v)

tiLit (AHsFrac _) 
   = do 
        v <- newTVar Star
        return ([IsIn cFractional v], v)

tiLit (AHsString _)  = return ([], tString)

--------------------------------------------------------------------------------

-- Typing Patterns

tiPat :: AHsPat -> TI ([Pred], Env Scheme, Type)

tiPat (AHsPVar i) 
   = do 
        v <- newTVar Star
        let newAssump = assumpToPair $ makeAssump i (toScheme v)
        return ([], unitEnv newAssump, v)

tiPat (AHsPLit l) 
   = do 
        (ps, t) <- tiLit l
        return (ps, emptyEnv, t)

-- this is for negative literals only
-- so the pat must be a literal
-- it is safe not to make any predicates about
-- the pat, since the type checking of the literal
-- will do this for us
tiPat (AHsPNeg pat)
   = tiPat pat

tiPat (AHsPInfixApp pLeft conName pRight)
   = do
        (psLeft, envLeft, tLeft)    <- tiPat pLeft
        (psRight, envRight, tRight) <- tiPat pRight
        t'                         <- newTVar Star
        sc <- dConScheme conName
        (qs :=> t) <- freshInst sc
        unify t (tLeft `fn` (tRight `fn` t'))
        return (psLeft ++ psRight, envLeft `joinEnv` envRight, t')

tiPat (AHsPApp conName pats)
   = do
        (ps,env,ts) <- tiPats pats
        t'         <- newTVar Star
        sc <- dConScheme conName
        (qs :=> t) <- freshInst sc
        unify t (foldr fn t' ts)
        return (ps++qs, env, t') 

tiPat tuple@(AHsPTuple pats)
   = do
        (ps, env, ts) <- tiPats pats 
        return (ps, env, TTuple ts) 

tiPat (AHsPList [])
   = do
        v <- newTVar Star
        return ([], emptyEnv, TAp tList v)

tiPat (AHsPList pats@(_:_))
   = do
        (ps, env, ts) <- tiPats pats
        unifyList ts
        return (ps, env, TAp tList (head ts))

tiPat AHsPWildCard
 = do v <- newTVar Star
      return ([], emptyEnv, v)

tiPat (AHsPAsPat i pat)
 = do (ps, env, t) <- tiPat pat 
      let newAssump = makeAssump i $ toScheme t
      let newEnv = addToEnv (assumpToPair newAssump) env
      return (ps, newEnv, t)

tiPat (AHsPIrrPat p)
 = tiPat p

tiPat (AHsPParen p)
 = tiPat p 

tiPats :: [AHsPat] -> TI ([Pred], Env Scheme, [Type])
tiPats pats =
  do psEnvts <- mapM tiPat pats
     let ps = [ p | (ps,_,_) <- psEnvts, p<-ps ]
         env = joinListEnvs $ map snd3 psEnvts
         ts = [ t | (_,_,t) <- psEnvts ]
     return (ps, env, ts)
