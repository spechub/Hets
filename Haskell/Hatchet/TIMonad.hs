{-------------------------------------------------------------------------------

        Copyright:              Mark Jones and The Hatchet Team 
                                (see file Contributors)

        Module:                 TIMonad

        Description:            A monad to support type inference, in 
                                particular for threading the type environment
                                through the type inference code.

        Primary Authors:        Mark Jones, Bernie Pope and Bryn Humberstone

        Notes:                  See the file License for license information

                                Large parts of this module were derived from
                                the work of Mark Jones' "Typing Haskell in
                                Haskell", (http://www.cse.ogi.edu/~mpj/thih/)

-------------------------------------------------------------------------------}

module TIMonad (TI, 
                inst,
                runTI,
                getErrorContext, 
                getErrorStatus,
                setError, 
                pushErrorContext, 
                withContext,
                popErrorContext,
                -- DCAssumpTable,
                getSubst,
                getClassHierarchy,
                getKindEnv,
                getSigEnv,
                unify,
                freshInst,
                dConScheme,
                unifyList,
                getModName,
                newTVar) where

import AnnotatedHsSyn           (AHsName (..),
                                 AHsIdentifier (..),
                                 AModule(AModule),
                                 ASrcLoc(..))

import Diagnostic               (Diagnostic(..), 
                                 dumpDiagnostic,
                                 TypeError (..),
                                 typeError)

import Representation           (Type (..),
                                 Tyvar (..),
                                 Tycon (..),
                                 Kind (..),
                                 Qual (..),
                                 Pred (..),
                                 Subst,
                                 Scheme (..),
                                 Assump)

import Type                     ((@@),
                                 Types (..),
                                 Instantiate (..),
                                 nullSubst,
                                 mgu)

import Class                    (ClassHierarchy)

import FiniteMaps               (lookupFM,
                                 toListFM,
                                 listToFM,
                                 FiniteMap) 


import KindInference            (KindEnv)

import TypeSigs                 (SigEnv)

import Env                      (Env,
                                 lookupEnv)

import PPrint                   (pretty)

--------------------------------------------------------------------------------

-- type DCAssumpTable = FiniteMap AHsName Assump

newtype TI a = TI (State -> (a, State))

data State = 
   State {
      subst :: Subst,
      varnum :: Int,   -- to keep our supply fresh
      env  :: Env Scheme,
      ch    :: ClassHierarchy,
      kinds :: KindEnv,
      sigs  :: SigEnv,
      diagnostics :: [Diagnostic],   -- list of information that might help diagnosis
      inerror :: Bool,        -- True means that an error has happened
      modName :: AModule        -- the name of the current module 
   }

-- dcat == data constructor assump table

instance Monad TI where
    return a
        = TI (\state -> (a, state))    -- maintain state and return value

    TI comp >>= fun
        = TI (\state -> let (result, newState) = comp state
                            TI comp' = fun result
                        in
                        if inerror newState then (undefined, newState)
                                            else comp' newState)
          -- we only continue with the calculations if there isn't an error


runTI     :: Env Scheme-> ClassHierarchy -> KindEnv -> SigEnv -> AModule -> TI a -> a
runTI env' ch' kt' st' mod' (TI c)
   = result
   where (result,_) = c (State {subst = nullSubst, 
                                varnum = 0, 
                                env = env',
                                ch = ch',
                                kinds = kt',
                                sigs = st',
                                diagnostics = [],
                                inerror = False,
                                modName = mod'})


{- push some information (like function calls) onto the front of diagnostics -}
pushErrorContext :: Diagnostic -> TI ()
pushErrorContext info
   = TI (\state ->
            let curr = diagnostics state
            in ((), state {diagnostics = info:curr})
        )

{- pop off top information from diagnostics -}
popErrorContext :: TI Diagnostic
popErrorContext
   = TI (\state ->
            case diagnostics state of
                 (top:rest)  -> (top, state {diagnostics = rest})
                 []          -> error "Attempt to popErrorContext from empty stack!"
        )


{- given a diagnostic and a computation to take place inside the TI-monad,
   run the computation but during it have the diagnostic at the top of the 
   stack -}
withContext :: Diagnostic -> TI a -> TI a
withContext diagnostic comp
   = do 
       pushErrorContext diagnostic
       result <- comp
       popErrorContext 
       return result



{- a common theme is just returning one of the members of the state, so
   this function helps with this -}
select :: (State -> a) -> TI a
select selector = TI (\state -> (selector state, state))

getErrorContext :: TI [Diagnostic]
getErrorContext = select diagnostics

getErrorStatus :: TI Bool
getErrorStatus = select inerror 

getSubst :: TI Subst
getSubst = select subst

getDConsTypeEnv :: TI (Env Scheme) 
getDConsTypeEnv = select env 

getClassHierarchy  :: TI ClassHierarchy
getClassHierarchy = select ch

getKindEnv :: TI (KindEnv)
getKindEnv = select kinds

getSigEnv :: TI SigEnv
getSigEnv = select sigs

getModName :: TI AModule
getModName = select modName

setError :: TI ()
setError = TI (\state -> ((), state{inerror = True}))

dConScheme :: AHsName -> TI Scheme 
dConScheme conName
   = do
        env <- getDConsTypeEnv 
        case lookupEnv conName env of
           Nothing -> error $ "dConScheme: constructor not found: " ++ show conName ++
                              "\nin this environment:\n" ++ show env
           Just s -> return s

unify      :: Type -> Type -> TI ()
unify t1 t2 = do s <- getSubst
                 let t1' = apply s t1
                     t2' = apply s t2
                 case mgu t1' t2' of
                   Just u  -> extSubst u
                   Nothing -> do
                              diagnosis <- getErrorContext
                              typeError (Unification $ "attempted to unify " ++ 
                                                       pretty t1' ++
                                                       " with " ++
                                                       pretty t2')
                                        diagnosis

unifyList :: [Type] -> TI ()
unifyList [] = return ()
unifyList [_] = return ()
unifyList (t1:t2:ts)
   = do
       unify t1 t2
       unifyList (t2:ts)


trim       :: [Tyvar] -> TI ()
trim vs     = TI (\state ->
                     let s' = [(v,t) | (v,t) <- toListFM (subst state), v `elem` vs]
                         force = length (tv (map snd s'))
                     in force `seq` ((), state {subst = listToFM s'})
                 )


extSubst   :: Subst -> TI ()
extSubst s' = TI (\state -> ((), state {subst = s'@@(subst state)}))

newTVar    :: Kind -> TI Type
newTVar k   = TI (\state -> 
                   let n = varnum state
                       ident = AUnQual $ AHsIdent $ "v" ++ show n
                       v = Tyvar ident k
                   in  (TVar v, state{varnum = n+1})
                 )

freshInst               :: Scheme -> TI (Qual Type)
freshInst (Forall ks qt) = do ts <- mapM newTVar ks
                              return (inst ts qt)
