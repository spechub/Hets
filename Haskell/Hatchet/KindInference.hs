{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 KindInference

        Description:            Kind inference of data and class declarations.
                                Based very closely on type inference.

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module KindInference (kiModule, 
                      KindEnv, 
                      kiAHsQualType,
                      kindOf,
                      ) where 

import Representation   (Kind (..),
                         Kindvar (..)) 

import Env  (Env,
             emptyEnv,
             unitEnv,
             lookupEnv,
             joinEnv,
             joinListEnvs,
             listToEnv,
             envToList,
             showEnv,
             mapEnv
            ) 

import AnnotatedHsSyn         -- XXX need to say exactly what is imported
            
import Utils (isQualified,
              getDeclName,
              isSigDecl)

import List                             (nub)

import DependAnalysis                   (getBindGroups)

--------------------------------------------------------------------------------

-- the many interesting types and classes

type KindEnv = Env Kind

type Subst = [(Kindvar, Kind)]

nullSubst :: Subst
nullSubst = []

class Kinds a where
   vars :: a -> [Kindvar]
   apply :: Subst -> a -> a

instance Kinds Kind where
   vars Star = []
   vars (KVar kindvar) = [kindvar]
   vars (kind1 `Kfun` kind2) = vars kind1 ++ vars kind2 

   apply s Star = Star 
   apply s (KVar kindvar) 
      = case lookup kindvar s of
           Just k -> k
           Nothing -> KVar kindvar
   apply s (kind1 `Kfun` kind2)
      = (apply s kind1) `Kfun` (apply s kind2)

instance Kinds a => Kinds [a] where
   vars = nub . concatMap vars 
   apply s = map (apply s)

instance Kinds a => Kinds (b, a) where
   apply s (x, y) = (x, apply s y)
   vars (x, y) = vars y

instance Kinds KindEnv where
   apply s = mapEnv (\key el -> apply s el) 
   vars env = vars $ map snd $ envToList env


--------------------------------------------------------------------------------

-- unification

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = [(u, apply s1 k) | (u, k) <- s2] ++ s1


-- mgu :: Kind -> Kind -> Maybe Subst

-- can return either a substitution or a string
mgu :: Kind -> Kind -> Either Subst String
mgu Star Star = Left nullSubst
mgu (k1 `Kfun` k2) (k3 `Kfun` k4)
   = case mgu k1 k3 of
        Right errorMsg 
           -> Right errorMsg
        Left s1 
           -> case mgu (apply s1 k2) (apply s1 k4) of 
                 Right errorMsg -> Right errorMsg
                 Left s2 -> Left $ s2 `composeSubst` s1

mgu (KVar u) k = varBind u k
mgu k (KVar u) = varBind u k
mgu k1 k2 = Right $ "attempt to unify these two kinds: " ++ show k1 ++ ", " ++ show k2

varBind :: Kindvar -> Kind -> Either Subst String
varBind u k
   | k == KVar u = Left nullSubst
   | u `elem` vars k = Right $ "occurs check failed in kind inference: " ++ 
                               show u ++ ", " ++ show k  
   | otherwise = Left [(u, k)]


--------------------------------------------------------------------------------

-- The kind inference monad

newtype KI a = KI (State -> (a, State))

data State =
   State {
      env :: KindEnv,     -- the environment of kind assumptions 
      subst :: Subst,     -- the current substitution
      varnum :: Int       -- to keep our supply fresh
   }

instance Monad KI where
    return a
        = KI (\state -> (a, state)) 

    KI comp >>= fun
        = KI (\state -> let (result, newState) = comp state
                            KI comp' = fun result
                        in
                        comp' newState)

--------------------------------------------------------------------------------

-- useful operations in the inference monad

runKI     :: KindEnv -> KI a -> (a, State)
runKI kindEnv (KI comp)
   = (result, newState)
   where 
   (result,newState) 
      = comp (State {env = kindEnv, 
                     subst = nullSubst, 
                     varnum = 0})

select :: (State -> a) -> KI a
select selector = KI (\state -> (selector state, state))

getSubst :: KI Subst
getSubst = select subst

getVarNum :: KI Int
getVarNum = select varnum

getEnv :: KI (KindEnv)
getEnv = select env

getEnvVars :: KI [Kindvar]
getEnvVars 
   = do e <- select env
        return $ vars e 

incVarNum :: KI ()
incVarNum = KI (\state -> let oldVarNum = varnum state
                          in ((), state {varnum = oldVarNum + 1}))

unify :: Kind -> Kind -> KI ()
unify k1 k2
   = do s <- getSubst
        case mgu (apply s k1) (apply s k2) of
           Left newSubst  -> extendSubst newSubst 
           Right errorMsg -> error errorMsg 


extendSubst :: Subst -> KI ()
extendSubst s = KI (\state -> let oldSub = subst state
                              in ((), state {subst = s `composeSubst` oldSub}))
newKindVar :: KI Kind
newKindVar 
   = do n <- getVarNum
        incVarNum
        return (KVar (Kindvar $ "k" ++ show n))

lookupKindEnv :: AHsName -> KI (Maybe Kind)
lookupKindEnv name
   = do env <- getEnv
        return $ lookupEnv name env 

extendEnv :: KindEnv -> KI ()
extendEnv newEnv
   = KI (\state -> let oldEnv = env state
                   in ((), state {env = oldEnv `joinEnv` newEnv}))
    
applySubstToEnv :: Subst -> KI ()
applySubstToEnv subst 
   = KI (\state -> let oldEnv    = env state
                   in ((), state {env = apply subst oldEnv}))

envVarsToStars :: KI ()
envVarsToStars 
   = do vars <- getEnvVars
        let varsToStarSubst = map (\v -> (v, Star)) vars   -- clobber all remaining variables to stars
        applySubstToEnv varsToStarSubst
 

--------------------------------------------------------------------------------

-- kind inference proper
-- this is what gets called from outside of this module
kiModule :: KindEnv -> [AHsDecl] -> KindEnv
kiModule inputEnv classAndDataDecls
   = env newState 
   where
   (_, newState) = runKI inputEnv $ mapM_ kiKindGroup kindGroups
   kindGroups = map declsToKindGroup depGroups
   depGroups = getDataAndClassBg classAndDataDecls 

kiKindGroup :: KindGroup -> KI () 
kiKindGroup (classDecls, heads, context, dataBodies, classBodies)
   = do
        mapM_ kiClassDecl classDecls
        mapM_ kiTyConDecl heads
        mapM_ kiAsst context
        dataBodyKinds <- mapM (kiType True) dataBodies        -- vars must be seen previously here (hence True)
        mapM_ (\k -> unify k Star) dataBodyKinds
        classBodyKinds <- mapM (kiQualType False) classBodies  -- vars may not have been seen previously here (hence False)
        mapM_ (\k -> unify k Star) classBodyKinds
        currentSubst <- getSubst
        applySubstToEnv currentSubst
        envVarsToStars
        

kiTyConDecl :: DataDeclHead -> KI () 
kiTyConDecl (tyconName, args)
   = do
        argKindVars <- mapM newNameVar args
        let tyConKind = foldr Kfun Star $ map snd argKindVars
        let newEnv = listToEnv $ [(tyconName, tyConKind)] ++ argKindVars
        extendEnv newEnv

kiClassDecl :: AHsAsst -> KI ()
kiClassDecl (className, argName)
   = do
        varKind <- newKindVar 
        let newEnv = listToEnv $ [(className, varKind), (argName, varKind)]
        extendEnv newEnv

-- here we expext the classname to be already defined and should be in the
-- environment, we do not require that the variables will be defined
kiAsst :: AHsAsst -> KI Kind
kiAsst (className, argName)
   = do classKind <- lookupKindEnv className
        case classKind of
           Nothing -> error $ "kiAsst: could not find kind information for class: " ++ show className
           Just ck -> do argKind <- lookupKindEnv argName
                         case argKind of
                            Nothing -> do varKind <- newKindVar
					  extendEnv $ unitEnv (argName, varKind)
                                          unify ck varKind
                                          return ck 
                            Just ak -> do unify ck ak
                                          return ck
                                       
kiQualType :: Bool -> AHsQualType -> KI Kind
kiQualType varExist (AHsQualType cntxt t)
   = do mapM_ kiAsst cntxt
        kiType varExist t
kiQualType varExist (AHsUnQualType t)
   = kiType varExist t


-- boolean arg = True = throw error if var does not exist
--               False = if var does not exist then add it to the environment

kiType :: Bool -> AHsType -> KI Kind 
kiType _ (AHsTyCon name)
   = do tyConKind <- lookupKindEnv name 
        case tyConKind of
           Nothing 
              -> do env <- getEnv
                    error $ "kiType: could not find kind for this constructor: " ++ show name ++
                         "\nin this kind environment:\n" ++ show env
           Just k -> return k

kiType varExist (AHsTyVar name)
   = do varKind <- lookupKindEnv name 
        case varKind of
           Nothing 
              -> case varExist of
                    True 
                       -> error $ "kiType: could not find kind for this type variable: " ++ show name  
                    False -> do varKind <- newKindVar
				extendEnv $ unitEnv (name, varKind)
                                return varKind
           Just k -> return k

-- kind(t1) = kind(t2) -> var

kiType varExist (AHsTyApp t1 t2)
   = do
        k1 <- kiType varExist t1
        k2 <- kiType varExist t2
        varKind <- newKindVar
        unify k1 (k2 `Kfun` varKind) 
        return varKind 

-- kind(->) = * -> * -> *
-- kind (t1 -> t2) = *, |- kind(t1) = *, kind(t2) = *


kiType varExist (AHsTyFun t1 t2)
   = do
        k1 <- kiType varExist t1
        k2 <- kiType varExist t2 
        unify k1 Star
        unify k2 Star
        return Star 

-- kind (t1, t2, ..., tn) = *
-- |- kind(t1) = *, kind(t2) = *, ... , kind(tn) = *

kiType varExist (AHsTyTuple ts)
   = do
        tsKs <- mapM (kiType varExist) ts
        mapM_ (\k -> unify k Star) tsKs
        return Star 

newNameVar :: AHsName -> KI (AHsName, Kind)
newNameVar n 
   = do
        newVar <- newKindVar
        return (n, newVar) 


-------------------------------------------------------------------------------- 

-- code for getting the kinds of variables in type sigs

kiAHsQualType :: KindEnv -> AHsQualType -> KindEnv
kiAHsQualType inputEnv qualType
   = env newState
   where
   (_, newState)
      = runKI inputEnv $ do kiQualType False qualType
                            envVarsToStars


--------------------------------------------------------------------------------

getDataAndClassBg :: [AHsDecl] -> [[AHsDecl]]
getDataAndClassBg decls 
   = getBindGroups decls getDeclName dataAndClassDeps 

dataAndClassDeps :: AHsDecl -> [AHsName]
dataAndClassDeps (AHsDataDecl _sloc cntxt _name _args condecls _derives)
   = nub $ namesFromContext cntxt ++ (concatMap namesFromType $ concatMap conDeclToTypes condecls)
dataAndClassDeps (AHsNewTypeDecl _sloc cntxt _name _args condecl _derives)
   = nub $ namesFromContext cntxt ++ (concatMap namesFromType $ conDeclToTypes condecl)
dataAndClassDeps (AHsClassDecl _sloc (AHsQualType cntxt _classApp) decls)
   = nub $ namesFromContext cntxt ++ (concat [ namesFromQualType (typeFromSig s) | s <- decls,  isSigDecl s])
dataAndClassDeps (AHsClassDecl _sloc (AHsUnQualType _classApp) decls)
   = nub $ concat [ namesFromQualType (typeFromSig s) | s <- decls,  isSigDecl s]

namesFromQualType :: AHsQualType -> [AHsName]
namesFromQualType (AHsQualType cntxt t)
   = namesFromContext cntxt ++ namesFromType t
namesFromQualType (AHsUnQualType t)
   = namesFromType t

namesFromType :: AHsType -> [AHsName]
namesFromType (AHsTyFun t1 t2)
   = namesFromType t1 ++ namesFromType t2
namesFromType (AHsTyTuple ts)
   = concatMap namesFromType ts
namesFromType (AHsTyApp t1 t2)
   = namesFromType t1 ++ namesFromType t2
namesFromType (AHsTyVar _) = []
namesFromType (AHsTyCon n) = [n]

namesFromContext :: AHsContext -> [AHsName]
namesFromContext cntxt
   = map fst cntxt

--------------------------------------------------------------------------------

-- (type constructor name, arguments to constructor)
type DataDeclHead = (AHsName, [AHsName])
-- (class decls, data decl heads, class and data contexts, types in body of data decl, types in body of class)
type KindGroup = (AHsContext, [DataDeclHead], AHsContext, [AHsType], [AHsQualType])

declsToKindGroup :: [AHsDecl] -> KindGroup
declsToKindGroup [] = ([], [], [], [], [])

declsToKindGroup ((AHsDataDecl _sloc context tyconName tyconArgs condecls _derives):decls)
   = (restClassDecls, 
      newHead:restDataHeads, 
      context++restContext, 
      newBodies ++ restDataBodies, 
      restClassBodies)
   where
   (restClassDecls, restDataHeads, restContext, restDataBodies, restClassBodies) 
      = declsToKindGroup decls
   newHead = (tyconName, tyconArgs)
   newBodies = concatMap conDeclToTypes condecls

declsToKindGroup ((AHsNewTypeDecl _sloc context tyconName tyconArgs condecl _derives):decls)
   = (restClassDecls, 
      newHead:restDataHeads, 
      context++restContext, 
      newBodies ++ restDataBodies, 
      restClassBodies)
   where
   (restClassDecls, restDataHeads, restContext, restDataBodies, restClassBodies) 
      = declsToKindGroup decls
   newHead = (tyconName, tyconArgs)
   newBodies = conDeclToTypes condecl


declsToKindGroup (AHsClassDecl _sloc qualType sigsAndDefaults : decls)
   = (newClassDecl:restClassDecls, 
      restDataHeads, 
      newContext++restContext, 
      restDataBodies, 
      newClassBodies++restClassBodies)
   where
   (restClassDecls, restDataHeads, restContext, restDataBodies, restClassBodies) 
      = declsToKindGroup decls
   newClassBodies = map typeFromSig $ filter isSigDecl sigsAndDefaults
   (newClassDecl, newContext)
      = case qualType of
           (AHsQualType contxt (AHsTyApp (AHsTyCon className) (AHsTyVar classArg)))
              -> ((className, classArg), contxt)
           (AHsUnQualType (AHsTyApp (AHsTyCon className) (AHsTyVar classArg)))
              -> ((className, classArg), [])


conDeclToTypes :: AHsConDecl -> [AHsType]
conDeclToTypes (AHsConDecl _sloc name bangTypes)
   = map bangTypeToType bangTypes
conDeclToTypes (AHsRecDecl _lsoc _name _recs)
   = error $ "conDeclToType (AHsRecDecl _lsoc _name _recs): not implemented yet"

bangTypeToType :: AHsBangType -> AHsType
bangTypeToType (AHsBangedTy t) = t
bangTypeToType (AHsUnBangedTy t) = t

typeFromSig :: AHsDecl -> AHsQualType
typeFromSig (AHsTypeSig _sloc _names qualType) = qualType

--------------------------------------------------------------------------------

kindOf :: AHsName -> KindEnv -> Kind
kindOf name env 
   = case lookupEnv name env of
        Nothing -> error $ "kindOf: could not find kind of : " ++ show name
        Just k -> k


