{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 DataConsAssump 

        Description:            Computes the type assumptions of data 
                                constructors in a module

                                For example:
                                        MyCons :: a -> MyList a
                                        Just :: a -> Maybe a
                                        True :: Bool

                                Note Well:

                                from section 4.2 of the Haskell Report:

                                "These declarations may only appear at the 
                                 top level of a module."

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module DataConsAssump (dataConsEnv) where


import AnnotatedHsSyn           (AHsDecl (..),
                                 AHsName (..),
                                 AModule (AModule),
                                 AHsBangType (..),
                                 AHsConDecl (..),
                                 AHsContext)

import Representation           (Type (..),
                                 Tycon (..),
                                 Tyvar (..),
                                 unfoldKind,
                                 Kind (..),
                                 Pred (..),
                                 Qual (..),
                                 Assump (..),
                                 Scheme)

import Type                     (assumpToPair,
                                 makeAssump,
                                 Types (..),
                                 quantify)

import HaskellPrelude           (fn)

import Utils                    (fromAHsName)


import TypeUtils                (aHsTypeToType)


import FiniteMaps               (FiniteMap,
                                 toListFM,
                                 listToFM)


import KindInference            (KindEnv,
                                 kindOf)

import Env                      (Env,
                                 showEnv,
                                 joinListEnvs,
                                 unitEnv,
                                 emptyEnv,
                                 listToEnv)

--------------------------------------------------------------------------------

dataConsEnv :: AModule -> KindEnv -> [AHsDecl] -> Env Scheme 
dataConsEnv modName kt decls 
   = joinListEnvs $ map (dataDeclEnv modName kt) decls 


-- we should only apply this function to data decls and newtype decls
-- howver the fall through case is just there for completeness

dataDeclEnv :: AModule -> KindEnv -> (AHsDecl) -> Env Scheme 
dataDeclEnv modName kt (AHsDataDecl _sloc context typeName args condecls derives)
   = joinListEnvs $ map (conDeclType modName kt preds resultType) $ condecls 
   where
   typeKind = kindOf typeName kt 
   resultType = foldl TAp tycon argVars
   tycon = TCon (Tycon typeName typeKind)
   argVars = map fromAHsNameToTyVar $ zip argKinds args
   argKinds = init $ unfoldKind typeKind 
   fromAHsNameToTyVar :: (Kind, AHsName) -> Type
   fromAHsNameToTyVar (k, n) 
      = TVar (Tyvar n k)
   preds = hsContextToPreds kt context

dataDeclEnv modName kt (AHsNewTypeDecl _sloc context typeName args condecl derives)
   = conDeclType modName kt preds resultType condecl
   where
   typeKind = kindOf typeName kt
   resultType = foldl TAp tycon argVars
   tycon = TCon (Tycon typeName typeKind)
   argVars = map fromAHsNameToTyVar $ zip argKinds args
   argKinds = init $ unfoldKind typeKind
   fromAHsNameToTyVar :: (Kind, AHsName) -> Type
   fromAHsNameToTyVar (k, n)
      = TVar (Tyvar n k)
   preds = hsContextToPreds kt context

dataDeclEnv _modName _kt _anyOtherDecl 
   = emptyEnv

-- broken until classes are added properly

hsContextToPreds :: KindEnv -> AHsContext -> [Pred]
hsContextToPreds _ assts
   = []

conDeclType :: AModule -> KindEnv -> [Pred] -> Type -> AHsConDecl -> Env Scheme 
conDeclType modName kt preds tResult (AHsConDecl _sloc conName bangTypes)
   = unitEnv $ assumpToPair $ makeAssump conName $ quantify (tv qualConType) qualConType
   where
   conType = foldr fn tResult (map (bangTypeToType kt) bangTypes)
   qualConType = preds :=> conType

bangTypeToType :: KindEnv -> AHsBangType -> Type
bangTypeToType kt (AHsBangedTy t) = aHsTypeToType kt t 
bangTypeToType kt (AHsUnBangedTy t) = aHsTypeToType kt t

