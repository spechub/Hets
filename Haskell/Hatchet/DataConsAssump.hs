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

module Haskell.Hatchet.DataConsAssump (dataConsEnv) where


import Haskell.Hatchet.AnnotatedHsSyn
                                (AHsDecl (..),
                                 AHsName (..),
                                 AHsConDecl (..),
                                 AHsContext)

import Haskell.Hatchet.Representation           
                                (Type (..),
                                 Tycon (..),
                                 Tyvar (..),
                                 unfoldKind,
                                 Kind (..),
                                 Pred (..),
                                 Qual (..),
                                 Scheme)

import Haskell.Hatchet.Type     (assumpToPair,
                                 makeAssump,
                                 Types (..),
                                 quantify)

import Haskell.Hatchet.HaskellPrelude (fn)

import Haskell.Hatchet.TypeUtils (aHsTypeToType)


import Haskell.Hatchet.KindInference
                                (KindEnv,
                                 bangTypeToType,
				 kindOf)

import Haskell.Hatchet.Env      (Env,
                                 joinListEnvs,
                                 unitEnv,
                                 listToEnv)

--------------------------------------------------------------------------------
-- True gets constructors, False selectors
dataConsEnv :: Bool -> KindEnv -> [AHsDecl] -> Env Scheme 
dataConsEnv b kt decls 
   = joinListEnvs $ map (dataDeclEnv b kt) decls 


-- we should only apply this function to data decls and newtype decls
-- howver the fall through case is just there for completeness

dataDeclEnv :: Bool -> KindEnv -> AHsDecl -> Env Scheme 
dataDeclEnv b kt decl = 
  let (context, typeName, args, condecls) = case decl of  
          AHsDataDecl _ c t a ds _ -> (c, t, a, ds)
	  AHsNewTypeDecl _ c t a d _ -> (c, t, a, [d])
	  _ -> ([], undefined, [], [])
      typeKind = kindOf typeName kt 
      resultType = foldl TAp tycon argVars
      tycon = TCon (Tycon typeName typeKind)
      argVars = map fromAHsNameToTyVar $ zip argKinds args
      argKinds = init $ unfoldKind typeKind 
      fromAHsNameToTyVar :: (Kind, AHsName) -> Type
      fromAHsNameToTyVar (k, n) = TVar (Tyvar n k)
      preds = hsContextToPreds kt context
      in joinListEnvs $ map (conDeclType b kt preds resultType) 
	 condecls

-- broken until classes are added properly

hsContextToPreds :: KindEnv -> AHsContext -> [Pred]
hsContextToPreds _ _assts
   = []

conDeclType :: Bool -> KindEnv -> [Pred] -> Type -> AHsConDecl 
	    -> Env Scheme 
conDeclType b kt preds tResult cd = 
    let (conName, bangTypes, sels) = case cd of 
           AHsConDecl _sloc cn bt -> (cn, bt, [])
	   AHsRecDecl _sloc cn lBts -> 
	       (cn, concatMap ( \ (ls, bt) -> map (const bt) ls) lBts,
		concatMap ( \ (ls, bt) -> map ( \ l -> (l , bt)) ls) lBts)
	conType = foldr fn tResult $ map toType bangTypes
	qualConType = preds :=> conType
	toType bt = aHsTypeToType kt $ bangTypeToType bt
    in if b then unitEnv $ assumpToPair 
         $ makeAssump conName $ quantify (tv qualConType) qualConType
       else listToEnv $ map ( \ ( s, bt) ->
		  let qty = [] :=> (fn tResult $ toType bt)
		  in assumpToPair $ makeAssump s $ quantify (tv qty ) qty) sels
