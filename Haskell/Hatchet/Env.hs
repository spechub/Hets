{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 Env

        Description:            A generic environment that supports mappings 
                                from names to values.

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information
                                
                                Based on FiniteMaps

-------------------------------------------------------------------------------}

module Env (Env, 
            emptyEnv, 
            unitEnv, 
            lookupEnv,
            addToEnv,
            joinEnv, 
            joinListEnvs, 
            listToEnv,
            envToList,
            getNamesFromEnv,
            showEnv,
            pprintEnv,
            mapEnv
           ) where

import FiniteMaps (FiniteMap,
                   toListFM,
                   zeroFM,
                   unitFM,
                   lookupFM,
                   addToFM,
                   joinFM,
                   mapFM
                  )

import AnnotatedHsSyn      (AHsName (..))

import Utils      (isQualified,
                   getUnQualName)

import PPrint     (PPrint (..), 
                   Doc, 
                   vcat,
                   (<+>),
                   ($$),
                   text,
                   empty)

--------------------------------------------------------------------------------

type Env a = FiniteMap AHsName a 

emptyEnv :: Env a
emptyEnv = zeroFM

unitEnv :: (AHsName, a) -> Env a 
unitEnv item@(name, val)
   = unitFM name val

lookupEnv :: AHsName -> Env a -> Maybe a 
lookupEnv name env
   = lookupFM env name


addToEnv :: (AHsName, a) -> Env a -> Env a
addToEnv item@(name, val) env
   = addToFM name val env

-- this might be expensive!
joinEnv :: Env a -> Env a -> Env a 
joinEnv env1 env2 
   = joinFM env1 env2

joinListEnvs :: [Env a] -> Env a 
joinListEnvs = foldr joinEnv emptyEnv

listToEnv :: [(AHsName, a)] -> Env a 
listToEnv = foldr addToEnv emptyEnv  

envToList :: Env a -> [(AHsName, a)]
envToList env
   = toListFM env 

-- just get all the names out of the Env (added by Bryn)
getNamesFromEnv :: Env a -> [AHsName]
getNamesFromEnv env = map fst (toListFM env)

showEnv :: Show a => Env a -> String
showEnv env
   = unlines $ map show $ toListFM env 

-- pretty print the environment

pprintEnv :: PPrint a => Env a -> Doc
pprintEnv env 
   = vcat [((pprint a) <+> (text "::") <+> (pprint b)) | (a, b) <- toListFM env]

-- map a function over the elements of the environment
mapEnv :: (AHsName -> e -> e') -> Env e -> Env e'
mapEnv f map = mapFM f map

--------------------------------------------------------------------------------
