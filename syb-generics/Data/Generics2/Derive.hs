{-# OPTIONS -fglasgow-exts -fth -fallow-overlapping-instances #-}
--
-- The bulk of this module was shamelessly ripped from Ulf Norell,
-- winner of the  Succ-zeroth International Obfuscated Haskell Code Contest. I
-- mention this as it was from his winning entry that this module began.
--
--
-- I have extended it to deal with data definitions with type variables.
-- I also added the coments.
--
-- Sean Seefried 2004
--
-- Extended to work with SYB3, by Simon Foster 2004.
--

module Data.Generics2.Derive where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.List
import Data.Char
import Data.Generics2.Basics
import Control.Monad
import Data.Maybe

-- maximum type paramters for a Typeable instance 
maxTypeParams = 7


-- | Make an unqualified version of a name
unqualName :: Name -> Name
unqualName n = mkName $ nameBase n

--
-- | Takes the name of an algebraic data type, the number of type parameters
--   it has and creates a Typeable instance for it.
deriveTypeablePrim :: Name -> Int -> Q [Dec]
deriveTypeablePrim name nParam
  | nParam <= maxTypeParams =
     sequence
      [ instanceD (return [])
         (conT typeableName `appT` conT name)
        [ funD typeOfName [clause [wildP] (normalB
           [| mkTyConApp (mkTyCon $(litE $ stringL (nameBase name))) $(listE []) |]) []]
        ]
      ]
  | otherwise = error ("Typeable classes can only have a maximum of " ++
                      show maxTypeParams ++ " parameters")
  where
    typeableName
      | nParam == 0 = mkName "Typeable"
      | otherwise   = mkName ("Typeable" ++ show nParam)
    typeOfName
      | nParam == 0  = mkName "typeOf"
      | otherwise    = mkName ("typeOf" ++ show nParam)

--
-- | Takes a name of a algebraic data type, the number of parameters it
--   has, a list of constructor pairs and a context variable.  Each one of these constructor
--   pairs consists of a constructor name and the number of type
--   parameters it has.  The function returns an automatically generated
--   instance declaration for the Data class.
--
--   Doesn't do gunfold, dataCast1 or dataCast2
deriveDataPrim :: Name -> [TypeQ] -> [(Name, Int)] -> [(Name, [(Maybe Name, Type)])] -> Maybe Name -> Q [Dec]
deriveDataPrim name typeQParams cons terms ctx =
  do sequence (
      conDecs ++

      [ dataTypeDec
      , instanceD context
           (conT ''Data `appT` varT ctx' `appT` (foldl1 appT ([conT name] ++ typeQParams)))
        [ funD (unqualName 'gfoldl)
            [ clause ([wildP] ++ (map (varP . mkName) ["f", "z", "x"]))
                (normalB $ caseE (varE (mkName "x")) (map mkMatch cons))
                []
            ]
        , funD (unqualName 'gunfold)
          [clause ([wildP] ++ (map (varP. mkName) ["k", "z", "c"]))
            (if (null cons) then (normalB [| error "gunfold : Type has no constructors" |]) 
                            else (normalB $ caseE (varE (mkName "constrIndex") `appE` varE (mkName "c")) mkMatches)) []]
        , funD (unqualName 'toConstr)
            [ clause [wildP, varP (mkName "x")]
                (normalB $ caseE (varE (mkName "x"))
                 (zipWith mkSel cons conVarExps))
                []
            ]
        , funD (unqualName 'dataTypeOf)
            [ clause [wildP, wildP] (normalB $ varE (mkName dataTypeName)) []
            ]
        ]
      ])
     where
         ctx' = fromMaybe (mkName "ctx") ctx
         distinctTypes = map return $ filter (\x -> case x of (VarT _) -> False; _ -> True) $ nub $ map snd $ concat $ map snd terms
         fieldNames = let fs = map (map fst.snd) terms in
			  map (\x -> if (null x || all isNothing x) then [] else map (maybe "" show) x) fs
         nParam = length typeQParams
         
{-         paramNames = take nParam (zipWith (++) (repeat "a") (map show [0..]))
         typeQParams = map (\nm -> varT (mkName nm)) paramNames-}
         context = cxt $ (maybe ((map (\typ -> conT ''Data `appT` varT ctx' `appT` typ) distinctTypes)   ++ 
                                 (map (\typ -> conT ''Sat  `appT` (varT ctx' `appT` typ)) distinctTypes) ++
                                 (map (\typ -> conT ''Data `appT` (varT ctx') `appT` typ) typeQParams)   ++ 
                                 [conT ''Sat `appT` ((varT ctx') `appT` (foldl1 appT ([conT name] ++ typeQParams)))])

                                 
                                 (const $ if (null typeQParams) 
                                            then []
                                            else ((map (\typ -> conT ''Data `appT` (varT ctx') `appT` typ) typeQParams) ++
                                                  [conT ''Sat `appT` ((varT ctx') `appT` (foldl1 appT ([conT name] ++ typeQParams)))]))

                                 ctx)
                         

         -- Takes a pair (constructor name, number of type arguments) and
         -- creates the correct definition for gfoldl
         -- It is of the form z <constr name> `f` arg1 `f` ... `f` argn
         mkMatch (c,n) =
            do  vs <- mapM (\s -> newName s) names
                match   (conP c $ map varP vs)
                        (normalB $ foldl
                           (\e x -> (varE (mkName "f") `appE` e) `appE` varE x)
                                    (varE (mkName "z") `appE` conE c)
                                    vs
                        ) []
           where names = take n (zipWith (++) (repeat "x") (map show [0..]))
	 mkMatches = map (\(n, (cn, i)) -> match (litP $ integerL n) (normalB $ reapply (appE (varE $ mkName "k")) i (varE (mkName "z") `appE` conE cn)) []) (zip [1..] cons)
	   where
           reapply _ 0 f = f
           reapply x n f = x (reapply x (n-1) f)
         lowCaseName = map toLower nameStr
         nameStr = nameBase name
         dataTypeName = lowCaseName ++ "DataType"
         -- Creates dataTypeDec of the form:
         -- <name>DataType = mkDataType <name> [<constructors]
         dataTypeDec = funD (mkName dataTypeName)
                       [clause []
                        (normalB
                         [| mkDataType nameStr $(listE (conVarExps)) |]) [] ]
                
         -- conVarExps is a [ExpQ]. Each ExpQ is a variable expression
         -- of form varE (mkName <con>Constr)
         numCons = length cons
         constrNames =
           take numCons (map (\i -> dataTypeName ++ show i ++ "Constr") [1..])
         conNames = map (nameBase . fst) cons
         conVarExps = map (varE . mkName) constrNames
         conDecs = zipWith3 mkConstrDec constrNames conNames fieldNames
          where
           mkConstrDec decNm conNm fieldNm =
             funD (mkName decNm)
                     [clause []
                        (normalB
                         [| mkConstr $(varE (mkName dataTypeName)) conNm fieldNm
                            $(fixity conNm)
                         |]) []]
                
         fixity (':':_)  = [| Infix |]
         fixity _        = [| Prefix |]

         mkSel (c,n) e = match  (conP c $ replicate n wildP)
                         (normalB e) []

deriveMinimalData :: Name -> Int  -> Q [Dec]
deriveMinimalData name nParam  = do
   decs <- qOfDecs
   let listOfDecQ = map return decs
   sequence
     [ instanceD context
         (conT ''Data `appT` (foldl1 appT ([conT name] ++ typeQParams)))
         listOfDecQ ]

   where
     paramNames = take nParam (zipWith (++) (repeat "a") (map show [0..]))
     typeQParams = map (\nm -> varT (mkName nm)) paramNames
     context = cxt (map (\typ -> conT ''Data `appT` typ) typeQParams)
     qOfDecs =
       [d| gunfold _ _ _ = error ("gunfold not defined")
           toConstr x    = error ("toConstr not defined for " ++
                              show (typeOf x))
           dataTypeOf x = error ("dataTypeOf not implemented for " ++
                            show (typeOf x))
           gfoldl f z x = z x
        |]

{- instance Data NameSet where
   gunfold _ _ _ = error ("gunfold not implemented")
   toConstr x = error ("toConstr not implemented for " ++ show (typeOf 
x))
   dataTypeOf x = error ("dataTypeOf not implemented for " ++ show 
(typeOf x))
   gfoldl f z x = z x -}

typeInfo :: DecQ -> Q (Name, [Name], [(Name, Int)], [(Name, [(Maybe Name, Type)])])
typeInfo m =
     do d <- m
        case d of
           d@(DataD _ _ _ _ _) ->
            return $ (simpleName $ name d, paramsA d, consA d, termsA d)
           d@(NewtypeD _ _ _ _ _) ->
            return $ (simpleName $ name d, paramsA d, consA d, termsA d)
           _ -> error ("derive: not a data type declaration: " ++ show d)

     where
        consA (DataD _ _ _ cs _)    = map conA cs
        consA (NewtypeD _ _ _ c _)  = [ conA c ]

        paramsA (DataD _ _ ps _ _) = ps
        paramsA (NewtypeD _ _ ps _ _) = ps

        termsA (DataD _ _ _ cs _) = map termA cs
	termsA (NewtypeD _ _ _ c _) = [ termA c ]

        termA (NormalC c xs)        = (c, map (\x -> (Nothing, snd x)) xs)
	termA (RecC c xs)           = (c, map (\(n, _, t) -> (Just $ simpleName n, t)) xs)
	termA (InfixC t1 c t2)      = (c, [(Nothing, snd t1), (Nothing, snd t2)])

        conA (NormalC c xs)         = (simpleName c, length xs)
        conA (RecC c xs)            = (simpleName c, length xs)
        conA (InfixC _ c _)         = (simpleName c, 2)

        name (DataD _ n _ _ _)      = n
        name (NewtypeD _ n _ _ _)   = n
        name d                      = error $ show d

simpleName :: Name -> Name
simpleName nm =
   let s = nameBase nm
   in case dropWhile (/=':') s of
        []          -> mkName s
        _:[]        -> mkName s
        _:t         -> mkName t

--
-- | Derives the Data and Typeable instances for a single given data type.
--
deriveOne :: Name -> Q [Dec]
deriveOne name =
  do    info' <- reify name
        case info' of
           TyConI d -> do
             (name, param, ca, terms) <- typeInfo ((return d) :: Q Dec)
             t <- deriveTypeablePrim name (length param)
             d <- deriveDataPrim name (map varT param) ca terms Nothing
             return $ t ++ d
           _ -> error ("derive: can't be used on anything but a type " ++
                      "constructor of an algebraic data type")

deriveOneCtx :: Name -> Name -> Q [Dec]
deriveOneCtx name ctx =
  do    info' <- reify name
        case info' of
           TyConI d -> do
             (name, param, ca, terms) <- typeInfo ((return d) :: Q Dec)
             t <- deriveTypeablePrim name (length param)
             d <- deriveDataPrim name (map varT param) ca terms (Just ctx)
             return $ t ++ d
           _ -> error ("derive: can't be used on anything but a type " ++
                      "constructor of an algebraic data type")


deriveOneFromDec :: DecQ -> Q [Dec]
deriveOneFromDec dec = 
    do (name, param, ca, terms) <- typeInfo dec
       t <- deriveTypeablePrim name (length param)
       d <- deriveDataPrim name (map varT param) ca terms Nothing
       return $ t ++ d


deriveOneData :: Name -> Q [Dec]
deriveOneData name = 
  do    info' <- reify name
        case info' of
           TyConI d -> do
             (name, param, ca, terms) <- typeInfo ((return d) :: Q Dec)
             d <- deriveDataPrim name (map varT param) ca terms Nothing
             return d
           _ -> error ("derive: can't be used on anything but a type " ++
                      "constructor of an algebraic data type")


--
-- | Derives Data and Typeable instances for a list of data
--   types. Order is irrelevant. This should be used in favour of
--   deriveOne since Data and Typeable instances can often depend on
--   other Data and Typeable instances - e.g. if you are deriving a
--   large, mutually recursive data type.  If you splice the derived
--   instances in one by one you will need to do it in depedency order
--   which is difficult in most cases and impossible in the mutually
--   recursive case. It is better to bring all the instances into
--   scope at once.
--
--  e.g. if
--     data Foo = Foo Int
--  is declared in an imported module then
--     $(derive [''Foo])
--  will derive the instances for it
derive :: [Name] -> Q [Dec]
derive names = do
  decss <- mapM deriveOne names
  return (concat decss)

deriveCtx :: [Name] -> Name -> Q [Dec]
deriveCtx names ctx = do
  decss <- mapM (\n -> deriveOneCtx n ctx) names
  return (concat decss)


deriveData :: [Name] -> Q [Dec]
deriveData names = do
  decss <- mapM deriveOneData names
  return (concat decss)

deriveTypeable :: [Name] -> Q [Dec]
deriveTypeable names = do
  decss <- mapM deriveOneTypeable names
  return (concat decss)

deriveOneTypeable :: Name -> Q [Dec]
deriveOneTypeable name =
  do    info' <- reify name
        case info' of
           TyConI d -> do
             (name, param, ca, terms) <- typeInfo ((return d) :: Q Dec)
             t <- deriveTypeablePrim name (length param)
             return t
           _ -> error ("derive: can't be used on anything but a type " ++
                      "constructor of an algebraic data type")


  
  
--
-- | This function is much like deriveOne except that it brings into
--   scope an instance of Data with minimal definitions. gfoldl will
--   essentially leave a data structure untouched while gunfoldl,
--   toConstr and dataTypeOf will yield errors.
--
--   This function is useful when you are certain that you will never
--   wish to transform a particular data type.  For instance you may
--   be transforming another data type that contains other data types,
--   some of which you wish to transform (perhaps recursively) and
--   some which you just wish to return unchanged.
--
--   Sometimes you will be forced to use deriveMinimalOne because you 
--   do not have access to the contructors of the data type (perhaps
--   because it is an Abstract Data Type). However, should the
--   interface to the ADT be sufficiently rich it is possible to
--   define you're own Data and Typeable instances.
deriveMinimalOne :: Name -> Q [Dec]
deriveMinimalOne name =
  do    info' <- reify name
        case info' of
           TyConI d -> do
            (name, param, _, _) <- typeInfo ((return d) :: Q Dec)
            t <- deriveTypeablePrim name (length param)
            d <- deriveMinimalData name (length param)
            return $ t ++ d
           _ -> error ("deriveMinimal: can't be used on anything but a type " ++
                      "constructor of an algebraic data type")


deriveMinimal :: [Name] -> Q [Dec]
deriveMinimal names = do
   decss <- mapM deriveMinimalOne names
   return (concat decss)

-- Apologies for this, but it's the only way atm to get lifted Strings to be output
-- as Strings rather than lists of Chars.
-- instance Lift String where
--    lift x = litE $ stringL x
