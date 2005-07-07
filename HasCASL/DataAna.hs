{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (MonadState)

analyse alternatives of data types

-}

module HasCASL.DataAna where

import Data.Maybe

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Result
import Common.AS_Annotation

import HasCASL.As
import HasCASL.Le
import HasCASL.TypeAna
import HasCASL.AsUtils
import HasCASL.Builtin
import HasCASL.Unify

mkSelId :: [Pos] -> String -> Int -> Int -> Id
mkSelId p str n m = mkId 
    [Token (str ++ "_" ++ show n ++ "_" ++ show m) p]

mkSelVar :: Int -> Int -> Type -> VarDecl
mkSelVar n m ty = VarDecl (mkSelId (get_pos ty) "x" n m) ty  Other []

genTuple :: Int -> Int -> [Selector] -> [VarDecl]
genTuple _ _ [] = [] 
genTuple n m (Select _ ty _ : sels) = 
    mkSelVar n m ty : genTuple n (m + 1) sels

genSelVars :: Int -> [[Selector]]  -> [[VarDecl]]
genSelVars _ [] = []
genSelVars n (ts:sels)  = 
    genTuple n 1 ts : genSelVars (n + 1) sels

makeSelTupleEqs :: DataPat -> Term -> Int -> Int -> [Selector] -> [Named Term]
makeSelTupleEqs dt ct n m (Select mi ty p : sels) = 
    let sc = getSelType dt p ty in
    (case mi of
     Just i -> let
                  vt = QualVar $ mkSelVar n m ty
                  eq = mkEqTerm eqId [] (mkApplTerm (mkOpTerm i sc) [ct]) vt
              in [NamedSen ("ga_select_" ++ show i) True eq]
     _ -> [])
    ++ makeSelTupleEqs dt ct n (m + 1) sels
makeSelTupleEqs _ _ _ _ [] = []

makeSelEqs :: DataPat -> Term -> Int -> [[Selector]] -> [Named Term]
makeSelEqs dt ct n (sel:sels) = 
    makeSelTupleEqs dt ct n 1 sel 
    ++ makeSelEqs dt ct (n + 1) sels 
makeSelEqs _ _ _ _ = []

makeAltSelEqs :: DataPat -> AltDefn -> [Named Term]
makeAltSelEqs dt@(_, args, _) (Construct mc ts p sels) = 
    case mc of
    Nothing -> []
    Just c -> let sc = TypeScheme args (getConstrType dt p ts) [] 
                  newSc = generalize sc
                  vars = genSelVars 1 sels 
                  as = map ( \ vs -> mkTupleTerm (map QualVar vs) []) vars
                  ct = mkApplTerm (mkOpTerm c newSc) as
              in map (mapNamed (mkForall (map GenTypeVarDecl args
                                  ++ map GenVarDecl (concat vars))))
                 $ makeSelEqs dt ct 1 sels

makeDataSelEqs :: DataEntry -> Kind -> [Named Sentence]
makeDataSelEqs (DataEntry _ i _ args alts) k =
    map (mapNamed Formula) $  
    concatMap (makeAltSelEqs(i, args, k)) alts

anaAlts :: [DataPat] -> DataPat -> [Alternative] -> TypeEnv -> Result [AltDefn]
anaAlts tys dt alts te = 
    do l <- mapM (anaAlt tys dt te) alts
       Result (checkUniqueness $ catMaybes $ 
               map ( \ (Construct i _ _ _) -> i) l) $ Just ()
       return l

anaAlt :: [DataPat] -> DataPat -> TypeEnv -> Alternative 
       -> Result AltDefn 
anaAlt _ (_, args, _) te (Subtype ts _) = 
    do l <- mapM ( \ t -> anaStarTypeM t te) ts
       return $ Construct Nothing (map ( \ (_, t) -> mkGenVars args t) l) 
              Partial []
anaAlt tys dt te (Constructor i cs p _) = 
    do newCs <- mapM (anaComps tys dt te) cs
       let sels = map snd newCs
       Result (checkUniqueness $ catMaybes $ 
                map ( \ (Select s _ _) -> s ) $ concat sels) $ Just ()
       return $ Construct (Just i) (map fst newCs) p sels

anaComps :: [DataPat] -> DataPat -> TypeEnv -> [Component]
         -> Result (Type, [Selector]) 
anaComps tys rt te cs =
    do newCs <- mapM (anaComp tys rt te) cs
       return (mkProductType (map fst newCs) [], map snd newCs)

anaComp :: [DataPat] -> DataPat -> TypeEnv -> Component 
        -> Result (Type, Selector)
anaComp tys rt te (Selector s p t _ _) =
    do ct <- anaCompType tys rt t te
       return (ct, Select (Just s) ct p)
anaComp tys rt te (NoSelector t) =
    do ct <- anaCompType tys rt t te
       return  (ct, Select Nothing ct Partial)

getSelType :: DataPat -> Partiality -> Type -> TypeScheme
getSelType dp@(_, args, _) p rt = let dt = typeIdToType dp in 
    generalize $ TypeScheme args ((case p of 
    Partial -> addPartiality [dt]
    Total -> id) (FunType dt FunArr rt [])) []

anaCompType :: [DataPat] -> DataPat -> Type -> TypeEnv -> Result Type
anaCompType tys (_, as, _) t te = do
    (_, ct1) <- anaStarTypeM t te
    let ct = mkGenVars as ct1
        ds = unboundTypevars as ct 
    if null ds then return () else Result ds Nothing
    mapM (checkMonomorphRecursion ct te) tys
    return ct
 
checkMonomorphRecursion :: Type -> TypeEnv -> DataPat -> Result ()
checkMonomorphRecursion t te p@(i, _, _) = 
    let rt = typeIdToType p in
    if occursIn (typeMap te) i t then 
       if lesserType te t rt || lesserType te rt t then return ()
       else Result [Diag Error  ("illegal polymorphic recursion" 
                                 ++ expected rt t) $ get_pos t] Nothing
    else return ()

occursIn :: TypeMap -> TypeId -> Type -> Bool
occursIn tm i = any (relatedTypeIds tm i) . Set.toList . idsOf (const True)

relatedTypeIds :: TypeMap -> TypeId -> TypeId -> Bool
relatedTypeIds tm i1 i2 = 
    not $ Set.null $ Set.intersection (allRelIds tm i1) $ allRelIds tm i2

allRelIds :: TypeMap -> TypeId -> Set.Set TypeId
allRelIds tm i = Set.union (superIds tm i) $ subIds tm i 

-- | super type ids
superIds :: TypeMap -> Id -> Set.Set Id
superIds tm = supIds tm Set.empty . Set.singleton

subIds :: TypeMap -> Id -> Set.Set Id
subIds tm i = foldr ( \ j s ->
                 if Set.member i $ superIds tm j then
                      Set.insert j s else s) Set.empty $ Map.keys tm

supIds :: TypeMap -> Set.Set Id -> Set.Set Id -> Set.Set Id
supIds tm known new = 
    if Set.null new then known else 
       let more = Set.unions $ map superTypeToId $ 
                  concatMap ( \ i -> superTypes 
                            $ Map.findWithDefault starTypeInfo i tm)
                  $ Set.toList new 
           newKnown = Set.union known new
    in supIds tm newKnown (more Set.\\ newKnown)

superTypeToId :: Type -> Set.Set Id
superTypeToId t = 
    case t of
           TypeName i _ _ -> Set.singleton i
           _ -> Set.empty
