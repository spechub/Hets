{- |
Module      :  $Header$
Description :  analysis of data type declarations
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

analyse alternatives of data types
-}

module HasCASL.DataAna
    ( DataPat(..)
    , toDataPat
    , getConstrScheme
    , getSelScheme
    , anaAlts
    , makeDataSelEqs
    , inductionScheme
    , mkVarDecl
    ) where

import Data.Maybe (catMaybes)

import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.Id
import Common.Result
import Common.AS_Annotation

import HasCASL.As
import HasCASL.Le
import HasCASL.TypeAna
import HasCASL.AsUtils
import HasCASL.Builtin
import HasCASL.Unify

-- | description of polymorphic data types
data DataPat = DataPat Id [TypeArg] RawKind Type

mkVarDecl :: Id -> Type -> VarDecl
mkVarDecl i t = VarDecl i t Other nullRange

mkSelId :: Range -> String -> Int -> Int -> Id
mkSelId p str n m = mkId
    [Token (str ++ "_" ++ (if n < 1 then "" else show n ++ "_") ++ show m) p]

mkSelVar :: Int -> Int -> Type -> VarDecl
mkSelVar n m ty = mkVarDecl (mkSelId (getRange ty) "x" n m) ty

genTuple :: Int -> Int -> [Selector] -> [(Selector, VarDecl)]
genTuple _ _ [] = []
genTuple n m (s@(Select _ ty _) : sels) =
    (s, mkSelVar n m ty) : genTuple n (m + 1) sels

genSelVars :: Int -> [[Selector]] -> [[(Selector, VarDecl)]]
genSelVars n sels = case sels of
  [ts] -> [genTuple 0 1 ts]
  _ -> if all isSingle sels
       then map (: []) $ genTuple 0 1 $ map head sels
       else genSelVarsAux n sels

genSelVarsAux :: Int -> [[Selector]]  -> [[(Selector, VarDecl)]]
genSelVarsAux _ [] = []
genSelVarsAux n (ts : sels)  =
    genTuple n 1 ts : genSelVarsAux (n + 1) sels

makeSelTupleEqs :: DataPat -> Term -> [(Selector, VarDecl)] -> [Named Term]
makeSelTupleEqs dt ct = concatMap (\ (Select mi ty p, v) -> case mi of
     Just i -> let
         sc = getSelScheme dt p ty
         eq = mkEqTerm eqId ty nullRange
              (mkApplTerm (mkOpTerm i sc) [ct]) $ QualVar v
         in [makeNamed ("ga_select_" ++ show i) eq]
     _ -> [])

makeSelEqs :: DataPat -> Term -> [[(Selector, VarDecl)]] -> [Named Term]
makeSelEqs dt ct = concatMap $ makeSelTupleEqs dt ct

makeAltSelEqs :: DataPat -> AltDefn -> [Named Term]
makeAltSelEqs dt@(DataPat _ iargs _ _) (Construct mc ts p sels) =
    case mc of
    Nothing -> []
    Just c -> let
      selvars = genSelVars 1 sels
      vars = map (map snd) selvars
      ars = mkSelArgs vars
      ct = mkApplTerm (mkOpTerm c $ getConstrScheme dt p ts) ars
      in map (mapNamed (mkForall (map GenTypeVarDecl iargs
           ++ map GenVarDecl (concat vars)))) $ makeSelEqs dt ct selvars

mkSelArgs :: [[VarDecl]] -> [Term]
mkSelArgs = map (\ vs -> mkTupleTerm (map QualVar vs) nullRange)

getConstrScheme :: DataPat -> Partiality -> [Type] -> TypeScheme
getConstrScheme (DataPat _ args _ rt) p ts =
  TypeScheme args (getFunType rt p ts) nullRange

getSelScheme :: DataPat -> Partiality -> Type -> TypeScheme
getSelScheme (DataPat _ args _ rt) p t =
  TypeScheme args (getSelType rt p t) nullRange

-- | remove variances from generalized type arguments
toDataPat :: DataEntry -> DataPat
toDataPat (DataEntry im i _ args rk _) = let j = Map.findWithDefault i i im in
  DataPat j (map nonVarTypeArg args) rk $ patToType j args rk

-- | create selector equations for a data type
makeDataSelEqs :: DataPat -> [AltDefn] -> [Named Sentence]
makeDataSelEqs dp = map (mapNamed Formula) . concatMap (makeAltSelEqs dp)

-- | analyse the alternatives of a data type
anaAlts :: [DataPat] -> DataPat -> [Alternative] -> Env -> Result [AltDefn]
anaAlts tys dt alts te =
    do l <- mapM (anaAlt tys dt te) alts
       Result (checkUniqueness $ catMaybes $
               map ( \ (Construct i _ _ _) -> i) l) $ Just ()
       return l

anaAlt :: [DataPat] -> DataPat -> Env -> Alternative
       -> Result AltDefn
anaAlt _ _ te (Subtype ts _) =
    do l <- mapM ( \ t -> anaStarTypeM t te) ts
       return $ Construct Nothing (Set.toList $ Set.fromList $ map snd l)
           Partial []
anaAlt tys dt te (Constructor i cs p _) =
    do newCs <- mapM (anaComps tys dt te) cs
       let sels = map snd newCs
       Result (checkUniqueness $ catMaybes $
                map ( \ (Select s _ _) -> s ) $ concat sels) $ Just ()
       return $ Construct (Just i) (map fst newCs) p sels

anaComps :: [DataPat] -> DataPat -> Env -> [Component]
         -> Result (Type, [Selector])
anaComps tys rt te cs =
    do newCs <- mapM (anaComp tys rt te) cs
       return (mkProductType $ map fst newCs, map snd newCs)

isPartialSelector :: Type -> Bool
isPartialSelector ty = case ty of
  TypeAppl (TypeName i _ _) _ -> i == lazyTypeId
  _ -> False

anaComp :: [DataPat] -> DataPat -> Env -> Component
        -> Result (Type, Selector)
anaComp tys rt te (Selector s _ t _ _) =
    do ct <- anaCompType tys rt t te
       let (p, nct) = case getTypeAppl ct of
             (TypeName i _ _, [lt]) | i == lazyTypeId
                && isPartialSelector t -> (Partial, lt)
             _ -> (Total, ct)
       return (nct, Select (Just s) nct p)
anaComp tys rt te (NoSelector t) =
    do ct <- anaCompType tys rt t te
       return  (ct, Select Nothing ct Partial)

anaCompType :: [DataPat] -> DataPat -> Type -> Env -> Result Type
anaCompType tys (DataPat _ tArgs _ _) t te = do
    (_, ct) <- anaStarTypeM t te
    let ds = unboundTypevars True tArgs ct
    if null ds then return () else Result ds Nothing
    mapM_ (checkMonomorphRecursion ct te) tys
    return $ generalize tArgs ct

checkMonomorphRecursion :: Type -> Env -> DataPat -> Result ()
checkMonomorphRecursion t te (DataPat i _ _ rt) =
    case filter (\ ty -> not (lesserType te ty rt || lesserType te rt ty))
       $ findSubTypes (typeMap te) i t of
      [] -> return ()
      ty : _ -> Result [Diag Error  ("illegal polymorphic recursion"
                                 ++ expected rt ty) $ getRange ty] Nothing

findSubTypes :: TypeMap -> Id -> Type -> [Type]
findSubTypes tm i t = case getTypeAppl t of
    (TypeName j _ _, args) -> if relatedTypeIds tm i j then [t]
                              else concatMap (findSubTypes tm i) args
    (topTy, args) -> concatMap (findSubTypes tm i) $ topTy : args

relatedTypeIds :: TypeMap -> Id -> Id -> Bool
relatedTypeIds tm i1 i2 =
    not $ Set.null $ Set.intersection (allRelIds tm i1) $ allRelIds tm i2

allRelIds :: TypeMap -> Id -> Set.Set Id
allRelIds tm i = Set.union (superIds tm i) $ subIds tm i

subIds :: TypeMap -> Id -> Set.Set Id
subIds tm i = foldr ( \ j s ->
                 if Set.member i $ superIds tm j then
                      Set.insert j s else s) Set.empty $ Map.keys tm

mkPredVar :: DataPat -> VarDecl
mkPredVar (DataPat i _ _ rt) = let ps = posOfId i in
  mkVarDecl (if isSimpleId i then mkId [mkSimpleId $ "p_" ++ show i]
             else Id [mkSimpleId "p"] [i] ps) (predType ps rt)

mkPredAppl :: DataPat -> Term -> Term
mkPredAppl dp t = mkApplTerm (QualVar $ mkPredVar dp) [t]

mkPredToVarAppl :: DataPat -> VarDecl -> Term
mkPredToVarAppl dp = mkPredAppl dp . QualVar

mkConclusion :: DataPat -> Term
mkConclusion dp@(DataPat _ _ _ ty) =
  let v = mkVarDecl (mkId [mkSimpleId "x"]) ty
  in mkForall [GenVarDecl v] $ mkPredToVarAppl dp v

mkPremise :: Map.Map Type DataPat -> DataPat -> AltDefn -> [Term]
mkPremise m dp (Construct mc ts p sels) =
    case mc of
    Nothing -> []
    Just c -> let
      vars = map (map snd) $ genSelVars 1 sels
      findHypo vd@(VarDecl _ ty _ _) =
        fmap (flip mkPredToVarAppl vd) $ Map.lookup ty m
      flatVars = concat vars
      indHypos = catMaybes $ map findHypo flatVars
      indConcl = mkPredAppl dp
        $ mkApplTerm (mkOpTerm c $ getConstrScheme dp p ts)
        $ mkSelArgs vars
      in [mkForall (map GenVarDecl flatVars) $
          if null indHypos then indConcl else
           mkLogTerm implId nullRange (mkConjunct indHypos) indConcl]

mkConjunct :: [Term] -> Term
mkConjunct ts = if null ts then error "HasCASL.DataAna.mkConjunct" else
  toBinJunctor andId ts nullRange

mkPremises :: Map.Map Type DataPat -> DataEntry -> [Term]
mkPremises m de@(DataEntry _ _ _ _ _ alts) =
    concatMap (mkPremise m $ toDataPat de) $ Set.toList alts

joinTypeArgs :: [DataPat] -> Map.Map Id TypeArg
joinTypeArgs = foldr (\ (DataPat _ iargs _ _) m ->
   foldr (\ ta -> Map.insert (getTypeVar ta) ta) m iargs) Map.empty

inductionScheme :: [DataEntry] -> Term
inductionScheme des =
    let dps = map toDataPat des
        m = Map.fromList $ map (\ dp@(DataPat _ _ _ ty) -> (ty, dp)) dps
    in mkForall (map GenTypeVarDecl (Map.elems $ joinTypeArgs dps)
                 ++ map (GenVarDecl . mkPredVar) dps)
       $ mkLogTerm implId nullRange
         (mkConjunct $ concatMap (mkPremises m) des)
         $ mkConjunct $ map mkConclusion dps
