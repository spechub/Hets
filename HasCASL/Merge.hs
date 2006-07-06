{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

merging parts of local environment
-}

module HasCASL.Merge where

import Common.Id
import Common.DocUtils
import Common.Result

import HasCASL.As
import HasCASL.Le
import HasCASL.AsUtils
import HasCASL.TypeAna
import HasCASL.PrintLe()
import HasCASL.Unify
import HasCASL.Builtin
import HasCASL.MapTerm
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

import Control.Monad(foldM)
import Data.List

-- | merge together repeated or extended items
class Mergeable a where
    merge :: a -> a -> Result a 

instance (Ord a, PosItem a, Pretty a, Mergeable b) 
    => Mergeable (Map.Map a b) where
    merge = mergeMap id merge

improveDiag :: (PosItem a, Pretty a) => a -> Diagnosis -> Diagnosis
improveDiag v d = d { diagString = let f:l = lines $ diagString d in 
                      unlines $ (f ++ " of '" ++ showDoc v "'") : l
                    , diagPos = getRange v
                    }

mergeMap :: (Ord a, PosItem a, Pretty a) => 
            (b -> b) -> (b -> b -> Result b) 
         -> Map.Map a b -> Map.Map a b -> Result  (Map.Map a b)
mergeMap e f m1 m2 = foldM ( \ m (k, v) -> 
                          case k `Map.lookup` m of
                          Nothing -> return $ Map.insert k (e v) m
                          Just w -> 
                              let Result ds mu = f (e v) w
                                  ns = map (improveDiag k) ds  
                              in case mu of 
                                 Nothing -> Result ns $ Nothing
                                 Just u -> Result ns $ Just $ Map.insert k u m)
                  Map.empty (Map.toList m1 ++ Map.toList m2)  

instance Mergeable a => Mergeable (Maybe a) where
    merge m1 m2 = case m1 of 
                          Nothing -> return m2
                          Just v1 -> case m2 of 
                                             Nothing -> return m1
                                             Just v2 -> do v <- merge v1 v2
                                                           return $ Just v

instance Mergeable ClassInfo where
    merge = mergeA "super classes"

instance (Pretty a, Eq a) => Mergeable (AnyKind a) where
    merge = mergeA "super kinds" 

mergeTypeInfo :: TypeInfo -> TypeInfo -> Result TypeInfo 
mergeTypeInfo t1 t2 = 
    do k <- merge (typeKind t1) $ typeKind t2
       o <- merge (otherTypeKinds t1) $ otherTypeKinds t2
       s <- merge (superTypes t1) $ superTypes t2
       d <- mergeTypeDefn (typeDefn t1) $ typeDefn t2
       return $ TypeInfo k o s d 

mergeTypeDefn :: TypeDefn -> TypeDefn -> Result TypeDefn
mergeTypeDefn d1 d2 = 
        case (d1, d2) of 
            (_, DatatypeDefn _) -> return d2 
            (PreDatatype, _) -> fail "expected data type definition"
            (_, PreDatatype) -> return d1
            (NoTypeDefn, _) -> return d2
            (_, NoTypeDefn) -> return d1
            (AliasTypeDefn s1, AliasTypeDefn s2) -> 
                do s <- mergeScheme s1 s2
                   return $ AliasTypeDefn s
            (_, _) -> mergeA "TypeDefn" d1 d2

instance Mergeable Vars where
    merge = mergeA "variables for subtype definition"

mergeScheme :: TypeScheme -> TypeScheme -> Result TypeScheme
mergeScheme s1@(TypeScheme a1 t1 _)
            s2@(TypeScheme a2 t2 _) = 
    let v1 = genVarsOf t1
        v2 = genVarsOf t2
        mp a v = foldr ( \ i l ->
               maybe l (:l) $ findIndex ((== i) . getTypeVar) a)
                  [] (map fst v)
    in 
    if t1 == t2 then 
       if null a1 && null a2 || isSingle a1 && isSingle a2 then 
          return s1
       else if mp a1 v1 == mp a2 v2 then return s1
                else fail ("differently bound type variables" 
                         ++ expected s1 s2) 
    else fail ("wrong type scheme" ++ expected s1 s2)

instance Mergeable OpAttr where
    merge (UnitOpAttr t1 p1) (UnitOpAttr t2 p2) = 
        do t <- mergeTerm Warning t1 t2
           return $ UnitOpAttr t (p1 `appRange` p2)
    merge a1 a2 = mergeA "attributes" a1 a2 

instance Mergeable OpBrand where
    merge Pred _ = return Pred
    merge _ Pred = return Pred
    merge Op _   = return Op
    merge _ Op   = return Op
    merge _ _    = return Fun
    
instance Mergeable OpDefn where
    merge (NoOpDefn _) d  = return d
    merge d (NoOpDefn _)  = return d
    merge (ConstructData d1) (ConstructData _d2) = do 
--        d <- mergeA "constructor target type" d1 d2
        return $ ConstructData d1
    merge (SelectData c1 d1) (SelectData c2 _d2) = do
--        d <- mergeA "selector source type" d1 d2
        c <- merge c1 c2
        return $ SelectData c d1
    merge (Definition b1 d1) (Definition b2 d2) =
        do d <- mergeTerm Hint d1 d2
           b <- merge b1 b2
           return $ Definition b d
    merge _d1 _d2 = fail "illegal redefinition"

instance Eq a => Mergeable [a] where
    merge [] l2 = return l2
    merge (e:l1) l2 = do 
      l3 <- merge l1 l2
      return $ if any (e==) l2 then l3
         else e:l3

instance Ord a => Mergeable (Set.Set a) where
    merge s1 s2 = return $ Set.union s1 s2

mergeOpInfos :: TypeMap -> OpInfos -> OpInfos -> Result OpInfos 
mergeOpInfos tm (OpInfos l1) (OpInfos l2) = 
    do l <- mergeOps (addUnit tm) l1 l2
       return $ OpInfos  l

mergeOps :: TypeMap -> [OpInfo] -> [OpInfo] -> Result [OpInfo]
mergeOps _ [] l = return l
mergeOps tm (o:os) l2 = do 
    let (es, us) = partition (isUnifiable tm 1
                              (opType o) . opType) l2
    l1 <- mergeOps tm os us 
    if null es then return (o : l1)
       else do r <- mergeOpInfo tm o $ head es
               return (r : l1)

mergeOpInfo ::  TypeMap -> OpInfo -> OpInfo -> Result OpInfo
mergeOpInfo tm o1 o2 = 
        do let s1 = opType o1
               s2 = opType o2 
           sc <- if instScheme tm 1 s2 s1 then return s1
                    else if instScheme tm 1 s1 s2 then return s2
                    else fail "overlapping but incompatible type schemes"
           as <- merge (opAttrs o1) $ opAttrs o2
           d <- merge (opDefn o1) $ opDefn o2
           return $ OpInfo sc as d

instance Mergeable Env where
    merge e1 e2 =
        do cMap <- merge (classMap e1) $ classMap e2
           tMap <- mergeMap id mergeTypeInfo
                   (typeMap e1) $ typeMap e2
           as <- mergeMap (OpInfos . 
                           map (mapOpInfo (id, expandAlias tMap)) . opInfos) 
                 (mergeOpInfos tMap)
                 (assumps e1) $ assumps e2
           return initialEnv { classMap = cMap
                             , typeMap = tMap
                             , assumps = as }

mergeA :: (Pretty a, Eq a) => String -> a -> a -> Result a
mergeA str t1 t2 = if t1 == t2 then return t1 else 
    fail ("different " ++ str ++ expected t1 t2)

mergeTerm :: DiagKind -> Term -> Term -> Result Term
mergeTerm k t1 t2 = if t1 == t2 then return t1 else
            Result [Diag k ("different terms" ++ expected t1 t2) 
                    nullRange] $ Just t2
