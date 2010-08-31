{- |
Module      :  $Header$
Description :  manually resolve mixfix type applications
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

analyse mixfix types

-}

module HasCASL.TypeMixAna (mkTypeConstrAppl) where

import HasCASL.As
import HasCASL.Le
import HasCASL.AsUtils
import HasCASL.PrintAs ()
import Common.DocUtils
import Common.Id
import Common.Result
import qualified Data.Set as Set

-- | resolve parsed mixfix type to type applications with dummy kinds
mkTypeConstrAppl :: Env -> Type -> Result Type
mkTypeConstrAppl = mkTypeConstrAppls TopLevel

-- | construct application differently for left and right arguments
data ApplMode = TopLevel | OnlyArg

-- | manual mixfix resolution of parsed types
mkTypeConstrAppls :: ApplMode -> Env -> Type -> Result Type
mkTypeConstrAppls m e ty = case ty of
    TypeName _ _ _ -> return ty
    TypeToken tt -> return $ toType $ simpleIdToId tt
    BracketType b ts ps -> do
       args <- mapM (mkTypeConstrAppls m e) ts
       case b of
         Squares -> hint () ("a non-compound list: " ++ showDoc ty "") ps
         _ -> return ()
       case args of
         [] -> return $ case b of
             Parens -> unitType
             _ -> toType $ mkId $ mkBracketToken b ps
         [x] -> return $ case b of
             Parens -> x
             _ -> let
                 [o, c] = mkBracketToken b ps
                 t = TypeName (mkId [o, Token place ps, c])
                     (toRaw coKind) 0
                 in if isPlaceType (head ts) then t else TypeAppl t x
         _ -> mkError "illegal type" ty
    MixfixType l -> case mkCompoundTypeIds e l of
         f : a -> do
           newF <- mkTypeConstrAppls TopLevel e f
           nA <- mapM (mkTypeConstrAppls OnlyArg e) a
           return $ foldl1 TypeAppl $ newF : nA
         [] -> error "mkTypeConstrAppl (MixfixType [])"
    KindedType t k p -> do
       newT <- mkTypeConstrAppls m e t
       return $ KindedType newT k p
    _ -> case getTypeAppl ty of
       (top@(TypeName i _ _), ts) -> let n = length ts in
           if i == lazyTypeId && n == 1 then do
           newT <- mkTypeConstrAppls TopLevel e $ head ts
           return $ mkLazyType newT
           else if isProductIdWithArgs i n then
             if all isPlaceType ts then
                return top else do
                mTs <- mapM (mkTypeConstrAppls TopLevel e) ts
                return $ mkProductTypeWithRange mTs $ posOfId i
           else if n == 2 && isArrow i then
                if all isPlaceType ts then
                return top else do
                mTs <- mapM (mkTypeConstrAppls TopLevel e) ts
                return $ mkTypeAppl top mTs
           else error "mkTypeConstrAppls"
       _ -> error $ "mkTypeConstrAppls " ++ showDoc ty "\n" ++ show ty

mkCompoundTypeIds :: Env -> [Type] -> [Type]
mkCompoundTypeIds e l = case l of
    a@(TypeToken t) : b@(BracketType Squares as ps) : r ->
        let mis = mapM reparseAsId as in
        case mis of
          Just cs | Set.member cs $ getCompoundLists e ->
           toType (Id [t] cs ps) : mkCompoundTypeIds e r
          _ -> a : b : mkCompoundTypeIds e r
    a : r -> a : mkCompoundTypeIds e r
    [] -> []

isPlaceType :: Type -> Bool
isPlaceType ty = case ty of
    TypeToken t -> isPlace t
    _ -> False
