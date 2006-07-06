{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

analyse mixfix types

-}

module HasCASL.TypeMixAna (mkTypeConstrAppl) where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs ()
import Common.DocUtils
import Common.Id
import Common.Result

-- | resolve parsed mixfix type to type applications with dummy kinds
mkTypeConstrAppl :: Type -> Result Type
mkTypeConstrAppl = mkTypeConstrAppls TopLevel

-- | construct application differently for left and right arguments 
data ApplMode = TopLevel | OnlyArg 

-- | manual mixfix resolution of parsed types
mkTypeConstrAppls :: ApplMode -> Type -> Result Type
mkTypeConstrAppls m ty = case ty of
    TypeName _ _ _ -> return ty
    TypeToken tt -> return $ toType $ simpleIdToId tt
    BracketType b ts ps -> do
       args <- mapM (\ trm -> mkTypeConstrAppls m trm) ts
       case args of
                  [] -> case b of
                        Parens -> return unitType
                        _ -> return $ toType $ mkId $ mkBracketToken b ps
                  [x] -> case b of
                         Parens -> return x
                         _ -> do let [o,c] = mkBracketToken b ps 
                                     t = toType $ mkId 
                                         [o, Token place $ firstPos args ps, c]
                                 if isPlaceType (head ts) then return t
                                    else return $ TypeAppl t x
                  _ -> mkError "illegal type" ty
    MixfixType [] -> error "mkTypeConstrAppl (MixfixType [])"
    MixfixType (f:a) -> case (f, a) of 
      (TypeToken t, [BracketType Squares as@(_:_) ps]) -> do 
         mis <- mapM mkTypeCompId as 
         return $ toType $ Id [t] mis ps
      _ -> do newF <- mkTypeConstrAppls TopLevel f 
              nA <- mapM ( \ t -> mkTypeConstrAppls OnlyArg t) a
              return $ foldl1 TypeAppl $ newF : nA
    KindedType t k p -> do 
       newT <- mkTypeConstrAppls m t
       return $ KindedType newT k p
    _ -> case getTypeAppl ty of 
       (top@(TypeName i _ _), ts) -> let n = length ts in 
           if i == lazyTypeId && n == 1 then do
           newT <- mkTypeConstrAppls TopLevel $ head ts
           return $ mkLazyType newT
           else if i == productId n then
             if all isPlaceType ts then 
                return top else do
                mTs <- mapM (mkTypeConstrAppls TopLevel) ts
                return $ mkProductType mTs
           else if n == 2 && isArrow i then
                if all isPlaceType ts then
                return top else do
                mTs <- mapM (mkTypeConstrAppls TopLevel) ts
                return $ mkTypeAppl top mTs
           else error "mkTypeConstrAppls"
       _ -> error $ "mkTypeConstrAppls " ++ showDoc ty "\n" ++ show ty

isPlaceType :: Type -> Bool
isPlaceType ty = case ty of 
    TypeToken t -> isPlace t
    _ -> False

mkTypeCompId :: Type -> Result Id
mkTypeCompId ty = case ty of 
    TypeToken t -> if isPlace t then mkError "unexpected place" t
                   else return $ Id [t] [] nullRange
    MixfixType [] -> error "mkTypeCompId: MixfixType []"
    MixfixType (hd:tps) ->
         if null tps then mkTypeCompId hd
         else do 
         let (toks, comps) = break ( \ p -> 
                        case p of BracketType Squares (_:_) _ -> True
                                  _ -> False) tps
         mts <- mapM mkTypeCompToks (hd:toks)
         (mis, ps) <- if null comps then return ([], nullRange)
                     else mkTypeCompIds $ head comps
         pls <- if null comps then return [] 
                else mapM mkTypeIdPlace $ tail comps
         return $ Id (concat mts ++ pls) mis ps 
    _ -> do ts <- mkTypeCompToks ty
            return $ Id ts [] nullRange

mkTypeCompIds :: Type -> Result ([Id], Range)
mkTypeCompIds ty = case ty of
    BracketType Squares tps@(_:_) ps -> do
        mis <- mapM mkTypeCompId tps  
        return (mis, ps)
    _ -> mkError "no compound list for type id" ty

mkTypeCompToks :: Type -> Result [Token]
mkTypeCompToks ty = case ty of 
    TypeToken t -> return [t]
    BracketType bk [tp] ps -> case bk of 
        Parens -> mkError "no type id" ty
        _ -> do let [o,c] = mkBracketToken bk ps
                mts <- mkTypeCompToks tp
                return (o : mts ++ [c])
    MixfixType tps -> do
        mts <- mapM mkTypeCompToks tps
        return $ concat mts
    _ -> mkError "no type tokens" ty

mkTypeIdPlace :: Type -> Result Token
mkTypeIdPlace ty =  case ty of 
    TypeToken t -> if isPlace t then return t
                   else mkError "no place" t
    _ -> mkError "no place" ty

