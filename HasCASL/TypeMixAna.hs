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
import Common.Id
import Common.Result
import Common.PrettyPrint

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
    LazyType t p -> do
       newT <- mkTypeConstrAppls TopLevel t
       return $ LazyType newT p 
    ProductType ts ps -> let n = length ts in 
       if all isPlaceType ts && n > 1 then 
       return $ toType $ productId n else do
       mTs <- mapM (\ t -> mkTypeConstrAppls TopLevel t) ts
       return $ mkProductType mTs ps
    FunType t1 a t2 ps -> if isPlaceType t1 && isPlaceType t2 then
       return $ toType $ arrowId a else do
       newT1 <- mkTypeConstrAppls TopLevel t1
       newT2 <- mkTypeConstrAppls TopLevel t2
       return $ FunType newT1 a newT2 ps
    ExpandedType _ t2 -> mkTypeConstrAppls m t2
    _ -> error $ "mkTypeConstrAppls " ++ showPretty ty "\n" ++ show ty

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

