{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable

   HasCASL's builtin types and functions
-}

module HasCASL.Builtin where

import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Id
import Common.Keywords
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Earley
import HasCASL.As
import HasCASL.Le

trueId :: Id
trueId = mkId [mkSimpleId trueS]

falseId :: Id
falseId = mkId [mkSimpleId falseS]

ifThenElse :: Id
ifThenElse = mkId (map mkSimpleId [ifS, place, thenS, place, elseS, place])

whenElse :: Id
whenElse = mkId (map mkSimpleId [place, whenS, place, elseS, place])

mkInfix :: String -> Id
mkInfix s = mkId $ map mkSimpleId [place, s, place]

infixIf :: Id 
infixIf = mkInfix ifS

exEq :: Id 
exEq = mkInfix exEqual

eqId :: Id 
eqId = mkInfix equalS

andId :: Id 
andId = mkInfix lAnd

orId :: Id 
orId = mkInfix lOr

implId :: Id 
implId = mkInfix implS

eqvId :: Id 
eqvId = mkInfix equivS

defId :: Id 
defId = mkId $ map mkSimpleId [defS, place]

notId :: Id 
notId = mkId $ map mkSimpleId [notS, place]

negId :: Id 
negId = mkId $ map mkSimpleId [negS, place]

builtinRelIds :: Set.Set Id 
builtinRelIds = Set.fromList [typeId, eqId, exEq, defId]

builtinLogIds :: Set.Set Id 
builtinLogIds = Set.fromList 
                 [andId, eqvId, implId, orId, infixIf, notId] 

addBuiltins :: GlobalAnnos -> GlobalAnnos
addBuiltins ga = 
    let ass = assoc_annos ga
        newAss = Map.union ass $ Map.fromList 
                 [(applId, ALeft), (andId, ALeft), (orId, ALeft), 
                  (implId, ARight), (infixIf, ALeft), 
                  (whenElse, ARight)]
        precs = prec_annos ga
        pMap = Rel.toMap precs          
        opIds = Set.unions (Rel.keysSet pMap : Map.elems pMap)
        opIs = Set.toList ((((Set.filter isInfix opIds)
                Set.\\ builtinRelIds) Set.\\ builtinLogIds) 
                Set.\\ Set.fromList [applId, whenElse])

        logs = [(eqvId, implId), (implId, andId), (implId, orId), 
                (eqvId, infixIf), (infixIf, andId), (infixIf, orId),
                 (andId, notId), (orId, notId),
                (andId, negId), (orId, negId)]

        rels1 = map ( \ i -> (notId, i)) $ Set.toList builtinRelIds
        rels1b = map ( \ i -> (negId, i)) $ Set.toList builtinRelIds
        rels2 = map ( \ i -> (i, whenElse)) $ Set.toList builtinRelIds
        ops1 = map ( \ i -> (whenElse, i)) (applId : opIs)
        ops2 = map ( \ i -> (i, applId)) (whenElse : opIs)
        newPrecs = foldr (\ (a, b) p -> if Rel.member b a p then p else 
                         Rel.insert a b p) precs $  
                  concat [logs, rels1, rels1b, rels2, ops1, ops2]
    in ga { assoc_annos = newAss
          , prec_annos = Rel.transClosure newPrecs }

mkPrecIntMap :: Rel.Rel Id -> PrecMap
mkPrecIntMap r = 
    let t = Rel.topSort r
        l = length t
        m = foldr ( \ (n, s) m1 -> 
                    Set.fold ( \ i m2 ->Map.insert i n m2)  m1 s)
                 Map.empty $ zip [1..l] t
        in (m, m Map.! eqId, l)

aVar :: Id
aVar = simpleIdToId $ mkSimpleId "a"
aType :: Type
aType = TypeName aVar star (-1)

bindA :: Type -> TypeScheme
bindA ty = TypeScheme [TypeArg aVar star Other []] ty []

lazyLog :: Type 
lazyLog = LazyType logicalType []

eqType, logType, defType, notType, whenType, unitType :: TypeScheme
eqType = bindA $ 
          FunType (ProductType [aType, aType] [])
          PFunArr logicalType []
logType = simpleTypeScheme $ 
          FunType (ProductType [lazyLog, lazyLog] [])
          PFunArr logicalType []
defType = bindA $ FunType aType PFunArr logicalType []
notType = simpleTypeScheme $ FunType lazyLog PFunArr logicalType []

whenType = bindA $ 
          FunType (ProductType [aType, lazyLog, aType] [])
          PFunArr aType []
unitType = simpleTypeScheme logicalType

botId :: Id
botId = mkId [mkSimpleId "bottom"]

predTypeId :: Id
predTypeId = mkId [mkSimpleId "Pred"]

logId :: Id
logId = mkId [mkSimpleId "Logical"]

botType :: TypeScheme
botType = bindA aType

bList :: [(Id, TypeScheme)]
bList = (botId, botType) : (defId, defType) : (notId, notType) : 
        (negId, notType) : (whenElse, whenType) :
        (trueId, unitType) : (falseId, unitType) :
        (eqId, eqType) : (exEq, eqType) :
        map ( \ o -> (o, logType)) [andId, orId, eqvId, implId, infixIf]

addUnit :: TypeMap -> TypeMap
addUnit tm = foldr ( \ (i, k, s, d) m -> 
                 Map.insertWith ( \ _ old -> old) i
                         (TypeInfo k [k] s d) m) tm $
              (unitTypeId, star, [], NoTypeDefn)
              : (predTypeId, FunKind star star [], [], AliasTypeDefn defType)
              : (logId, star, [], AliasTypeDefn $ simpleTypeScheme $ 
                 FunType logicalType PFunArr logicalType [])
              : (productId, prodKind, [], NoTypeDefn)
              : map ( \ (a, l) -> (arrowId a, funKind, 
                        map ( \ b -> TypeName (arrowId b) funKind 0) l,
                                   NoTypeDefn)) 
                [(PFunArr,[]), (FunArr, [PFunArr]), (PContFunArr, [PFunArr]), 
                 (ContFunArr, [PContFunArr, FunArr])]

addOps :: Assumps -> Assumps
addOps as = foldr ( \ (i, sc) m -> 
                 Map.insertWith ( \ _ old -> old) i
                 (OpInfos [OpInfo sc [] (NoOpDefn Fun)]) m) as bList

mkQualOp :: Id -> TypeScheme -> [Pos] -> Term 
mkQualOp i sc ps = QualOp Fun (InstOpId i [] ps) sc ps

mkTerm :: Id -> TypeScheme -> [Pos] -> Term  -> Term
mkTerm i sc ps t = ApplTerm (mkQualOp i sc ps) t ps

mkBinTerm :: Id -> TypeScheme -> [Pos] -> Term  -> Term -> Term
mkBinTerm i sc ps t1 t2 = mkTerm i sc ps $ TupleTerm [t1, t2] ps

mkLogTerm :: Id -> [Pos] -> Term  -> Term -> Term
mkLogTerm i ps = mkBinTerm i logType ps

mkEqTerm :: Id -> [Pos] -> Term  -> Term -> Term
mkEqTerm i ps = mkBinTerm i eqType ps

unitTerm :: Id -> [Pos] -> Term
unitTerm i ps = mkQualOp i unitType ps

toBinJunctor :: Id -> [Term] -> [Pos] -> Term
toBinJunctor i ts ps = case ts of
    [] -> error "toBinJunctor"
    [t] -> t
    t:rs -> mkLogTerm i ps t 
            (toBinJunctor i rs ps)



