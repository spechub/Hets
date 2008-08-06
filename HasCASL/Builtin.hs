{- |
Module      :  $Header$
Description :  builtin types and functions
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

HasCASL's builtin types and functions
-}

module HasCASL.Builtin
    ( cpoId
    , cpoMap
    , bList
    , bTypes
    , bOps
    , preEnv
    , addBuiltins
    , aTypeArg
    , bTypeArg
    , aType
    , bType
    , botId
    , whenElse
    , ifThenElse
    , defId
    , eqId
    , falseId
    , trueId
    , notId
    , negId
    , andId
    , orId
    , implId
    , infixIf
    , eqvId
    , resId
    , resType
    , botType
    , whenType
    , defType
    , eqType
    , notType
    , logType
    , mkQualOp
    , mkEqTerm
    , mkLogTerm
    , toBinJunctor
    , mkTerm
    , unitTerm
    , unitTypeScheme
    ) where

import Common.Id
import Common.Keywords
import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Anno_Parser
import Common.AnalyseAnnos
import Common.Result
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le

import Text.ParserCombinators.Parsec

-- * buitln identifiers

trueId :: Id
trueId = mkId [mkSimpleId trueS]

falseId :: Id
falseId = mkId [mkSimpleId falseS]

ifThenElse :: Id
ifThenElse = mkId (map mkSimpleId [ifS, place, thenS, place, elseS, place])

whenElse :: Id
whenElse = mkId (map mkSimpleId [place, whenS, place, elseS, place])

infixIf :: Id
infixIf = mkInfix ifS

andId :: Id
andId = mkInfix lAnd

orId :: Id
orId = mkInfix lOr

implId :: Id
implId = mkInfix implS

eqvId :: Id
eqvId = mkInfix equivS

resId :: Id
resId = mkInfix "res"

{-
    make these prefix identifier to allow "not def x" to be recognized
    as "not (def x)" by giving def__ higher precedence then not__.
    Simple identifiers usually have higher precedence then ____,
    otherwise "def x" would be rejected. But with simple identifiers
    "not def x" would be parsed as "(not def) x" because ____ is left
    associative.
-}

defId :: Id
defId = mkId [mkSimpleId defS, placeTok]

notId :: Id
notId = mkId [mkSimpleId notS, placeTok]

negId :: Id
negId = mkId [mkSimpleId negS, placeTok]

builtinRelIds :: Set.Set Id
builtinRelIds = Set.fromList [typeId, eqId, exEq, defId]

builtinLogIds :: Set.Set Id
builtinLogIds = Set.fromList [andId, eqvId, implId, orId, infixIf, notId]

-- | add builtin identifiers
addBuiltins :: GlobalAnnos -> GlobalAnnos
addBuiltins ga =
    let ass = assoc_annos ga
        newAss = Map.union ass $ Map.fromList
                 [(applId, ALeft), (andId, ALeft), (orId, ALeft),
                  (implId, ARight), (infixIf, ALeft),
                  (whenElse, ARight)]
        precs = prec_annos ga
        pMap = Rel.toMap precs
        opIds = Set.unions (Map.keysSet pMap : Map.elems pMap)
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
        ops2 = map ( \ i -> (i, applId)) opIs
        newPrecs = foldl (\ p (a, b) -> if Rel.path b a p then p else
                         Rel.insert a b p) precs $
                   concat [logs, rels1, rels1b, rels2, ops1, ops2]
    in case addGlobalAnnos ga { assoc_annos = newAss
          , prec_annos = Rel.transClosure newPrecs } $
            map parseDAnno displayStrings of
         Result _ (Just newGa) -> newGa
         _ -> error "addBuiltins"

displayStrings :: [String]
displayStrings =
  [ "%display __\\/__ %LATEX __\\vee__"
  , "%display __/\\__ %LATEX __\\wedge__"
  , "%display __=>__ %LATEX __\\Rightarrow__"
  , "%display __<=>__ %LATEX __\\Leftrightarrow__"
  , "%display not__ %LATEX \\neg__"
  ]

parseDAnno :: String -> Annotation
parseDAnno str = case parse annotationL "" str of
    Left _ -> error "parseDAnno"
    Right a -> a

aVar :: Id
aVar = stringToId "a"

bVar :: Id
bVar = stringToId "b"

aType :: Type
aType = typeArgToType aTypeArg

bType :: Type
bType = typeArgToType bTypeArg

lazyAType :: Type
lazyAType = mkLazyType aType

varToTypeArg :: Id -> Int -> Variance -> TypeArg
varToTypeArg i n v = TypeArg i v (VarKind universe) rStar n Other nullRange

mkATypeArg :: Variance -> TypeArg
mkATypeArg = varToTypeArg aVar (-1)

aTypeArg :: TypeArg
aTypeArg = mkATypeArg NonVar

bTypeArg :: TypeArg
bTypeArg = varToTypeArg bVar (-2) NonVar

bindA :: Type -> TypeScheme
bindA t = TypeScheme [aTypeArg] t nullRange

resType :: TypeScheme
resType = TypeScheme [aTypeArg, bTypeArg]
    (mkFunArrType (mkProductType [lazyAType, mkLazyType bType]) FunArr aType)
    nullRange

lazyLog :: Type
lazyLog = mkLazyType unitType

aPredType :: Type
aPredType = TypeAbs (mkATypeArg ContraVar)
    (mkFunArrType aType PFunArr unitType) nullRange

eqType :: TypeScheme
eqType = bindA $ mkFunArrType (mkProductType [lazyAType, lazyAType])
    PFunArr unitType

logType :: TypeScheme
logType = simpleTypeScheme $ mkFunArrType
    (mkProductType [lazyLog, lazyLog]) PFunArr unitType

notType :: TypeScheme
notType = simpleTypeScheme $ mkFunArrType lazyLog PFunArr unitType

whenType :: TypeScheme
whenType = bindA $ mkFunArrType
    (mkProductType [lazyAType, lazyLog, lazyAType]) PFunArr aType

unitTypeScheme :: TypeScheme
unitTypeScheme = simpleTypeScheme lazyLog

botId :: Id
botId = mkId [mkSimpleId "g_bottom"]

predTypeId :: Id
predTypeId = mkId [mkSimpleId "Pred"]

logId :: Id
logId = mkId [mkSimpleId "Logical"]

botType :: TypeScheme
botType = bindA $ lazyAType

defType :: TypeScheme
defType = bindA $ mkFunArrType lazyAType PFunArr unitType

-- | builtin functions
bList :: [(Id, TypeScheme)]
bList = (botId, botType) : (defId, defType) : (notId, notType) :
        (negId, notType) : (whenElse, whenType) :
        (trueId, unitTypeScheme) : (falseId, unitTypeScheme) :
        (eqId, eqType) : (exEq, eqType) : (resId, resType) :
        map ( \ o -> (o, logType)) [andId, orId, eqvId, implId, infixIf]

funSupertypes :: [(Arrow, [Arrow])]
funSupertypes = [(PFunArr,[]), (FunArr, [PFunArr]), (PContFunArr, [PFunArr]),
                 (ContFunArr, [PContFunArr, FunArr])]

-- | builtin data type map
bTypes :: TypeMap
bTypes = Map.fromList . map ( \ (i, k, s, d) ->
    (i, TypeInfo (toRaw k) (Set.singleton k) (Set.fromList s) d)) $
              (unitTypeId, universe, [], NoTypeDefn)
              : (predTypeId, FunKind ContraVar universe universe nullRange, [],
                           AliasTypeDefn aPredType)
              : (lazyTypeId, coKind, [], NoTypeDefn)
              : (logId, universe, [], AliasTypeDefn $ mkLazyType unitType)
              : map ( \ n -> (productId n nullRange, prodKind n nullRange
                             , [], NoTypeDefn))
                [2 .. 5]
              ++ map ( \ (a, l) -> (arrowId a, funKind,
                        map ( \ b -> arrowId b) l,
                                   NoTypeDefn))
                funSupertypes

cpoId :: Id
cpoId = stringToId "Cpo"

-- | builtin class map
cpoMap :: ClassMap
cpoMap = Map.empty -- Map.singleton cpoId $ ClassInfo rStar Set.empty

-- | builtin function map
bOps :: Assumps
bOps = Map.fromList $ map ( \ (i, sc) ->
    (i, Set.singleton $ OpInfo sc Set.empty $ NoOpDefn Fun)) bList

-- | environment with predefined names
preEnv :: Env
preEnv = initialEnv { classMap = cpoMap, typeMap = bTypes, assumps = bOps }

mkQualOp :: Id -> TypeScheme -> [Type] -> Range -> Term
mkQualOp i sc tys ps = QualOp Fun (PolyId i [] ps) sc tys Infer ps

mkTerm :: Id -> TypeScheme -> [Type] -> Range -> Term  -> Term
mkTerm i sc tys ps t = ApplTerm (mkQualOp i sc tys ps) t ps

mkBinTerm :: Id -> TypeScheme -> [Type] -> Range -> Term  -> Term -> Term
mkBinTerm i sc tys ps t1 t2 = mkTerm i sc tys ps $ TupleTerm [t1, t2] ps

mkLogTerm :: Id -> Range -> Term  -> Term -> Term
mkLogTerm i ps = mkBinTerm i logType [] ps

mkEqTerm :: Id -> Type -> Range -> Term -> Term -> Term
mkEqTerm i ty ps = mkBinTerm i eqType [ty] ps

unitTerm :: Id -> Range -> Term
unitTerm i ps = mkQualOp i unitTypeScheme [] ps

toBinJunctor :: Id -> [Term] -> Range -> Term
toBinJunctor i ts ps = case ts of
    [] -> error "toBinJunctor"
    [t] -> t
    t : rs -> mkLogTerm i ps t (toBinJunctor i rs ps)
