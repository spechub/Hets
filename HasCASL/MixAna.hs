{- |
Module      :  ./HasCASL/MixAna.hs
Description :  mixfix analysis for terms
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Mixfix analysis of terms and patterns, type annotations are also analysed
-}

module HasCASL.MixAna
  ( resolve
  , anaPolyId
  , makeRules
  , getPolyIds
  , iterateCharts
  , toMixTerm
  , uTok
  ) where

import Common.AnnoParser
import Common.AnnoState
import Common.ConvertMixfixToken
import Common.DocUtils
import Common.Earley
import Common.GlobalAnnotations
import Common.Id
import Common.Lib.State
import Common.Parsec
import Common.Prec
import Common.Result

import qualified Data.Map as Map
import qualified Data.Set as Set

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs
import HasCASL.VarDecl
import HasCASL.Le
import HasCASL.ParseTerm
import HasCASL.TypeAna

import qualified Text.ParserCombinators.Parsec as P

import Data.Maybe
import Control.Exception (assert)
import Control.Monad

addType :: Term -> Term -> Term
addType (MixTypeTerm q ty ps) t = TypedTerm t q ty ps
addType _ _ = error "addType"

-- | try to reparse terms as a compound list
isCompoundList :: Set.Set [Id] -> [Term] -> Bool
isCompoundList compIds =
    maybe False (`Set.member` compIds) . mapM reparseAsId

isTypeList :: Env -> [Term] -> Bool
isTypeList e l = case mapM termToType l of
    Nothing -> False
    Just ts ->
        let Result ds ml = mapM ( \ t -> anaTypeM (Nothing, t) e) ts
        in isJust ml && not (hasErrors ds)

termToType :: Term -> Maybe Type
termToType t = case P.runParser ((case getPosList t of
    [] -> return ()
    p : _ -> P.setPosition $ fromPos p)
      >> parseType << P.eof) (emptyAnnos ()) "" $ showDoc t "" of
    Right x -> Just x
    _ -> Nothing

anaPolyId :: PolyId -> TypeScheme -> State Env (Maybe TypeScheme)
anaPolyId (PolyId i@(Id _ cs _) _ _) sc = do
    mSc <- anaTypeScheme sc
    case mSc of
      Nothing -> return Nothing
      Just newSc@(TypeScheme tvars _ _) -> do
          e <- get
          let ids = Set.unions
                [ Map.keysSet $ classMap e
                , Map.keysSet $ typeMap e
                , Map.keysSet $ assumps e ]
              es = filter (not . flip Set.member ids) cs
          addDiags $ map (mkDiag (if null tvars then Hint else Warning)
            "unexpected identifier in compound list") es
          unless (null cs || null tvars)
            $ addDiags [mkDiag Hint "is polymorphic compound identifier" i]
          return $ Just newSc

resolveQualOp :: PolyId -> TypeScheme -> State Env TypeScheme
resolveQualOp i@(PolyId j _ _) sc = do
    mSc <- anaPolyId i sc
    e <- get
    case mSc of
      Nothing -> return sc -- and previous
      Just nSc -> do
        when (Set.null $ Set.filter ((== nSc) . opType)
                  $ Map.findWithDefault Set.empty j $ assumps e)
          $ addDiags [mkDiag Error "operation not found" j]
        return nSc

iterateCharts :: GlobalAnnos -> Set.Set Id -> Set.Set [Id] -> [Term]
              -> Chart Term -> State Env (Chart Term)
iterateCharts ga sIds compIds terms chart = do
    e <- get
    let self = iterateCharts ga sIds compIds
        oneStep = nextChart addType (toMixTerm e) ga chart
        vs = localVars e
        tm = typeMap e
    case terms of
      [] -> return chart
      t : tt -> let recurse trm = self tt $ oneStep
                      (trm, exprTok {tokPos = getRange trm}) in case t of
        MixfixTerm ts -> self (ts ++ tt) chart
        MixTypeTerm q typ ps -> do
          mTyp <- anaStarType typ
          case mTyp of
            Nothing -> recurse t
            Just nTyp -> self tt $ oneStep
                (MixTypeTerm q (monoType nTyp) ps, typeTok {tokPos = ps})
        BracketTerm b ts ps ->
          let bres = self (expandPos TermToken
                (getBrackets b) ts ps ++ tt) chart in case (b, ts, tt) of
          (Squares, _ : _, _)
            | isCompoundList compIds ts -> do
              addDiags [mkDiag Hint "is compound list" t]
              bres
            | isTypeList e ts -> do
              let testChart = oneStep (t, typeInstTok {tokPos = ps})
              if null $ solveDiags testChart then do
                addDiags [mkDiag Hint "is type list" t]
                self tt testChart
                else bres
          (Parens, [QualOp b2 v sc [] _ ps2], hd@(BracketTerm Squares
                   ts2@(_ : _) ps3) : rtt)
            | isTypeList e ts2 -> do
                   addDiags [mkDiag Hint "is type list" ts2]
                   nSc <- resolveQualOp v sc
                   self rtt $ oneStep
                     ( QualOp b2 v nSc (bracketTermToTypes e hd) UserGiven ps2
                     , exprTok {tokPos = appRange ps ps3})
          _ -> bres
        QualVar (VarDecl v typ ok ps) -> do
          mTyp <- anaStarType typ
          recurse $ maybe t ( \ nType -> QualVar $ VarDecl v (monoType nType)
            ok ps) mTyp
        QualOp b v sc [] k ps -> do
          nSc <- resolveQualOp v sc
          recurse $ QualOp b v nSc [] k ps
        QuantifiedTerm quant decls hd ps -> do
          newDs <- mapM (anaddGenVarDecl False) decls
          mt <- resolve hd
          putLocalVars vs
          putTypeMap tm
          recurse $ QuantifiedTerm quant (catMaybes newDs) (fromMaybe hd mt) ps
        LambdaTerm decls part hd ps -> do
          mDecls <- mapM resolve decls
          let anaDecls = catMaybes mDecls
              bs = concatMap extractVars anaDecls
          checkUniqueVars bs
          mapM_ (addLocalVar False) bs
          mt <- resolve hd
          putLocalVars vs
          recurse $ LambdaTerm anaDecls part (fromMaybe hd mt) ps
        CaseTerm hd eqs ps -> do
          mt <- resolve hd
          newEs <- resolveCaseEqs eqs
          recurse $ CaseTerm (fromMaybe hd mt) newEs ps
        LetTerm b eqs hd ps -> do
          newEs <- resolveLetEqs eqs
          mt <- resolve hd
          putLocalVars vs
          recurse $ LetTerm b newEs (fromMaybe hd mt) ps
        TermToken tok -> do
          let (ds1, trm) = convertMixfixToken (literal_annos ga)
                (flip ResolvedMixTerm []) TermToken tok
          addDiags ds1
          self tt $ oneStep $ case trm of
            TermToken _ -> (trm, tok)
            _ -> (trm, exprTok {tokPos = tokPos tok})
        AsPattern vd p ps -> do
          mp <- resolve p
          recurse $ AsPattern vd (fromMaybe p mp) ps
        TypedTerm trm k ty ps -> do
          -- assume that type is analysed
          mt <- resolve trm
          recurse $ TypedTerm (fromMaybe trm mt) k ty ps
        _ -> error ("iterCharts: " ++ show t)

-- * equation stuff
resolveCaseEq :: ProgEq -> State Env (Maybe ProgEq)
resolveCaseEq (ProgEq p t ps) = do
    mp <- resolve p
    case mp of
      Nothing -> return Nothing
      Just newP -> do
        let bs = extractVars newP
        checkUniqueVars bs
        vs <- gets localVars
        mapM_ (addLocalVar False) bs
        mtt <- resolve t
        putLocalVars vs
        return $ case mtt of
          Nothing -> Nothing
          Just newT -> Just $ ProgEq newP newT ps

resolveCaseEqs :: [ProgEq] -> State Env [ProgEq]
resolveCaseEqs eqs = case eqs of
    [] -> return []
    eq : rt -> do
      mEq <- resolveCaseEq eq
      reqs <- resolveCaseEqs rt
      return $ case mEq of
        Nothing -> reqs
        Just newEq -> newEq : reqs

resolveLetEqs :: [ProgEq] -> State Env [ProgEq]
resolveLetEqs eqs = case eqs of
    [] -> return []
    ProgEq pat trm ps : rt -> do
      mPat <- resolve pat
      case mPat of
        Nothing -> do
          resolve trm
          resolveLetEqs rt
        Just newPat -> do
          let bs = extractVars newPat
          checkUniqueVars bs
          mapM_ (addLocalVar False) bs
          mTrm <- resolve trm
          case mTrm of
            Nothing -> resolveLetEqs rt
            Just newTrm -> do
              reqs <- resolveLetEqs rt
              return $ ProgEq newPat newTrm ps : reqs

mkPatAppl :: Term -> Term -> Range -> Term
mkPatAppl op arg qs = case op of
    QualVar (VarDecl i (MixfixType []) _ _) -> ResolvedMixTerm i [] [arg] qs
    _ -> ApplTerm op arg qs

bracketTermToTypes :: Env -> Term -> [Type]
bracketTermToTypes e t = case t of
    BracketTerm Squares tys _ ->
      map (monoType . snd) $ fromMaybe (error "bracketTermToTypes")
      $ maybeResult $ mapM ( \ ty -> anaTypeM (Nothing, ty) e)
      $ fromMaybe (error "bracketTermToTypes1") $ mapM termToType tys
    _ -> error "bracketTermToTypes2"

toMixTerm :: Env -> Id -> [Term] -> Range -> Term
toMixTerm e i ar qs
  | i == applId = assert (length ar == 2) $
           let [op, arg] = ar in mkPatAppl op arg qs
  | elem i [tupleId, unitId] = mkTupleTerm ar qs
  | otherwise = case unPolyId i of
      Just j@(Id ts _ _) -> if isMixfix j && isSingle ar then
          ResolvedMixTerm j (bracketTermToTypes e $ head ar) [] qs
        else assert (length ar == 1 + placeCount j) $
        let (far, tar : sar) =
                splitAt (placeCount $ mkId $ fst $ splitMixToken ts) ar
        in ResolvedMixTerm j (bracketTermToTypes e tar) (far ++ sar) qs
      _ -> ResolvedMixTerm i [] ar qs

getKnowns :: Id -> Set.Set Token
getKnowns (Id ts cs _) =
    Set.union (Set.fromList ts) $ Set.unions $ map getKnowns cs

resolve :: Term -> State Env (Maybe Term)
resolve trm = do
    e <- get
    let ass = assumps e
        ga = globAnnos e
        (addRule, ruleS, sIds) = makeRules ga (preIds e) (getPolyIds ass)
                 $ Set.union (Map.keysSet $ binders e)
                 $ Set.union (Map.keysSet ass)
                 $ Map.keysSet $ localVars e
    chart <- iterateCharts ga sIds (getCompoundLists e) [trm]
      $ initChart addRule ruleS
    let Result ds mr = getResolved (showDoc . parenTerm) (getRange trm)
          (toMixTerm e) chart
    addDiags ds
    return mr

getPolyIds :: Assumps -> Set.Set Id
getPolyIds = Set.unions . map ( \ (i, s) ->
     Set.fold ( \ oi -> case opType oi of
       TypeScheme (_ : _) _ _ -> Set.insert i
       _ -> id) Set.empty s) . Map.toList

uTok :: Token
uTok = mkSimpleId "_"

builtinIds :: [Id]
builtinIds = [unitId, parenId, tupleId, exprId, typeId, applId]

makeRules :: GlobalAnnos -> (PrecMap, Set.Set Id) -> Set.Set Id
          -> Set.Set Id -> (TokRules, Rules, Set.Set Id)
makeRules ga ps@(p, _) polyIds aIds =
    let (sIds, ids) = Set.partition isSimpleId aIds
        ks = Set.fold (Set.union . getKnowns) Set.empty ids
        rIds = Set.union ids $ Set.intersection sIds $ Set.map simpleIdToId ks
        m2 = maxWeight p + 2
    in ( \ tok -> if isSimpleToken tok && not (Set.member tok ks)
                  || tok == uTok
         then Set.singleton (simpleIdToId tok, m2, [tok])
         else Set.empty
       , partitionRules $ listRules m2 ga ++
             initRules ps (Set.toList polyIds) builtinIds (Set.toList rIds)
       , sIds)

initRules :: (PrecMap, Set.Set Id) -> [Id] -> [Id] -> [Id] -> [Rule]
initRules (p, ps) polyIds bs is =
    map ( \ i -> mixRule (getIdPrec p ps i) i)
            (bs ++ is) ++
    map ( \ i -> (protect i, maxWeight p + 3, getPlainTokenList i))
            (filter isMixfix is) ++
-- identifiers with a positive number of type arguments
    map ( \ i -> ( polyId i, getIdPrec p ps i
                 , getPolyTokenList i)) polyIds ++
    map ( \ i -> ( protect $ polyId i, maxWeight p + 3
                 , getPlainPolyTokenList i)) (filter isMixfix polyIds)
