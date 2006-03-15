{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

conversion for mixfix printing
-}

module HasCASL.MixPrint where

import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Id
import Common.ConvertLiteral
import Common.Prec

import HasCASL.As
import HasCASL.FoldTerm
import HasCASL.Builtin

import Data.List (mapAccumL)

data Weight = Weight Int Id Id Id -- top, left, right

mkTrivWeight :: Id -> Int -> Weight
mkTrivWeight i n = Weight n i i i

data ConvFuns a = ConvFuns
    { parenthesize :: [a] -> a
    , juxtapose :: [a] -> a
    , convTok :: Token -> a
    , convComp :: [Id] -> a
    , commarize :: [a] -> a
    , convertTerm :: GlobalAnnos -> a -> a
    , convId :: Id -> a
    }

toMixWeight :: GlobalAnnos
         -> SplitM a
         -> ConvFuns a
         -> a -> (a, Maybe Weight)
toMixWeight ga splt convFuns trm =
    case splt trm of
    Nothing -> (convertTerm convFuns ga trm, Nothing)
    Just (i@(Id ts cs _), aas) -> let
        newGa = addBuiltins ga
        pa = prec_annos newGa
        precs = mkPrecIntMap pa
        m = maxWeight precs
        p = getSimpleIdPrec precs i
        dw = Just $ mkTrivWeight i p
        doSplit = maybe (error "doSplit") id . splt
        mk t = (convTok convFuns t, dw)
      in if isGenNumber splt ga i aas then
             mk $ toNumber doSplit i aas
         else if isGenFrac splt ga i aas then
             mk $ toFrac doSplit aas
         else if isGenFloat splt ga i aas then
             mk $ toFloat doSplit ga aas
         else if isGenString splt ga i aas then
             mk $ toString doSplit ga i aas
         else if isGenList splt ga i aas then
             let mkList op args cl =
                     juxtapose convFuns
                         [ convId convFuns op
                         , commarize convFuns $
                                   map (convertTerm convFuns ga) args
                         , convId convFuns cl ]
             in (toMixfixList mkList doSplit ga i aas, dw)
      else let
        newArgs = map (toMixWeight ga splt convFuns) aas
        in if null newArgs || length newArgs /= placeCount i then
              case newArgs of
              [] -> (convId convFuns i, dw)
              _ -> (juxtapose convFuns [convId convFuns i,
                      parenthesize convFuns $ map fst newArgs],
                    Just $ mkTrivWeight applId (m + 1))
           else let
             parArgs = reverse $ foldl ( \ l (arg, itm) ->
                let pArg = parenthesize convFuns [arg]
                in case itm of
                Nothing -> pArg : l
                Just (Weight q ta la ra) -> (if isLeftArg i l then
                       if checkArg ARight newGa (i, p) (ta, q) ra
                       then arg else pArg
                    else if isRightArg i l then
                       if checkArg ALeft newGa (i, p) (ta, q) la
                       then arg else pArg
                    else arg) : l) [] newArgs
             leftW = if isLeftArg i [] then
                  case snd $ head newArgs of
                  Just (Weight  _ _ l _) -> nextWeight ALeft newGa i l
                  _ -> i
                  else i
             rightW = if isRightArg i $ tail newArgs then
                  case snd $ last newArgs of
                  Just (Weight _ _ _ r) -> nextWeight ARight newGa i r
                  _ -> i
                  else i
             fts = fst $ splitMixToken ts
             (rArgs, fArgs) = mapAccumL ( \ ac t ->
               if isPlace t then case ac of
                 hd : tl -> (tl, hd)
                 _ -> error "addPlainArg"
                 else (ac, convTok convFuns t)) parArgs fts
            in (juxtapose convFuns $ fArgs ++
                 (if null cs then [] else [convComp convFuns cs])
                 ++ rArgs, Just $ Weight p i
                 leftW rightW)

hsConvFuns :: ConvFuns Term
hsConvFuns = ConvFuns
    { parenthesize = parenthesizeTerms
    , commarize = \ ts -> BracketTerm NoBrackets ts nullRange
    , juxtapose = MixfixTerm
    , convertTerm = convTerm
    , convTok = TermToken
    , convComp = \ is -> BracketTerm Squares (map ideToTerm is) nullRange
    , convId = ideToTerm }

ideToTerm :: Id -> Term
ideToTerm i = ResolvedMixTerm i [] nullRange

parenthesizeTerms :: [Term] -> Term
parenthesizeTerms ts = case ts of
    trm@(QualVar _) : [] -> trm
    trm@(QualOp _ _ _ _) : [] -> trm
    trm@(TupleTerm _ _) : [] -> trm
    trm@(BracketTerm _ _ _) : [] -> trm
    trm@(ResolvedMixTerm _ [] _) : [] -> trm
    _ -> BracketTerm Parens ts nullRange

splitTerm :: Term -> Maybe (Id, [Term])
splitTerm trm = case trm of
  ResolvedMixTerm i ts _ -> case ts of
     [TupleTerm args _] | placeCount i > 1 -> Just (i, args)
     _ -> Just(i, ts)
  ApplTerm (ResolvedMixTerm i [] _) t2 _ ->
      Just (i, case t2 of
          TupleTerm ts _ | placeCount i > 1 -> ts
          _ -> [t2])
  ApplTerm t1 t2 _ -> Just(applId, [t1, t2])
  _ -> Nothing

convApplTerm :: GlobalAnnos -> Term -> Term
convApplTerm ga t = fst $ toMixWeight ga splitTerm hsConvFuns t

convProgEq :: GlobalAnnos -> ProgEq -> ProgEq
convProgEq ga (ProgEq p t q) = ProgEq (convTerm ga p) (convTerm ga t) q

convTermRec :: GlobalAnnos -> MapRec
convTermRec ga = mapRec
    { foldApplTerm = \ t _ _ _ -> convApplTerm ga t
    , foldResolvedMixTerm = \ t _ _ _ -> convApplTerm ga t
    }

convTerm :: GlobalAnnos -> Term -> Term
convTerm ga = foldTerm $ convTermRec ga

rmTypeRec :: MapRec
rmTypeRec = mapRec
    { foldQualOp = \ t _ (InstOpId i _ _) _ ps ->
                 if elem i $ map fst bList then
                    ResolvedMixTerm i [] ps else t
    , foldTypedTerm = \ _ nt q ty ps ->
           case q of
           Inferred -> nt
           _ -> case nt of
               TypedTerm _ oq oty _ | oty == ty || oq == InType -> nt
               QualVar (VarDecl _ oty _ _) | oty == ty -> nt
               _ -> TypedTerm nt q ty ps
    }

rmSomeTypes :: Term -> Term
rmSomeTypes = foldTerm rmTypeRec
