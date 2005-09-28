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
import Common.Earley
import qualified Common.Lib.Map as Map

import HasCASL.As
import HasCASL.Le
import HasCASL.Builtin

import Data.Maybe
import Data.List

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

checkMyArg :: AssocEither -> GlobalAnnos -> (Id, Int) 
           -> (Id, Int) -> Id -> Bool
checkMyArg side ga (op, opPrec) (arg, argPrec) weight =
    let precs = prec_annos ga
        assocs = assoc_annos ga
    in if argPrec <= 0 then False
       else case compare argPrec opPrec of 
           LT -> False
           GT -> True
           EQ -> if joinPlace side arg then
               case precRel precs op weight of
               Lower -> True
               Higher -> False
               BothDirections -> False
               NoDirection -> 
                   case (isInfix arg, joinPlace side op) of 
                        (True, True) -> if arg == op 
                                        then not $ isAssoc side assocs op
                                        else True
                        (False, True) -> True
                        (True, False) -> False
                        _ -> side == ALeft
            else True

getSimpleIdPrec :: PrecMap -> Id -> Int
getSimpleIdPrec (pm, _, m) i =  if i == applId then m + 1
    else Map.findWithDefault
    (if begPlace i || endPlace i then m
     else m + 2) i pm

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
        precs@(_, _, m) = mkPrecIntMap pa
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
        n = length aas
        in if null aas || placeCount i /= n then
              case aas of
              [] -> (convId convFuns i, dw)
              _ -> (juxtapose convFuns [convId convFuns i, 
                      parenthesize convFuns $ map fst newArgs],
                    Just $ mkTrivWeight applId (m + 1)) 
           else let 
             parArgs = zipWith ( \ (arg, itm) num ->
                let pArg = parenthesize convFuns [arg]
                in case itm of
                Nothing -> pArg
                Just (Weight q ta la ra) -> if isLeftArg i num then 
                       if checkMyArg ARight newGa (i, p) (ta, q) ra 
                       then arg else pArg
                    else if isRightArg i num then
                       if checkMyArg ALeft newGa (i, p) (ta, q) la
                       then arg else pArg
                    else arg) newArgs [0 .. ]
             leftW = if isLeftArg i 0 then
                  case snd $ head newArgs of
                  Just (Weight  _ _ l _) -> if begPlace l then 
                        case precRel pa i l of
                        Higher -> l
                        _ -> i
                        else i
                  _ -> i
                  else i
             rightW = if isRightArg i (length newArgs - 1) then
                  case snd $ last newArgs of
                  Just (Weight _ _ _ r) -> if endPlace r then 
                        case precRel pa i r of
                        Higher -> r
                        _ -> i
                        else i
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
     [TupleTerm args _] -> Just (i, args)
     _ -> Just(i, ts)
  ApplTerm (ResolvedMixTerm i [] _) (TupleTerm ts _) _ -> Just(i, ts) 
  ApplTerm t1 t2 _ -> Just(applId, [t1, t2])
  _ -> Nothing

convApplTerm :: GlobalAnnos -> Term -> Term
convApplTerm ga t = fst $ toMixWeight ga splitTerm hsConvFuns t

convProgEq :: GlobalAnnos -> ProgEq -> ProgEq
convProgEq ga (ProgEq p t q) = ProgEq (convTerm ga p) (convTerm ga t) q

convTerm :: GlobalAnnos -> Term -> Term
convTerm ga trm = case trm of
    QualOp _ (InstOpId i _ _) _ ps -> if elem i $ map fst bList then 
        ResolvedMixTerm i [] ps else trm
    ResolvedMixTerm _ _ _ -> convApplTerm ga trm
    ApplTerm _ _ _ -> convApplTerm ga trm
    TupleTerm ts ps -> TupleTerm (map (convTerm ga) ts) ps
    TypedTerm t q ty ps -> let nt = convTerm ga t in
           case q of 
           Inferred -> nt 
           _ -> case nt of 
               TypedTerm _ oq oty _ | oty == ty || oq == InType -> nt
               QualVar (VarDecl _ oty _ _) | oty == ty -> nt 
               _ -> TypedTerm nt q ty ps
    QuantifiedTerm q vs t ps -> QuantifiedTerm q vs (convTerm ga t) ps
    LambdaTerm ps q t qs -> 
        LambdaTerm (map (convTerm ga) ps) q (convTerm ga t) qs
    CaseTerm t es ps -> CaseTerm (convTerm ga t) (map (convProgEq ga) es) ps 
    LetTerm br es t ps -> 
        LetTerm br (map (convProgEq ga) es) (convTerm ga t) ps
    MixfixTerm ts -> MixfixTerm $ map (convTerm ga) ts
    BracketTerm k ts ps -> BracketTerm k (map (convTerm ga) ts) ps
    AsPattern v p ps -> AsPattern v (convTerm ga p) ps
    TermToken _ -> trm
    MixTypeTerm _ _ _ -> trm
    QualVar _ -> trm

