{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  unstable
Portability :  portable 

conversion for mixfix printing 
-}

module HasCASL.MixPrint where 

import Common.GlobalAnnotations
import Common.AS_Annotation
import Common.Id
import Common.Earley
import qualified Common.Lib.Map as Map

import HasCASL.As
import HasCASL.AsUtils
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

getIdBoolPrec :: PrecMap -> Id -> Bool -> Int
getIdBoolPrec (pm, r, m) i b =  if i == applId then m + 1
    else Map.findWithDefault
    (if begPlace i || endPlace i then if b then r else m
     else m + 2) i pm

applWeight :: PrecMap -> Weight
applWeight (_, _, m) = mkTrivWeight applId (m + 1)

-- the Bool indicates if Id is a predicate
toMixWeight :: GlobalAnnos 
         -> (a -> Maybe (Id, Bool, [a]))
         -> ConvFuns a
         -> a -> (a, Maybe Weight)
toMixWeight ga splt convFuns trm =
    case splt trm of 
    Nothing -> (trm, Nothing)
    Just (i@(Id ts cs _), b, aas) -> let
        newGa = addBuiltins ga
        pa = prec_annos newGa
        precs = mkPrecIntMap pa
        p = getIdBoolPrec precs i b
        newArgs = map (toMixWeight ga splt convFuns) aas
        in if placeCount i /= length aas then
           (juxtapose convFuns [convId convFuns i, 
                      parenthesize convFuns $ map fst newArgs],
            Just $ applWeight precs)
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
             (rArgs, fArgs) = mapAccumR ( \ ac t -> 
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
    , juxtapose = MixfixTerm
    , convTok = TermToken
    , convComp = \ is -> BracketTerm Squares (map ideToTerm is) nullRange
    , convId = ideToTerm }

ideToTerm :: Id -> Term
ideToTerm i = ResolvedMixTerm i [] nullRange

parenthesizeTerms :: [Term] -> Term
parenthesizeTerms ts = case ts of 
    trm@(QualVar _) : [] -> trm
    trm@(QualOp _ _ _ _) : [] -> trm
    _ -> BracketTerm Parens ts nullRange

splitTerm :: Term -> Maybe (Id, Bool, [Term])
splitTerm trm = case trm of
  ResolvedMixTerm i ts _ -> Just(i, False, ts)
  ApplTerm (ResolvedMixTerm i [] _) t2 _ -> 
      case getTupleArgs t2 of
      Just ts -> Just(i, False, ts)
      _ -> Just(i, False, [t2]) 
  ApplTerm t1 t2 _ -> Just(applId, False, [t1, t2])
  _ -> Nothing

convApplTerm :: GlobalAnnos -> Term -> Term
convApplTerm ga t = fst $ toMixWeight ga splitTerm hsConvFuns t

convProgEq :: GlobalAnnos -> ProgEq -> ProgEq
convProgEq ga (ProgEq p t q) = ProgEq (convTerm ga p) (convTerm ga t) q

convTerm :: GlobalAnnos -> Term -> Term
convTerm ga trm = case trm of
    ResolvedMixTerm n ts ps -> 
        ResolvedMixTerm n (map (convTerm ga) ts) ps
    ApplTerm t1 t2 ps -> 
        convApplTerm ga $ ApplTerm (convTerm ga t1) (convTerm ga t2) ps
    TupleTerm ts ps -> TupleTerm (map (convTerm ga) ts) ps
    TypedTerm t q typ ps -> let nt = convTerm ga t in
           case q of 
           Inferred -> nt 
           _ -> TypedTerm nt q typ ps
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
    QualOp _ _ _ _ -> trm

