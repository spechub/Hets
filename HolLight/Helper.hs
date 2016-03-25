{- |
Module      :  ./HolLight/Helper.hs
Description :  Helper functions for dealing with terms
                (mainly for pretty printing which is
                 directly adapted from hollight)
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module HolLight.Helper where

import Data.Maybe (fromJust, isJust, catMaybes)
import HolLight.Term
import Data.List (union, (\\), find)
import Common.Doc
import Data.Char as Char

names :: [String]
names =
 let
  nextName [] = "a"
  nextName (x : xs) = if Char.ord x >= 122
                     then 'a' : nextName xs
                     else Char.chr (Char.ord x + 1) : xs
 in iterate (reverse . nextName . reverse) "a"

freeName :: [String] -> String
freeName ns = head (filter (\ x -> case find (== x) ns
                              of Nothing -> True
                                 _ -> False) names)

fromRight :: Either t t1 -> t1
fromRight e = case e of
  Right t -> t
  Left _ -> error "fromRight"

isPrefix :: Term -> Bool
isPrefix tm = case tm of
  Var _ _ (HolTermInfo (PrefixT, _)) -> True
  Const _ _ (HolTermInfo (PrefixT, _)) -> True
  _ -> False

ppPrintType :: HolType -> Doc
ppPrintType = sot 0

soc :: String -> Bool -> [Doc] -> Doc
soc sep' flag ss = if null ss then empty
  else let s = foldr1 (\ s1 s2 -> hcat [s1, text sep', s2]) ss
       in if flag then parens s else s

sot :: Int -> HolType -> Doc
sot pr ty = case (destVartype ty, destType ty) of
  -- exactly one of these is not Nothing
  (Just vtype, _) -> text vtype
  (_, Just t) -> case t of
    (con, []) -> text con
    ("fun", [ty1, ty2]) -> soc "->" (pr > 0) [sot 1 ty1, sot 0 ty2]
    ("sum", [ty1, ty2]) -> soc "+" (pr > 2) [sot 3 ty1, sot 2 ty2]
    ("prod", [ty1, ty2]) -> soc "#" (pr > 4) [sot 5 ty1, sot 4 ty2]
    ("cart", [ty1, ty2]) -> soc "^" (pr > 6) [sot 6 ty1, sot 7 ty2]
    (con, args) -> hcat [soc "," True (map (sot 0) args), text con]
  _ -> empty -- doesn't happen

-- lib.ml
revAssocd :: Eq t1 => t1 -> [(t, t1)] -> t -> t
revAssocd a l d = case l of
  [] -> d
  (x, y) : t -> if y == a then x
                       else revAssocd a t d

-- fusion.ml
destVar :: Term -> Maybe (String, HolType)
destVar v = case v of
  Var s ty _ -> Just (s, ty)
  _ -> Nothing

isVar :: Term -> Bool
isVar v = isJust (destVar v)

frees :: Term -> [Term]
frees tm = case tm of
  Var {} -> [tm]
  Const {} -> []
  Abs bv bod -> frees bod \\ [bv]
  Comb s t -> frees s `union` frees t

vfreeIn :: Term -> Term -> Bool
vfreeIn v tm = case tm of
  Abs bv bod -> v /= bv && vfreeIn v bod
  Comb s t -> vfreeIn v s || vfreeIn v t
  _ -> tm == v

variant :: [Term] -> Term -> Maybe Term
variant avoid v = if not (any (vfreeIn v) avoid) then Just v
                  else case v of
                         Var s ty p -> variant avoid (Var (s ++ "'") ty p)
                         _ -> Nothing

vsubst :: [(Term, Term)] -> Term -> Maybe Term
vsubst =
  let vsubst' ilist tm = case tm of
                           Var {} -> Just $ revAssocd tm ilist tm
                           Const {} -> Just tm
                           Comb s t -> case (vsubst' ilist s, vsubst ilist t) of
                             (Just s', Just t') -> Just $ if s' == s && t' == t
                                                  then tm
                                                  else Comb s' t'
                             _ -> Nothing
                           Abs v s -> let ilist' = filter (\ (_, x) -> x /= v)
                                                          ilist
                             in if null ilist' then Just tm
                                else case vsubst ilist' s of
                                  Just s' | s' == s -> Just tm
                                          | any (\ (t, x) -> vfreeIn v t
                                                            && vfreeIn x s)
                                                ilist' ->
                                            case variant [s'] v of
                                                Just v' -> case vsubst
                                                 ((v', v) : ilist') s of
                                                  Just t' ->
                                                   Just (Abs v' t')
                                                  _ -> Nothing
                                                _ -> Nothing
                                          | otherwise -> Just (Abs v s')
                                  _ -> Nothing
  in \ theta ->
    if null theta then Just else
    if all (\ (t, x) -> case (typeOf t, destVar x) of
                         (Just t', Just (_, x')) -> t' == x'
                         _ -> False) theta then vsubst' theta
    else const Nothing

destComb :: Term -> Maybe (Term, Term)
destComb c = case c of
  Comb f x -> Just (f, x)
  _ -> Nothing

isComb :: Term -> Bool
isComb c = isJust (destComb c)

destConst :: Term -> Maybe (String, HolType)
destConst c = case c of
  Const s ty _ -> Just (s, ty)
  _ -> Nothing

isConst :: Term -> Bool
isConst c = isJust (destConst c)

destAbs :: Term -> Maybe (Term, Term)
destAbs a = case a of
  Abs v b -> Just (v, b)
  _ -> Nothing

isAbs :: Term -> Bool
isAbs a = isJust (destAbs a)

rator :: Term -> Maybe Term
rator tm = fmap fst (destComb tm)

rand :: Term -> Maybe Term
rand tm = fmap snd (destComb tm)

splitlist :: (t -> Maybe (a, t)) -> t -> ([a], t)
splitlist dest x = case dest x of
  Just (l, r) -> let (ls, res) = splitlist dest r
                in (l : ls, res)
  _ -> ([], x)

revSplitlist :: (t -> Maybe (t, t1)) -> t -> (t, [t1])
revSplitlist dest x =
  let rsplist ls x' = case dest x' of
                       Just (l, r) -> rsplist (r : ls) l
                       _ -> (x', ls)
  in rsplist [] x

typeOf :: Term -> Maybe HolType
typeOf tm = case tm of
  Var _ ty _ -> Just ty
  Const _ ty _ -> Just ty
  Comb s _ -> case typeOf s of
                Just t -> case destType t of
                            Just (_, _ : x1 : _) -> Just x1
                            _ -> Nothing
                _ -> Nothing
  Abs (Var _ ty _) t -> case typeOf t of
                         Just t' -> Just (TyApp "fun" [ty, t'])
                         _ -> Nothing
  _ -> Nothing

destType :: HolType -> Maybe (String, [HolType])
destType a = case a of
  TyApp s ty -> Just (s, ty)
  _ -> Nothing

destVartype :: HolType -> Maybe String
destVartype t = case t of
  TyVar s -> Just s
  _ -> Nothing

typeSubst :: [(HolType, HolType)] -> HolType -> HolType
typeSubst i ty = case ty of
  TyApp tycon args -> let args' = map (typeSubst i) args
                      in if args' == args then ty else TyApp tycon args'
  _ -> revAssocd ty i ty

mkEq :: (Term, Term) -> Maybe Term
mkEq (l, r) = case (typeOf l, mkConst ("=", [])) of
               (Just ty, Just eq) -> case inst [(ty, TyVar "A")] eq of
                                Right eq_tm -> case mkComb (eq_tm, l) of
                                  Just m1 -> mkComb (m1, r)
                                  _ -> Nothing
                                _ -> Nothing
               _ -> Nothing

inst :: [(HolType, HolType)] -> Term -> Either Term Term
inst =
  let inst' env tyin tm = case tm of
                            Var n ty at -> let ty' = typeSubst tyin ty
                              in let tm' = if ty' == ty then tm
                                           else Var n ty' at
                                 in if revAssocd tm' env tm == tm
                                    then Right tm'
                                    else Left tm'
                            Const c ty at -> let ty' = typeSubst tyin ty
                              in Right $ if ty' == ty
                                 then tm
                                 else Const c ty' at
                            Comb f x -> case (inst' env tyin f,
                                              inst' env tyin x) of
                                          (Right f', Right x') ->
                                           Right $ if f' == f && x' == x
                                                   then tm else Comb f' x'
                                          (Left c, _) -> Left c
                                          (_, Left c) -> Left c
                            Abs y t -> case inst' [] tyin y of
                              Right y' -> let env' = (y, y') : env
                                in case inst' env' tyin t of
                                     Right t' ->
                                      Right $ if y' == y && t' == t
                                       then tm else Abs y' t'
                                     Left w' -> if w' /= y'
                                       then Left w'
                                       else let ifrees = map (fromRight .
                                                               inst' [] tyin)
                                                              (frees t) in
                                             case variant ifrees y' of
                                               Just y'' ->
                                                case (destVar y'', destVar y) of
                                                 (Just (v1, _), Just (_, v2)) ->
                                                  let z = Var v1 v2
                                                           (HolTermInfo
                                                           (Normal, Nothing))
                                                  in case vsubst [(z, y)] t of
                                                      Just s -> inst' env tyin
                                                       (Abs z s)
                                                      _ -> Left w'
                                                 _ -> Left w'
                                               _ -> Left w'
                              _ -> Left tm
  in (\ tyin -> if null tyin then Right else inst' [] tyin)

mkComb :: (Term, Term) -> Maybe Term
mkComb (f, a) = case typeOf f of
  Just (TyApp "fun" [ty, _]) -> case typeOf a of
    Just t -> if ty == t then Just (Comb f a) else Nothing
    _ -> Nothing
  _ -> Nothing

eqType :: HolType
eqType = TyApp "fun" [
  TyVar "A",
  TyApp "fun" [
    TyVar "A",
    TyApp "bool" []
  ]]

mkConst :: (String, [(HolType, HolType)]) -> Maybe Term
mkConst (name, theta) = if name == "="
                        then Just (Const name
                                   (typeSubst theta eqType)
                                   (HolTermInfo (InfixR 12, Nothing)))
                        else Nothing

-- basics.ml
destBinder :: String -> Term -> Maybe (Term, Term)
destBinder s tm = case tm of
  Comb (Const s' _ _) (Abs x t) ->
    if s' == s then Just (x, t)
    else Nothing
  _ -> Nothing

destExists :: Term -> Maybe (Term, Term)
destExists = destBinder "?"

stripExists :: Term -> ([Term], Term)
stripExists = splitlist destExists

destForall :: Term -> Maybe (Term, Term)
destForall = destBinder "!"

stripForall :: Term -> ([Term], Term)
stripForall = splitlist destForall

stripComb :: Term -> (Term, [Term])
stripComb = revSplitlist destComb

body :: Term -> Maybe Term
body tm = case destAbs tm of
  Just (_, ret) -> Just ret
  _ -> Nothing

destNumeral :: Term -> Maybe Integer
destNumeral tm' =
  let dest_num tm = case destConst tm of
                      Just ("_0", _) -> Just (toInteger (0 :: Int))
                      _ -> case destComb tm of
                             Just (l, r) -> case dest_num r of
                                             Just i ->
                                               let n = toInteger (2 :: Int) * i
                                               in case destConst l of
                                                    Just ("BIT0", _) -> Just n
                                                    Just ("BIT1", _) -> Just (n
                                                      + toInteger (1 :: Int))
                                                    _ -> Nothing
                                             _ -> Nothing
                             _ -> Nothing
  in case destComb tm' of
       Just (l, r) -> case destConst l of
                     Just ("NUMERAL", _) -> dest_num r
                     _ -> Nothing
       _ -> Nothing

destBinary' :: String -> Term -> Maybe (Term, Term)
destBinary' s tm = case tm of
  Comb (Comb (Const s' _ _) l) r -> if s' == s then Just (l, r)
                                  else Nothing
  _ -> Nothing

destCons :: Term -> Maybe (Term, Term)
destCons = destBinary' "CONS"

destList :: Term -> Maybe [Term]
destList tm = let (tms, nil) = splitlist destCons tm
               in case destConst nil of
                    Just ("NIL", _) -> Just tms
                    _ -> Nothing

destGabs :: Term -> Maybe (Term, Term)
destGabs tm =
  let dest_geq = destBinary' "GEQ"
  in if isAbs tm then destAbs tm
     else case destComb tm of
            Just (l, r) -> case destConst l of
                            Just ("GABS", _) -> case body r of
                              Just b -> case dest_geq (snd (stripForall b)) of
                                Just (ltm, rtm) -> case rand ltm of
                                  Just r' -> Just (r', rtm)
                                  _ -> Nothing
                                _ -> Nothing
                              _ -> Nothing
                            _ -> Nothing
            _ -> Nothing

isGabs :: Term -> Bool
isGabs tm = isJust (destGabs tm)

stripGabs :: Term -> ([Term], Term)
stripGabs = splitlist destGabs

destFunTy :: HolType -> Maybe (HolType, HolType)
destFunTy ty = case ty of
  TyApp "fun" [ty1, ty2] -> Just (ty1, ty2)
  _ -> Nothing

destLet :: Term -> Maybe ([(Term, Term)], Term)
destLet tm = let (l, aargs) = stripComb tm
              in case (aargs, destConst l) of
                   (a : as, Just ("LET", _)) ->
                     let (vars, lebod) = stripGabs a
                     in let eqs = zip vars as
                        in case destComb lebod of
                             Just (le, bod) -> case destConst le of
                              Just ("LET_END", _) -> Just (eqs, bod)
                              _ -> Nothing
                             _ -> Nothing
                   _ -> Nothing

-- printer.ml
nameOf :: Term -> String
nameOf tm = case tm of
  Var x _ _ -> x
  Const x _ _ -> x
  _ -> ""

-- printer.ml - pp_print_term
reverseInterface :: (String, Term) -> (String, Maybe HolParseType)
reverseInterface (s, tm) = case tm of
  Var _ _ ti -> case ti of
    HolTermInfo (_, Just (s'', pt)) -> (s'', Just pt)
    _ -> (s, Nothing)
  Const _ _ ti -> case ti of
    HolTermInfo (_, Just (s'', pt)) -> (s'', Just pt)
    _ -> (s, Nothing)
  _ -> (s, Nothing)

destBinary :: Term -> Term -> Maybe (Term, Term)
destBinary c tm = case destComb tm of -- original name: DEST_BINARY
  Just (il, r) -> case destComb il of
    Just (i, l) -> if (i == c) ||
      (isConst i && isConst c &&
       (fst (reverseInterface (fst (fromJust (destConst i)), i))
       == fst (reverseInterface (fst (fromJust (destConst c)), i))))
      then Just (l, r)
      else Nothing
    _ -> Nothing
  _ -> Nothing

powerof10 :: Integer -> Bool
powerof10 n = (10 * div n 10) == n

boolOfTerm :: Term -> Maybe Bool
boolOfTerm t = case t of
  Const "T" _ _ -> Just True
  Const "F" _ _ -> Just False
  _ -> Nothing

codeOfTerm :: Num b => Term -> Maybe b
codeOfTerm t =
  let (f, tms) = stripComb t in
  if not (isConst f && fst (fromJust (destConst f)) == "ASCII")
     || length tms /= 8
  then Nothing
  else let bools = map boolOfTerm (reverse tms)
       in if notElem Nothing bools then
          Just (foldr (\ b f' -> if b then 1 + 2 * f' else 2 * f')
                0 (catMaybes bools))
          else Nothing

randRator :: Term -> Maybe Term
randRator v = case rator v of
  Just v1 -> rand v1
  _ -> Nothing

destClause :: Term -> Maybe [Term]
destClause tm = case fmap stripExists (maybe Nothing body (body tm)) of
  Just (_, pbod) -> let (s, args) = stripComb pbod
                   in case (nameOf s, length args) of
                     ("_UNGUARDED_PATTERN", 2) ->
                       case (randRator (head args),
                             randRator (args !! 1)) of
                         (Just _1, Just _2) -> Just [_1, _2]
                         _ -> Nothing
                     ("_GUARDED_PATTERN", 3) ->
                       case (randRator (head args),
                             randRator (args !! 2)) of
                         (Just _1, Just _3) -> Just [_1, args !! 1, _3]
                         _ -> Nothing
                     _ -> Nothing
  _ -> Nothing

destClauses :: Term -> Maybe [[Term]]
destClauses tm = let (s, args) = stripComb tm
                  in if nameOf s == "_SEQPATTERN" && length args == 2
                     then case destClauses (args !! 1) of
                       Just cs -> case destClause (head args) of
                         Just c -> Just (c : cs)
                         _ -> Nothing
                       _ -> Nothing
                     else case destClause tm of
                       Just c -> Just [c]
                       _ -> Nothing

aright :: Term -> Bool
aright tm = case tm of
  Var _ _ (HolTermInfo (InfixR _, _)) -> True
  Const _ _ (HolTermInfo (InfixR _, _)) -> True
  _ -> False

getPrec :: Term -> Int
getPrec tm = case tm of
  Var _ _ (HolTermInfo (InfixR i, _)) -> i
  Const _ _ (HolTermInfo (InfixR i, _)) -> i
  _ -> 0

parsesAsBinder :: Term -> Bool
parsesAsBinder tm = case tm of
  Var _ _ (HolTermInfo (Binder, _)) -> True
  Const _ _ (HolTermInfo (Binder, _)) -> True
  _ -> False

canGetInfixStatus :: Term -> Bool
canGetInfixStatus tm = case tm of
  Var _ _ (HolTermInfo (InfixR _, _)) -> True
  Var _ _ (HolTermInfo (InfixL _, _)) -> True
  Const _ _ (HolTermInfo (InfixR _, _)) -> True
  Const _ _ (HolTermInfo (InfixL _, _)) -> True
  _ -> False
