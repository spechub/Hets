
{- HetCATS/HasCASL/TypeInference.hs
   $Id$
   Author:  Christian Maeder
   Year:    2002

   polymorphic type inference (with type classes) for terms

   limitiations:
   - no subtyping

   - ignore anonymous downsets as classes
   - an intersection class is a (flat) set of class names (without universe)

   - no mixfix analysis for types yet

   - use predicate types as in Wadler/Blott 1989 (ad-hoc polymorphism)?

   to do:
   - convert As.Type to Le.Type

   plan:
   - treat all arrows equal for unification and type inference
   - and also ignore lazy annotations!
  
   simply adapt the following

-- Part of `Typing Haskell in Haskell', version of November 23, 2000
-- Copyright (c) Mark P Jones and the Oregon Graduate Institute
-- of Science and Technology, 1999-2000
-- 
-- This program is distributed as Free Software under the terms
-- in the file "License" that is included in the distribution
-- of this software, copies of which may be obtained from:
--             http://www.cse.ogi.edu/~mpj/thih/

-}
module TypeInference where

import Id
import Le
import As
import AsToLe
import FiniteMap
import List -- (nub, (\\), intersect, union, partition)
import Monad(msum)
import MonadState

enumId  :: Int -> Id
enumId n = Id[Token "v" nullPos, Token (show n) nullPos][][]

tArrow :: Le.Type
tArrow   = TCon (Tycon (Id [Token "->?" nullPos][][]) 
		 (Kfun star (Kfun star star)))

infixr      4 `fn`
fn         :: Le.Type -> Le.Type -> Le.Type
a `fn` b    = TAp (TAp tArrow a) b

class HasKind t where
  kind :: t -> Le.Kind
instance HasKind Tyvar where
  kind (Tyvar _ k) = k
instance HasKind Tycon where
  kind (Tycon _ k) = k
instance HasKind Le.Type where
  kind (TCon tc) = kind tc
  kind (TVar u)  = kind u
  kind (TAp t _) = case (kind t) of
                     Kfun _ k -> k
		     Star _ -> error "wrong kind for TAp"
  kind (TGen _) = error "no kind for TGen"

-----------------------------------------------------------------------------
-- Subst:	Substitutions
-----------------------------------------------------------------------------

type Subst  = FiniteMap Tyvar Le.Type

nullSubst  :: Subst
nullSubst   = emptyFM

(+->)      :: Tyvar -> Le.Type -> Subst
u +-> t     = unitFM u t

class SubstApplicable t where
  apply :: Subst -> t -> t
  tv    :: t -> [Tyvar]

instance SubstApplicable Le.Type where
  apply s (TVar u)  = case lookupFM s u of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TAp l r) = TAp (apply s l) (apply s r)
  apply _ t         = t

  tv (TVar u)  = [u]
  tv (TAp l r) = tv l `union` tv r
  tv _         = []

instance SubstApplicable a => SubstApplicable [a] where
  apply s = map (apply s)
  tv      = nub . concat . map tv

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = plusFM (mapFM (const $ apply s1) s2) s1

-----------------------------------------------------------------------------
-- Unify:	Unification
-----------------------------------------------------------------------------

mgu, match :: Monad m => Le.Type -> Le.Type -> m Subst
mgum :: Monad m => Bool -> Le.Type -> Le.Type -> m Subst

mgu = mgum False
match = mgum True

mgum b (TAp l r) (TAp l' r') = do s1 <- mgum b l l'
				  s2 <- mgum b (apply s1 r) 
					(if b then r' else apply s1 r')
				  return (s2 @@ s1)
mgum _ (TVar u) t        = varBind u t
mgum b t (TVar u)        = if b then fail 
			   "a non-variable does not match a variable" 
			   else varBind u t
mgum _ (TCon tc1) (TCon tc2)
           | tc1==tc2 = return nullSubst
mgum b _ _   = fail ("types do not " ++ if b then "match" else "unify")

varBind :: Monad m => Tyvar -> Le.Type -> m Subst
varBind u t | t == TVar u      = return nullSubst
            | u `elem` tv t    = fail "occurs check fails"
            | kind u /= kind t = fail "kinds do not match"
            | otherwise        = return (u +-> t)

-----------------------------------------------------------------------------
-- Pred:		Predicates
-----------------------------------------------------------------------------

instance SubstApplicable t => SubstApplicable (Qual t) where
  apply s (ps :=> t) = apply s ps :=> apply s t
  tv (ps :=> t)      = tv ps `union` tv t

instance SubstApplicable Pred where
  apply s (IsIn i t) = IsIn i (apply s t)
  tv (IsIn _ t)      = tv t

mguPred, matchPred :: Pred -> Pred -> Maybe Subst
mguPred             = liftToPred mgu
matchPred           = liftToPred match

liftToPred :: Monad m => (Le.Type -> Le.Type -> m Subst) 
	   -> Pred -> Pred -> m Subst
liftToPred m (IsIn i t) (IsIn i' t')
         | i == i'   = m t t'
         | otherwise = fail "classes differ"

type ClassInst    = ([Id], [Inst]) -- super classes and instances
type Inst     = Qual Pred

-----------------------------------------------------------------------------

type ClassEnv = FiniteMap Id ClassInst

super     :: ClassEnv -> Id -> [Id]
super ce i = case lookupFM ce i of Just (is, _) -> is
				   Nothing -> []

insts     :: ClassEnv -> Id -> [Inst]
insts ce i = case lookupFM ce i of Just (_, its) -> its
				   Nothing -> []

defined :: Maybe a -> Bool
defined (Just _) = True
defined Nothing  = False

type EnvTransformer = ClassEnv -> Maybe ClassEnv

infixr 5 <:>
(<:>)       :: EnvTransformer -> EnvTransformer -> EnvTransformer
(f <:> g) ce = do ce' <- f ce
                  g ce'

addClass                              :: Id -> [Id] -> EnvTransformer
addClass i is ce
 | i `elemFM` ce                       = fail "class already defined"
 | not $ null $ is \\ keysFM ce        = fail "superclass not defined"
 | otherwise                           = return (addToFM ce i (is, []))

addPreludeClasses :: EnvTransformer
addPreludeClasses  = addCoreClasses

addCoreClasses ::   EnvTransformer
addCoreClasses  =   const Nothing

addInst                        :: [Pred] -> Pred -> EnvTransformer
addInst ps p@(IsIn i _) ce
 | not $ i `elemFM` ce          = fail "no class for instance"
 | any (overlap p) qs           = fail "overlapping instance"
 | otherwise                    = return (addToFM ce i c)
   where its = insts ce i
         qs  = [ q | (_ :=> q) <- its ]
         c   = (super ce i, (ps:=>p) : its)

overlap       :: Pred -> Pred -> Bool
overlap p q    = defined (mguPred p q)

exampleInsts ::  EnvTransformer
exampleInsts =   addPreludeClasses

-----------------------------------------------------------------------------

bySuper :: ClassEnv -> Pred -> [Pred]
bySuper ce p@(IsIn i t)
 = p : concat [ bySuper ce (IsIn i' t) | i' <- super ce i ]

byInst                   :: ClassEnv -> Pred -> Maybe [Pred]
byInst ce p@(IsIn i _)    = msum [ tryInst it | it <- insts ce i ]
 where tryInst (ps :=> h) = do u <- matchPred h p
                               Just (map (apply u) ps)

entail        :: ClassEnv -> [Pred] -> Pred -> Bool
entail ce ps p = any (p `elem`) (map (bySuper ce) ps) ||
                 case byInst ce p of
                   Nothing -> False
                   Just qs -> all (entail ce ps) qs

-----------------------------------------------------------------------------

inHnf       :: Pred -> Bool
inHnf (IsIn _ t) = hnf t
 where hnf (TVar _)  = True
       hnf (TCon _) = False
       hnf (TAp f _) = hnf f
       hnf (TGen _) = error "no hnf for TGen"

toHnfs      :: Monad m => ClassEnv -> [Pred] -> m [Pred]
toHnfs ce ps = do pss <- mapM (toHnf ce) ps
                  return (concat pss)

toHnf                 :: Monad m => ClassEnv -> Pred -> m [Pred]
toHnf ce p | inHnf p   = return [p]
           | otherwise = case byInst ce p of
                           Nothing -> fail "context reduction"
                           Just ps -> toHnfs ce ps

simplify   :: ClassEnv -> [Pred] -> [Pred]
simplify ce = loop []
 where loop rs []                            = rs
       loop rs (p:ps) | entail ce (rs++ps) p = loop rs ps
                      | otherwise            = loop (p:rs) ps

reduce      :: Monad m => ClassEnv -> [Pred] -> m [Pred]
reduce ce ps = do qs <- toHnfs ce ps
                  return (simplify ce qs)

scEntail        :: ClassEnv -> [Pred] -> Pred -> Bool
scEntail ce ps p = any (p `elem`) (map (bySuper ce) ps)

-----------------------------------------------------------------------------
-- Scheme:	Type schemes
-----------------------------------------------------------------------------

instance SubstApplicable Scheme where
  apply s (Scheme ks qt) = Scheme ks (apply s qt)
  tv (Scheme _ qt)      = tv qt

quantify      :: [Tyvar] -> Qual Le.Type -> Scheme
quantify vs qt = Scheme ks (apply (listToFM s) qt)
 where vs' = [ v | v <- tv qt, v `elem` vs ]
       ks  = map kind vs'
       s   = zip vs' (map TGen [0..])

toScheme      :: Le.Type -> Scheme
toScheme t     = Scheme [] ([] :=> t)

-----------------------------------------------------------------------------
-- TIMonad:	Type inference monad
-----------------------------------------------------------------------------

newtype TI a = TI {ti :: Subst -> Int -> (Subst, Int, a)}

instance Monad TI where
  return x   = TI (\s n -> (s,n,x))
  TI f >>= g = TI (\s n -> case f s n of
                            (s',m,x) -> let TI gx = g x
                                        in  gx s' m)

runTI       :: Int -> TI a -> a
runTI n (TI f) = x where (_, _, x) = f nullSubst n


freshInst               :: Scheme -> TIL (Qual Le.Type)
freshInst (Scheme ks qt) = do ts <- mapM newTVar ks
                              return (inst ts qt)


class Instantiate t where
  inst  :: [Le.Type] -> t -> t
instance Instantiate Le.Type where
  inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
  inst ts (TGen n)  = ts !! n
  inst _  t         = t
instance Instantiate a => Instantiate [a] where
  inst ts = map (inst ts)
instance Instantiate t => Instantiate (Qual t) where
  inst ts (ps :=> t) = inst ts ps :=> inst ts t
instance Instantiate Pred where
  inst ts (IsIn c t) = IsIn c (inst ts t)

newTVars :: Scheme -> TIL [Le.Type]
newTVars (Scheme ks _) = 
    TIL (\ (s, n) ->
    let m = n + length(ks)
    in [((s, m), 
	 zipWith (\ k i -> (TVar (Tyvar (enumId i) k))) ks [n .. m - 1])])

type Assumps = FiniteMap Id [Scheme]

lookUp :: Ord a => FiniteMap a [b] -> a -> [b]
lookUp ce = lookupWithDefaultFM ce [] 

-- <type Til = StateT (Subst, Int) []

newtype TIL a = TIL {til :: (Subst, Int) -> [((Subst, Int), a)]}

returnL :: [a] -> TIL a
returnL l = TIL (\ s -> map (\ x -> (s, x)) l)

instance Monad TIL where
  return x = returnL [x]
  f >>= g = TIL $ concatMap (\ (s, x) -> (til $ g x) s) . til f 
  fail _ = TIL $ const []

newTVar    :: Le.Kind -> TIL Le.Type
newTVar k   = TIL (\ (s, n) -> let v = Tyvar (enumId n) k
                          in  [((s, n+1), TVar v)])

getSubst   :: TIL Subst
getSubst    = TIL (\ s -> [(s, fst s)])

unify      :: Le.Type -> Le.Type -> TIL ()
unify t1 t2 = do s <- getSubst
                 u <- mgu (apply s t1) (apply s t2)
                 extSubst u

extSubst   :: Subst -> TIL ()
extSubst s' = TIL (\ (s, n) -> [((s'@@s, n), ())])

tiTerm :: ClassEnv -> Assumps -> As.Term -> TIL (Qual Le.Type, Le.Term)
tiTerm _ as (TermToken t) = let i = simpleIdToId t
			    in 
			    do sc@(Scheme ks qs) <- returnL (lookUp as i)
			       ts <- mapM newTVar ks
                               return (inst ts qs, BaseName i sc ts) 

tiTerm ce as (ApplTerm f a _) = 
    do (q1 :=> t1, e1) <- tiTerm ce as f
       (q2 :=> t2, e2) <- tiTerm ce as a
       t3 <- newTVar star
       unify t1 (t2 `fn` t3)
       return ((q1 ++ q2) :=> t3, Application e1 e2)

{-

-----------------------------------------------------------------------------
-- TIMain:	Type Inference Algorithm
-----------------------------------------------------------------------------
-- Infer:	Basic definitions for type inference
-----------------------------------------------------------------------------


type Infer e t = ClassEnv -> Assumps -> e -> TI (Qual t)


-----------------------------------------------------------------------------
-- Pat:		Patterns
-----------------------------------------------------------------------------

data Pat        = PVar Id
                | PWildcard
                | PAs  Id Pat
                | PCon Assumps [Pat]


tiPat :: Pat -> TI (Qual Le.Type, Assumps)

tiPat (PVar i) = do v <- newTVar star
                    return ([] :=> v, unitFM (toScheme v))

tiPat PWildcard   = do v <- newTVar star
                       return ([], [], v)

tiPat (PAs i pat) = do (ps, as, t) <- tiPat pat
                       return (ps, (i:>:toScheme t):as, t)

tiPat (PCon (_:>:sc) pats) = do (ps,as,ts) <- tiPats pats
                                t'         <- newTVar star
                                (qs :=> t) <- freshInst sc
                                unify t (foldr fn t' ts)
                                return (ps++qs, as, t')

tiPats     :: [Pat] -> TI (Qual [Le.Type], Assumps)
tiPats pats = do psasts <- mapM tiPat pats
                 let ps = concat [ ps' | (ps',_,_) <- psasts ]
                     as = concat [ as' | (_,as',_) <- psasts ]
                     ts = [ t | (_,_,t) <- psasts ]
                 return (ps, as, ts)

-----------------------------------------------------------------------------

data Expr = Var   Id
          | Const Assumps
          | Ap    Expr Expr
          | Let   BindGroup Expr

tiExpr                       :: Infer Expr Le.Type
tiExpr _  as (Var i)          = do sc         <- find i as
                                   (ps :=> t) <- freshInst sc
                                   return (ps, t)
tiExpr _ _ (Const (_:>:sc))   = do (ps :=> t) <- freshInst sc
                                   return (ps, t)
tiExpr ce as (Ap e f)         = do (ps,te) <- tiExpr ce as e
                                   (qs,tf) <- tiExpr ce as f
                                   t       <- newTVar star
                                   unify (tf `fn` t) te
                                   return (ps++qs, t)
tiExpr ce as (Let bg e)       = do (ps, as') <- tiBindGroup ce as bg
                                   (qs, t)   <- tiExpr ce (as' ++ as) e
                                   return (ps ++ qs, t)

-----------------------------------------------------------------------------

type Alt = ([Pat], Expr)

tiAlt                :: Infer Alt Le.Type
tiAlt ce as (pats, e) = do (ps, as', ts) <- tiPats pats
                           (qs,t)  <- tiExpr ce (as'++as) e
                           return (ps++qs, foldr fn t ts)

tiAlts             :: ClassEnv -> [Assump] -> [Alt] -> Le.Type -> TI [Pred]
tiAlts ce as alts t = do psts <- mapM (tiAlt ce as) alts
                         mapM (unify t) (map snd psts)
                         return (concat (map fst psts))

-----------------------------------------------------------------------------

split :: Monad m => ClassEnv -> [Tyvar] -> [Tyvar] -> [Pred]
                      -> m ([Pred], [Pred])
split ce fs gs ps = do ps' <- reduce ce ps
                       let (ds, rs) = partition (all (`elem` fs) . tv) ps'
                       rs' <- defaultedPreds ce (fs++gs) rs
                       return (ds, rs \\ rs')

type Ambiguity       = (Tyvar, [Pred])

ambiguities         :: ClassEnv -> [Tyvar] -> [Pred] -> [Ambiguity]
ambiguities _ vs ps = [ (v, filter (elem v . tv) ps) | v <- tv ps \\ vs ]

numClasses :: [Id]
numClasses  = []

stdClasses :: [Id]
stdClasses  = []

candidates           :: ClassEnv -> Ambiguity -> [Le.Type]
candidates _ _ = []

withDefaults :: Monad m => ([Ambiguity] -> [Le.Type] -> a)
                  -> ClassEnv -> [Tyvar] -> [Pred] -> m a
withDefaults f ce vs ps
    | any null tss  = fail "cannot resolve ambiguity"
    | otherwise     = return (f vps (map head tss))
      where vps = ambiguities ce vs ps
            tss = map (candidates ce) vps

defaultedPreds :: Monad m => ClassEnv -> [Tyvar] -> [Pred] -> m [Pred]
defaultedPreds  = withDefaults (\vps _ -> concat (map snd vps))

-----------------------------------------------------------------------------

type Expl = (Id, Scheme, [Alt])

tiExpl :: ClassEnv -> [Assump] -> Expl -> TI [Pred]
tiExpl ce as (_, sc, alts)
        = do (qs :=> t) <- freshInst sc
             ps         <- tiAlts ce as alts t
             s          <- getSubst
             let qs'     = apply s qs
                 t'      = apply s t
                 fs      = tv (apply s as)
                 gs      = tv t' \\ fs
                 sc'     = quantify gs (qs':=>t')
                 ps'     = filter (not . entail ce qs') (apply s ps)
             (ds,rs)    <- split ce fs gs ps'
             if sc /= sc' then
                 fail "signature too general"
               else if not (null rs) then
                 fail "context too weak"
               else
                 return ds

-----------------------------------------------------------------------------

type Impl   = (Id, [Alt])

restricted   :: [Impl] -> Bool
restricted bs = any simple bs
 where simple (_, alts) = any (null . fst) alts

tiImpls         :: Infer [Impl] [Assump]
tiImpls ce as bs = do ts <- mapM (\_ -> newTVar star) bs
                      let is    = map fst bs
                          scs   = map toScheme ts
                          as'   = zipWith (:>:) is scs ++ as
                          altss = map snd bs
                      pss <- sequence (zipWith (tiAlts ce as') altss ts)
                      s   <- getSubst
                      let ps'     = apply s (concat pss)
                          ts'     = apply s ts
                          fs      = tv (apply s as)
                          vss     = map tv ts'
                          gs      = foldr1 union vss \\ fs
                      (ds,rs) <- split ce fs (foldr1 intersect vss) ps'
                      if restricted bs then
                          let gs'  = gs \\ tv rs
                              scs' = map (quantify gs' . ([]:=>)) ts'
                          in return (ds++rs, zipWith (:>:) is scs')
                        else
                          let scs' = map (quantify gs . (rs:=>)) ts'
                          in return (ds, zipWith (:>:) is scs')

-----------------------------------------------------------------------------

type BindGroup  = ([Expl], [[Impl]])

tiBindGroup :: Infer BindGroup [Assump]
tiBindGroup ce as (es,iss) =
  do let as' = [ v:>:sc | (v,sc,alts) <- es ]
     (ps, as'') <- tiSeq tiImpls ce (as'++as) iss
     qss        <- mapM (tiExpl ce (as''++as'++as)) es
     return (ps++concat qss, as''++as')

tiSeq                  :: Infer bg [Assump] -> Infer [bg] [Assump]
tiSeq _ _ _ []          = return ([],[])
tiSeq ti ce as (bs:bss) = do (ps,as')  <- ti ce as bs
                             (qs,as'') <- tiSeq ti ce (as'++as) bss
                             return (ps++qs, as''++as')

-----------------------------------------------------------------------------
-- TIProg:	Type Inference for Whole Programs
-----------------------------------------------------------------------------

type Program = [BindGroup]

tiProgram :: ClassEnv -> [Assump] -> Program -> [Assump]
tiProgram ce as bgs = runTI $
                      do (ps, as') <- tiSeq tiBindGroup ce as bgs
                         s         <- getSubst
                         rs        <- reduce ce (apply s ps)
                         return (apply s as')

-----------------------------------------------------------------------------

-}