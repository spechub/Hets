{-------------------------------------------------------------------------------

        Copyright:              Mark Jones and The Hatchet Team 
                                (see file Contributors)

        Module:                 Type

        Description:            Manipulation of types

                                The main tasks implemented by this module are:
                                        - type substitution
                                        - type unification
                                        - type matching
                                        - type quantification

        Primary Authors:        Mark Jones and Bernie Pope

        Notes:                  See the file License for license information

                                Large parts of this module were derived from
                                the work of Mark Jones' "Typing Haskell in
                                Haskell", (http://www.cse.ogi.edu/~mpj/thih/)

-------------------------------------------------------------------------------}

module Type (kind,
             apply,
             nullSubst,
             (@@),
             Types (..),
             (+->),
             merge,
             mgu,
             match,
             quantify,
             toScheme,
             find,    -- XXX this is an awful name, should be replaced
             makeAssump,
             assumpScheme,
             assumpToPair,
             pairToAssump,
             assumpId,
             Instantiate (..)
             ) where 

import AnnotatedHsSyn           (AHsName (..))

import List                     (union, 
                                 nub)

import FiniteMaps               (toListFM,
                                 listToFM,
                                 zeroFM,
                                 unitFM,
                                 joinFM,
                                 intersectFM,
                                 FiniteMap (..))

import Representation           (Type (..),
                                 Tyvar (..),
                                 Tycon (..),
                                 Kind (..),
                                 Qual (..),
                                 Pred (..),
                                 Class,
                                 Inst,
                                 Subst,
                                 Scheme (..),
                                 Assump (..))

import Monad                    (foldM)

--------------------------------------------------------------------------------

class Types t where
  apply :: Subst -> t -> t
  tv    :: t -> [Tyvar]

class Instantiate t where
  inst  :: [Type] -> t -> t

instance Instantiate Type where
  inst ts (TAp l r)     = TAp (inst ts l) (inst ts r)
  inst ts (TArrow l r)  = TArrow (inst ts l) (inst ts r)
  inst ts (TTuple args) = TTuple $ map (inst ts) args
  inst ts (TGen n)      = ts !! n
  inst ts t             = t

instance Instantiate a => Instantiate [a] where
  inst ts = map (inst ts)

instance Instantiate t => Instantiate (Qual t) where
  inst ts (ps :=> t) = inst ts ps :=> inst ts t

instance Instantiate Pred where
  inst ts (IsIn c t) = IsIn c (inst ts t)

class HasKind t where
  kind :: t -> Kind
instance HasKind Tyvar where
  kind (Tyvar v k) = k
instance HasKind Tycon where
  kind (Tycon v k) = k
instance HasKind Type where
  kind (TCon tc) = kind tc
  kind (TVar u)  = kind u
  kind (TAp t _) = case (kind t) of
                     (Kfun _ k) -> k
  kind (TArrow _l _r) = Star
  kind (TTuple _args) = Star

-----------------------------------------------------------------------------

instance Types t => Types (Qual t) where
  apply s (ps :=> t) = apply s ps :=> apply s t
  tv (ps :=> t)      = tv ps `union` tv t

instance Types Pred where
  apply s (IsIn c t) = IsIn c (apply s t)
  tv (IsIn c t)      = tv t

--------------------------------------------------------------------------------

-- substitutions

nullSubst  :: Subst
nullSubst   = zeroFM 

(+->)      :: Tyvar -> Type -> Subst
u +-> t     = unitFM u t

instance Types Type where
  
  -- attempting to cache successful substitutions doesn't
  -- seem to make much difference, as the variables are 
  -- mostly independent

  apply s (TVar var@(Tyvar name _kind)) 
     = case lookupSubstitutionMap s name of
          Just t  -> t
          Nothing -> TVar var 
  apply s (TAp l r)     = TAp (apply s l) (apply s r)
  apply s (TArrow l r)  = TArrow (apply s l) (apply s r)
  apply s (TTuple args) = TTuple $ map (apply s) args 
  apply _ t         = t

  tv (TVar u)      = [u]
  tv (TAp l r)     = tv l `union` tv r
  tv (TArrow l r)  = tv l `union` tv r 
  -- tv (TTuple args) = concatMap tv args 
  tv (TTuple args) = foldl union [] $ map tv args 
  tv _             = []

instance Types a => Types [a] where
  apply s = map (apply s)              -- it may be worth using a cached version of apply in this circumstance? 
  tv      = nub . concat . map tv

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2 
   = joinFM s1OverS2 s1
   where
   s1OverS2 = mapSubstitution s1 s2 

merge      :: Subst -> Subst -> Maybe Subst
merge s1 s2 = if agree then Just s else Nothing
 where
 s = joinFM s1 s2
 agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v)) $ map fst $ toListFM $ s1 `intersectFM` s2

-- highly specialised version of lookupFM for
-- a Substitution. It is worth specialising this as it is called
-- frequently during a call to apply
-- according to profiling almost half of the computation time
-- is spent here

lookupSubstitutionMap :: FiniteMap Tyvar Type -> AHsName -> Maybe Type
lookupSubstitutionMap (Node (Tyvar k _kind) e _ sm gr) k'
   | k' <  k    = lookupSubstitutionMap sm k' 
   | k' >  k    = lookupSubstitutionMap gr k' 
   | otherwise  = Just e
lookupSubstitutionMap Leaf _
   = Nothing

-- specialised version of mapFM for substitutions

mapSubstitution :: Subst -> FiniteMap Tyvar Type -> FiniteMap Tyvar Type 
mapSubstitution s (Node k e n sm gr)  = Node k (apply s e) n (mapSubstitution s sm) (mapSubstitution s gr)
mapSubstitution s Leaf                = Leaf

--------------------------------------------------------------------------------

-- unification

mgu     :: Type -> Type -> Maybe Subst
varBind :: Tyvar -> Type -> Maybe Subst

mgu (TAp l r) (TAp l' r') 
   = do s1 <- mgu l l'
        s2 <- mgu (apply s1 r) (apply s1 r')
        Just (s2 @@ s1)

mgu (TArrow l r) (TArrow l' r')
   = do s1 <- mgu l l' 
        s2 <- mgu (apply s1 r) (apply s1 r')
        Just (s2 @@ s1)



mgu (TTuple args1) (TTuple args2)
   = do let lenArgs1 = length args1
        let lenArgs2 = length args2
        -- check the dimensions of the tuples are the same
        case lenArgs1 == lenArgs2 of
           True  -> foldM (\oldSub (t1,t2) -> case mgu (apply oldSub t1) (apply oldSub t2) of
                                                 Nothing      -> Nothing
                                                 Just newSub  -> Just (newSub @@ oldSub)) 
                          nullSubst
                          (zip args1 args2)
           False -> Nothing 

mgu (TVar u) t        = varBind u t
mgu t (TVar u)        = varBind u t
mgu (TCon tc1) (TCon tc2)
           | tc1==tc2 = Just nullSubst
           | otherwise = Nothing
mgu t1 t2  = Nothing

varBind u t | t == TVar u      = Just nullSubst
            | u `elem` tv t    = Nothing
            | kind u == kind t = Just (u +-> t)
            | otherwise        = Nothing

match :: Type -> Type -> Maybe Subst

match (TAp l r) (TAp l' r') 
   = do sl <- match l l'
        sr <- match r r'
        merge sl sr

match (TArrow l r) (TArrow l' r') 
   = do sl <- match l l'
        sr <- match r r'
        merge sl sr


match (TTuple args1) (TTuple args2) 
   = do let lenArgs1 = length args1
        let lenArgs2 = length args2
        -- check the dimensions of the tuples are the same
        case lenArgs1 == lenArgs2 of
           True  -> foldM (\oldSub (t1,t2) -> case match t1 t2 of
                                                 Nothing      -> Nothing
                                                 Just newSub  -> merge oldSub newSub)
                          nullSubst
                          (zip args1 args2)
           False -> Nothing 

match (TVar u) t
   | kind u == kind t = Just (u +-> t)

match (TCon tc1) (TCon tc2)
   | tc1==tc2         = Just nullSubst

match t1 t2           = Nothing

-----------------------------------------------------------------------------

instance Types Scheme where
  apply s (Forall ks qt) = Forall ks (apply s qt)
  tv (Forall ks qt)      = tv qt

quantify      :: [Tyvar] -> Qual Type -> Scheme
quantify vs qt = Forall ks (apply s qt)
 where vs' = [ v | v <- tv qt, v `elem` vs ]
       ks  = map kind vs'
       s   = listToFM $ zip vs' (map TGen [0..])

toScheme      :: Type -> Scheme
toScheme t     = Forall [] ([] :=> t)

-----------------------------------------------------------------------------

assumpToPair :: Assump -> (AHsName, Scheme)
assumpToPair (n :>: s) = (n,s)

pairToAssump :: (AHsName, Scheme) -> Assump
pairToAssump (n,s) = (n :>: s)

instance Types Assump where
  apply s (i :>: sc) = i :>: (apply s sc)
  tv (i :>: sc)      = tv sc

find     :: AHsName -> [Assump] -> Scheme
find i as
   = case schemeList of
        (x:_) -> x
        []    -> error $ "find: could not find the type scheme for identifier: " ++ (show i)
   where
   schemeList = [ sc | (i':>:sc) <- as, i==i' ]

assumpId :: Assump -> AHsName 
assumpId (id :>: _scheme) = id

assumpScheme :: Assump -> Scheme
assumpScheme (_id :>: scheme) = scheme 

makeAssump :: AHsName -> Scheme -> Assump
makeAssump name scheme = name :>: scheme
