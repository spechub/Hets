{- Fast, Error Correcting Parser Combinators; See version history in same directory.
 - Copyright:  S. Doaitse Swierstra
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT
               the Netherlands
               swierstra@cs.uu.nl
SDS: April 23, removed Code dta type, added states
-}

module UU_Parsing         ( module UU_Parsing
                          , module UU_Parsing_Core
                          , module UU_Parsing_Analysing
                          )
where
import UU_Parsing_Core
import UU_Parsing_Analysing
-- import IOExts
import List
import Maybe
{-
pLocate :: (Alternative a, SymParser a b, Sequence a) => [[b]] -> a [b]
pToks :: (Sequence a, SymParser a b) => [b] -> a [b]
list_of :: Sequence a => a b -> ([c],a ([b] -> [b]),d -> d)
usealg :: Sequence a => (b -> c,d) -> a b -> (d,a c,e -> e)
pMerged :: (Sequence a, SplitParser a, SymParser a b, Show (Exp b), Alternative a) => c -> (d,a (d -> d),c -> d -> e) -> a e
(<||>) :: (Sequence a, Alternative a) => (b,a (c -> c),d -> e -> f) -> (g,a (h -> h),f -> i -> j) -> ((b,g),a ((c,h) -> (c,h)),d -> (e,i) -> j)
pAnySym :: (Alternative a, SymParser a b) => [b] -> a b
pAny :: Alternative a => (b -> a c) -> [b] -> a c

pChainl :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a (c -> c -> c) -> a c -> a c
pChainl_ng :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a (c -> c -> c) -> a c -> a c
pChainl_gr :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a (c -> c -> c) -> a c -> a c
pChainr :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a (c -> c -> c) -> a c -> a c
pChainr_ng :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a (c -> c -> c) -> a c -> a c
pChainr_gr :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a (c -> c -> c) -> a c -> a c
pList1Sep :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a c -> a d -> a [d]
pList1Sep_ng :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a c -> a d -> a [d]
pList1Sep_gr :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a c -> a d -> a [d]
pListSep :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a c -> a d -> a [d]
pListSep_ng :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a c -> a d -> a [d]
pListSep_gr :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a c -> a d -> a [d]
pList1 :: (Sequence a, Alternative a, SplitParser a, SymParser a b, Show (Exp b)) => a c -> a [c]
pList1_ng :: (Sequence a, Alternative a, SplitParser a, Show (Exp b), SymParser a b) => a c -> a [c]
pList1_gr :: (Sequence a, Alternative a, SplitParser a, SymParser a b, Show (Exp b)) => a c -> a [c]
pList :: (Show (Exp a), SymParser b a, SplitParser b, Sequence b, Alternative b) => b c -> b [c]
pList_ng :: (SymParser a b, Show (Exp b), SplitParser a, Alternative a, Sequence a) => a c -> a [c]
pList_gr :: (Show (Exp a), SymParser b a, SplitParser b, Sequence b, Alternative b) => b c -> b [c]
list_alg :: (a -> [a] -> [a],[b])
pFoldr1Sep :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => (c -> d -> d,d) -> a e -> a c -> a d
pFoldr1Sep_ng :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => (c -> d -> d,d) -> a e -> a c -> a d
pFoldr1Sep_gr :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => (c -> d -> d,d) -> a e -> a c -> a d
pFoldrSep :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => (c -> d -> d,d) -> a e -> a c -> a d
pFoldrSep_ng :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => (c -> d -> d,d) -> a e -> a c -> a d
pFoldrSep_gr :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => (c -> d -> d,d) -> a e -> a c -> a d
pFoldr1 :: (Sequence a, Alternative a, SplitParser a, SymParser a b, Show (Exp b)) => (c -> d -> d,d) -> a c -> a d
pFoldr1_ng :: (Sequence a, Alternative a, SplitParser a, Show (Exp b), SymParser a b) => (c -> d -> d,d) -> a c -> a d
pFoldr1_gr :: (Sequence a, Alternative a, SplitParser a, SymParser a b, Show (Exp b)) => (c -> d -> d,d) -> a c -> a d
pFoldr :: (Show (Exp a), SymParser b a, SplitParser b, Sequence b, Alternative b) => (c -> d -> d,d) -> b c -> b d
pFoldr_gr :: (Show (Exp a), SymParser b a, SplitParser b, Sequence b, Alternative b) => (c -> d -> d,d) -> b c -> b d
pFoldr_ng :: (SymParser a b, Show (Exp b), SplitParser a, Alternative a, Sequence a) => (c -> d -> d,d) -> a c -> a d
pPacked :: Sequence a => a b -> a c -> a d -> a d

(<?>) :: SymParser a b => a c -> [Char] -> a c
(<??>) :: (Sequence a, Alternative a, Show (Exp b), SymParser a b, SplitParser a) => a c -> a (c -> c) -> a c
(<$$>) :: Sequence a => (b -> c -> d) -> a c -> a (b -> d)
(<**>) :: Sequence a => a b -> a (b -> c) -> a c
(*>) :: Sequence a => a b -> a c -> a c
(<*) :: Sequence a => a b -> a c -> a b
(<$) :: Sequence a => b -> a c -> a b
(<+>) :: Sequence a => a b -> a c -> a (b,c)
asOpt :: SymParser a b => Exp b -> a c -> a c
asList :: SymParser a b => Exp b -> a c -> a c
opt :: (SplitParser a, SymParser a b, Show (Exp b), Sequence a, Alternative a) => a c -> c -> a c
pExcept :: (Alternative a, SymParser a b, Symbol b, Eq (SymbolR b)) => (b,b,b) -> [b] -> a b
(<..>) :: SymParser a b => b -> b -> a b
mnz :: (SplitParser a, SymParser a b, Show (Exp b)) => a c -> d -> d
acceptsepsilon :: SplitParser a => a b -> Bool
parse :: (Symbol a, InputState b) => AnaParser b Id a c -> b a -> (c,Reports a)
parsebasic :: RealParser a Id b c -> (a b -> Result (Id d) b) -> a b -> (c,Reports b)
-}
-- =======================================================================================
-- ===== Derived Combinators =============================================================
-- =======================================================================================
infixl 2 <?>
infixl 3 <|>
infixl 4 <*>, <~*~>, <$> , <~$~>, <+>

infixl 4 <$, <*, *>, <**>, <??>
infixl 2 `opt`
infixl 5 <..>

parsebasic (P rp) handleEof inp
 = let (( Id (res, a),msgs), _) = rp handleEof inp
   in (res, msgs)

parse (pp) inp
 =  parsebasic (pars pp) handleEof inp

-- =======================================================================================
-- ===== PARSER CLASSES ==================================================================
-- =======================================================================================
class (Sequence p, Alternative p, SymParser p s, SplitParser p, Show s) => IsParser p s | p -> s

instance (Sequence p, Alternative p, SymParser p s, SplitParser p, Show s)
        => IsParser p s


class Sequence p where
  (<*>) :: p (a->b) -> p a -> p b
  pSucceed :: a -> p a
  pLow     :: a -> p a
  (<$>) :: (a->b) -> p a -> p b
  f <$> p = pSucceed f <*> p

class Alternative p where
  (<|>) :: p a -> p a -> p a
  pFail :: p a

class SymParser p s | p -> s where
 pCostRange   :: Int -> s -> SymbolR s -> p s
 pCostSym     :: Int -> s -> s         -> p s
 pSym         ::             s         -> p s
 pRange       ::        s -> SymbolR s -> p s
 pSym a       =  pCostSym   5 a a
 pRange       =  pCostRange 5
 getfirsts    ::  p v -> Exp s
 setfirsts    ::  Exp s -> p v ->  p v

class SplitParser p where
 getzerop     ::  p v -> Maybe (p v)
 getonep      ::  p v -> Maybe (p v)
-- =======================================================================================
-- ===== DEFAULT IMPLEMENTATION  =========================================================
-- =======================================================================================
instance InputState [] where
 splitStateE []     = Right []
 splitStateE (s:ss) = Left  (s, ss)
 splitState  (s:ss) = (s, ss)
 insertState s ss   = s:ss
 firstState  []     = Nothing
 firstState  (s:ss) = Just s




newtype Id a = Id a

instance OutputState Id  where
  acceptR  v (Id          r  ) = Id (v  , r)
  applyR     (Id (f, ~(a, r))) = Id (f a, r)
  dollarR f  (Id     ~(a, r) ) = Id (f a, r)
  finalstate      v            = Id v
-- =======================================================================================
-- ===== ANAPARSER INSTANCES =============================================================
-- =======================================================================================
type Parser = AnaParser  []  Id



instance (Symbol s, InputState state, OutputState result)
        => Sequence (AnaParser state result s)    where
  (<*>) = anaSeq
  pSucceed = anaSucceed
  pLow     = anaLow

instance (Symbol s, InputState state, OutputState result)
        => Alternative (AnaParser state result s) where
  (<|>) = anaOr
  pFail = anaFail

instance (Symbol s, InputState state, OutputState result)
        => SymParser (AnaParser state result s) s where
  pCostRange   = anaCostRange
  pCostSym     = anaCostSym
  getfirsts    = anaGetFirsts
  setfirsts    = anaSetFirsts

instance OutputState result => SplitParser (AnaParser state result s) where
 getzerop  p = case zerop p of
                 Nothing     -> Nothing
                 Just (b,e)  -> Just p {pars=libSucceed `either` id $ e
                                       ,onep=Nothing
                                       }
 getonep   p = case onep p of
                Nothing    -> Nothing
                Just (r,d) -> Just p{pars=r
                                    ,zerop=Nothing
                                    }

-- =======================================================================================
-- ===== PERMUTATIONS ================================================================
-- =======================================================================================
permute :: (Alternative a, Sequence a) => Perms a b -> a b
(<~$~>) :: (Sequence a, SplitParser a) => (b -> c) -> a b -> Perms a c
add :: Sequence a => Perms a (b -> c) -> (Maybe (a b),Maybe (a b)) -> Perms a c
(<~*~>) :: (Sequence a, SplitParser a) => Perms a (b -> c) -> a b -> Perms a c

newtype Perms p a = Perms (Maybe (p a), [Br p a])
data Br p a = forall b. Br (Perms p (b -> a)) (p b)

perms <~*~> p = perms `add` (getzerop p, getonep p)
f     <~$~> p = Perms (Just (pLow f), []) <~*~> p

add b2a@(Perms (eb2a, nb2a)) bp@(eb, nb)
 =  let changing :: Sequence a => (b -> c) -> Perms a b -> Perms a c
        f `changing` Perms (ep, np) = Perms (fmap (f <$>) ep, [Br ((f.) `changing` pp) p | Br pp p <- np])
    in Perms
      ( do { f <- eb2a
           ; x <- eb
           ; return (f <*>  x)
           }
      ,  (case nb of
          Nothing     -> id
          Just pb     -> (Br b2a  pb:)
        )[ Br ((flip `changing` c) `add`  bp) d |  Br c d <- nb2a]
      )

permute (Perms (empty,nonempty))
 = foldl (<|>) (fromMaybe pFail empty) [ (flip ($)) <$> p <*> permute pp
                                       | Br pp  p <- nonempty
                                       ]
-- =======================================================================================
-- ===== CHECKING ========================================================================
-- =======================================================================================
acceptsepsilon p       = case getzerop p of {Nothing -> False; _ -> True}

mnz p v
   = if( acceptsepsilon p)
     then   usererror ("You are calling a list based derived combinator with a parser that accepts the empty string.\n"
                    ++
                   "We cannot handle the resulting left recursive formulation (and it is ambiguous too).\n"++
                   (case getfirsts p of
                    ESeq []  ->  "There are no other alternatives for this parser"
                    d        ->  "The other alternatives of this parser may start with:\n"++ show d
                  ))
     else v
-- =======================================================================================
-- ===== START OF PRELUDE DEFINITIONS ========== =========================================
-- =======================================================================================
a <..> b   = pRange a (Range a b)
(l,r,err) `pExcept` elems = let ranges = filter (/= EmptyR) (Range l r `except` elems)
                            in if null ranges then pFail
                               else foldr (<|>) pFail (map (pRange err) ranges)

p `opt` v       = mnz p (p  <|> pLow v)   -- note that opt is greedy, if you do not want this
                                              -- use "... <|> pSucceed v"" instead
                                              -- p should not recognise the empty string
-- =======================================================================================
-- ===== Special sequential compositions =========================================
-- =======================================================================================
asList  exp = setfirsts (ESeq [EStr "(",  exp, EStr  ")*"])
asList1 exp = setfirsts (ESeq [EStr "(",  exp, EStr  ")+"])
asOpt   exp = setfirsts (ESeq [EStr "( ", exp, EStr  ")?"])


pa <+> pb       = (,) <$> pa <*> pb
f <$  p         = const f        <$> p
p <*  q         = (\ x _ -> x)   <$> p <*> q
p *>  q         = (\ _ x -> x)   <$> p <*> q
p <**> q        = (\ x f -> f x) <$> p <*> q
f <$$> p        = pSucceed (flip f) <*> p
p <??> q        = p <**> (q `opt` id)
p <?>  str      = setfirsts  (EStr str) p
pPacked l r x   =   l *>  x <*   r

-- =======================================================================================
-- ===== Iterating ps ===============================================================
-- =======================================================================================
pFoldr_ng      alg@(op,e)     p = mnz p (asList (getfirsts p) pfm)
                                  where pfm = (op <$> p <*> pfm)  <|> pSucceed e
pFoldr_gr      alg@(op,e)     p = mnz p (asList (getfirsts p) pfm)
                                  where pfm = (op <$> p <*> pfm) `opt` e
pFoldr         alg            p = pFoldr_gr alg p

pFoldr1_gr     alg@(op,e)     p = asList1 (getfirsts p) (op <$> p <*> pFoldr_gr  alg p)
pFoldr1_ng     alg@(op,e)     p = asList1 (getfirsts p) (op <$> p <*> pFoldr_ng  alg p)
pFoldr1        alg            p = pFoldr1_gr alg  p

pFoldrSep_gr   alg@(op,e) sep p = mnz p (asList (getfirsts p)((op <$> p <*> pFoldr_gr alg (sep *> p)) `opt` e ))
pFoldrSep_ng   alg@(op,e) sep p = mnz p (asList (getfirsts p)((op <$> p <*> pFoldr_ng alg (sep *> p))  <|>  pSucceed e))
pFoldrSep      alg        sep p = pFoldrSep_gr alg sep p

pFoldr1Sep_gr  alg@(op,e) sep p = if acceptsepsilon sep then mnz p pfm else pfm
                                  where pfm = op <$> p <*> pFoldr_gr alg (sep *> p)
pFoldr1Sep_ng  alg@(op,e) sep p = if acceptsepsilon sep then mnz p pfm else pfm
                                  where pfm = op <$> p <*> pFoldr_ng alg (sep *> p)
pFoldr1Sep     alg        sep p = pFoldr1Sep_gr alg sep p

list_alg = ((:), [])

pList_gr        p = pFoldr_gr     list_alg   p
pList_ng        p = pFoldr_ng     list_alg   p
pList           p = pList_gr p

pList1_gr       p = pFoldr1_gr    list_alg   p
pList1_ng       p = pFoldr1_ng    list_alg   p
pList1          p = pList1_gr                p

pListSep_gr   s p = pFoldrSep_gr  list_alg s p
pListSep_ng   s p = pFoldrSep_ng  list_alg s p
pListSep      s p = pListSep_gr            s p

pList1Sep_gr  s p = pFoldr1Sep_gr list_alg s p
pList1Sep_ng  s p = pFoldr1Sep_ng list_alg s p
pList1Sep     s p = pList1Sep_gr          s p

pChainr_gr op x    =  if acceptsepsilon op then mnz x r else r
                   where r = x <??> (flip <$> op <*> r)
pChainr_ng op x    =  if acceptsepsilon op then mnz x r else r
                   where r = x <**> ((flip <$> op <*> r)  <|> pSucceed id)
pChainr    op x    = pChainr_gr op x

pChainl_gr op x    =  if acceptsepsilon op then mnz x r else r
                      where
                       r      = (f <$> x <*> pList_gr (flip <$> op <*> x) )
                       f x [] = x
                       f x (func:rest) = f (func x) rest

pChainl_ng op x    =  if acceptsepsilon op then mnz x r else r
                   where
                    r      = (f <$> x <*> pList_ng (flip <$> op <*> x) )
                    f x [] = x
                    f x (func:rest) = f (func x) rest
pChainl    op x    = pChainl_gr op x

pAny  f l = if null l then usererror "pAny: argument may not be empty list" else foldr1 (<|>) (map f l)
pAnySym l = pAny pSym l -- used to be called pAnySym

-- ==== merging
-- e.g. chars_digs = cat3 `pMerged` (list_of pDig <||> list_of pL <||> list_of pU)
--      parsing "12abCD1aV" now returns "121abaCDV", so the sequence of
-- recognised elements is stored in three lists, which are then passed to cat3

(pe, pp, punp) <||> (qe, qp, qunp)
 =( (pe, qe)
  , (\f (pv, qv) -> (f pv, qv)) <$> pp
              <|>
    (\f (pv, qv) -> (pv, f qv)) <$> qp
  , \f (x, y) -> qunp (punp f x) y
  )

sem `pMerged` (units, alts, unp)
 = let pres = alts <*> pres `opt` units
   in unp sem <$> pres

usealg (op, e) p = (e, op <$> p, id)
list_of p = usealg list_alg p

pToks []     = pSucceed []
pToks (a:as) = (:) <$> pSym a <*> pToks as

pLocate list = pAny pToks list

-- =======================================================================================
-- ===== RANGE ASSISTANTS === ============================================================
-- =======================================================================================
{-
data OC = RO | CL | LO
        deriving (Eq,Ord, Show)

type Point s = (s,OC)

instance (Ord s, Show s) => Symbol (Point s) where
 symBefore (v,CL) = (v,RO)
 symBefore (v,LO) = (v,CL)
 symBefore (v,RO) = systemerror "UU_Parsing_Library" ("before RO")
 symAfter  (v,CL) = (v,LO)
 symAfter  (v,RO) = (v,CL)
 symAfter  (v,LO) = systemerror "UU_Parsing_Library" ("after LO")
 symInRange ran = (EQ==).symRS ran
 symRS (Range (l,lb) (r,rb))
  = if l == r && lb == CL && rb == CL then compare l
    else \s -> case compare l s of
               LT -> case compare r s of
                     EQ -> compare rb CL
                     LT -> LT
                     GT -> EQ
               EQ -> compare lb CL
               GT -> GT



instance (Symbol s) => Show (SymbolR (Point s)) where
  show (Range (a, CL) (b,CL)) = if a==b then "["++show a++"]"
                        else "["++show a++ ".." ++ show b ++ "]"
  show (Range (a, ab) (b, bb)) = (if ab == LO then "(" else "[")
                                 ++ show a ++ ".." ++ show b ++
                                 (if ab == RO then ")" else "]")
  show EmptyR       = " [] "
-}