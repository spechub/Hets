{- Fast, Error Correcting Parser Combinators;See version history in same directory.
 - Copyright:  S. Doaitse Swierstra
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT
               the Netherlands
               swierstra@cs.uu.nl -}
module UU_Parsing_Core
where
import UU_BinaryTrees

systemerror :: [Char] -> [Char] -> a
usererror :: [Char] -> a
libCorrect :: Eq (Exp a) => ((b,Reports a),Steps a) -> ((b,Reports a),Steps a) -> c -> ((b,Reports a),Steps a)
libGreedy :: (Symbol a, OutputState b) => RealParser c b a d -> RealParser c b a d -> RealParser c b a d
libDollar :: OutputState a => (b -> c) -> RealParser d a e b -> RealParser d a e c
libSeq :: OutputState a => RealParser b a c (d -> e) -> RealParser b a c d -> RealParser b a c e
libSucceed :: OutputState a => b -> RealParser c a d b
libAccept :: (OutputState a, InputState b) => RealParser b a c c
libOr :: (Symbol a, OutputState b) => RealParser c b a d -> RealParser c b a d -> RealParser c b a d

except :: Symbol a => SymbolR a -> [a] -> [SymbolR a]
symRS :: Ord a => SymbolR a -> a -> Ordering
symInRange :: Ord a => SymbolR a -> a -> Bool
mk_range :: Ord a => a -> a -> SymbolR a

handleEof :: (InputState a, Symbol b, OutputState c) => a b -> ((c (a b),Reports b),Steps d)
libDelete :: (Symbol a, InputState b) => Exp a -> RealParser b c a d -> RealParser b c a d
libInsert :: InputState a => Int -> b -> Exp b -> RealParser a c b d -> RealParser a c b d

to_list :: Exp a -> [Exp a]
unionExp :: Eq (Exp a) => Exp a -> Exp a -> Exp a
addexpecting :: Eq (Exp a) => Exp a -> Reports a -> Reports a
unP :: RealParser a b c d -> (a c -> Result (b e) c) -> a c -> Result (b (d,e)) c

-- =======================================================================================
-- ===== BASIC PARSER TYPE AND PARSERS ===================================================
-- =======================================================================================
type Result val s = ((val, Reports s), Steps s)

newtype RealParser state result s a =  P (forall r. (state s -> Result (result r) s) ->  state s -> Result (result (a,r)) s)

class InputState state where
 splitStateE :: state s            -> Either (s, state s) (state s)
 splitState  :: state s            -> (s, state s)
 insertState :: s       -> state s -> state s
 firstState  :: state s            -> (Maybe s)

class OutputState r  where
  acceptR      ::  v -> r rest              -> r (v, rest)
  applyR       ::  r (b -> a, (b, rest))    -> r (a, rest)
  dollarR      :: (b -> a) ->  r (b, rest)  -> r (a, rest)
  finalstate   ::  a                        -> r a

instance Show (RealParser state result s a) where
 show (P p) = "Function"

unP (P p) = p
-- =======================================================================================
-- ===== ERROR REPORTING =================================================================
-- =======================================================================================
data Reports s   = Insert    (Maybe s) s (Exp s)  (Reports s)
                 | Delete    (Maybe s) s (Exp s)  (Reports s)
                 | NoMoreReports
                 deriving Eq

instance Symbol s => Show (Reports s) where
 show msgs = case msgs of
             (Insert    s a exp rest) ->  "\nSymbol " ++ show a ++ " was inserted " ++ atsymbol s ++ expecting exp ++ show rest
             (Delete    s a exp rest) ->  "\nSymbol " ++ show a ++ atsymbol s ++ " was deleted"   ++ expecting exp ++ show rest
             (NoMoreReports         ) -> ""
             where atsymbol Nothing  = " at end of file"
                   atsymbol (Just s) = " before " ++ show s
                   expecting ss    = ", because " ++ show ss ++ " was expected."

addexpecting more  (Insert s a exp msgs) = Insert s a (more `unionExp` exp) msgs
addexpecting more  (Delete s a exp msgs) = Delete s a (more `unionExp` exp) msgs
addexpecting _     NoMoreReports         = systemerror "UU_Parsing_Library" "addexpecting"

data Exp s = ESym (SymbolR s)
           | EStr String
           | EOr  [Exp s]
           | ESeq [Exp s]
           deriving (Eq)


instance (Eq s,Show s) => Show (Exp s) where
 show (ESym  s)     = show s
 show (EStr  str)   = str
 show (EOr   ors)   = concat (intersperse " or " (map show ors))
                      where intersperse sep (x:xs)   = x : (if null xs then [] else sep : intersperse sep xs)
                            intersperse sep []       = []

 show (ESeq  seq)   = concat (map show seq)

unionExp l          r          = let rl = to_list r
                                     result = foldr (\e rr -> if e `elem` rl then rr else e:rr) rl (to_list l)
                                 in if null (tail result) then head result else ( EOr result)
to_list (EOr l)                 = l
to_list e                      = [e]

libInsert      c sym firsts cont = P (\k inp -> let (~(result, msgs), steps) = unP cont k (insertState sym inp)
                                                in  ( (result, Insert (firstState inp)  sym firsts msgs)
                                                    , Cost c firsts steps
                                                    ))

libDelete firsts cont = P(\ k inp ->let (s, ss)                  = splitState inp
                                        (~(result, msgs), steps) = unP cont k ss
                                    in  ( (result, Delete (firstState ss) s firsts msgs)
                                          , Cost (deleteCost s)  firsts steps
                                        ))

handleEof input = case splitStateE input
                  of Left (s, ss) -> let (~(result, msgs), steps) = handleEof ss
                                     in  ( (result, Delete Nothing s  (EStr "eof") msgs)
                                         , Cost (deleteCost s)  (EStr "eof") steps)
                     Right final  -> ((finalstate final, NoMoreReports), NoMoreSteps)

-- =======================================================================================
-- ===== SYMBOLS and RANGES ==============================================================
-- =======================================================================================
class (Ord s, Show s) => Symbol s where
 deleteCost :: s -> Int
 symBefore  :: s -> s
 symAfter   :: s -> s
 deleteCost b = 5
 symBefore  = error "You should have made your token type an instance of the Class Symbol. eg by defining symBefore = succ"
 symAfter   = error "You should have made your token type an instance of the Class Symbol. eg by defining symBefore = pred"

data  SymbolR s  =  Range s s | EmptyR deriving (Eq,Ord)

instance (Show s,Eq s) => Show (SymbolR s) where
 show EmptyR      = "the empty range"
 show (Range a b) = if a == b then show a else show a ++ ".." ++ show b

mk_range             l    r =  if l > r then EmptyR else Range l r

symInRange (Range l r) = if l == r then (l==)
                                   else (\ s -> not (s < l || r < s ))

symRS (Range l r)
  = if l == r then (compare l)
    else (\ s -> if      s < l then GT
                 else if s > r then LT
                 else               EQ)

range `except` elems
 = foldr removeelem [range] elems
   where removeelem elem ranges = [r | ran <- ranges, r <- ran `minus` elem]
         EmptyR          `minus` _    = []
         ran@(Range l r) `minus` elem = if symInRange ran elem
                                        then [mk_range l (symBefore elem), mk_range (symAfter elem) r]
                                        else [ran]
-- =======================================================================================
-- ===== STEPS ===========================================================================
-- =======================================================================================
data Steps s = Ok                     (Steps s)
             | Cost {costing::Int, starting::(Exp s), rest::(Steps s)}
             | Best {starting::(Exp s), left::(Steps s), right::(Steps s)}
             | NoMoreSteps

-- =======================================================================================
-- ===== CORE PARSERS ====================================================================
-- =======================================================================================
libOr  (P p) (P q)
 = P (\ k state   -> let pr@(pv, ps) = p k state
                         qr@(qv, qs) = q k state
                         select left@(Ok l)   right@( Ok r)  = let (v,    ss) = select l r
                                                               in  (v, Ok ss)
                         select  ls@(Ok   _)   _             = (pv, ls)
                         select  _             rs@(Ok _)     = (qv, rs)
                         select  NoMoreSteps   _             = (pv, NoMoreSteps)
                         select  _             NoMoreSteps   = (qv, NoMoreSteps)
                         select  pl            ql            = libCorrect (pv,pl) (qv,ql) "libOr"
                     in select ps qs
     )

libAccept           = P (\ k state  -> let (s, ss)                  = splitState state
                                           ( ~(result, msgs), st)   = k ss
                                       in  ((acceptR s result , msgs), Ok st))

libSucceed v = P(\ k state  -> let (~(result, msgs), st) = k       state in ((acceptR v result, msgs), st))
libSeq (P p) (P q)   =  P (\ k state  -> let (~(result, msgs), st) = p (q k) state in ((applyR result, msgs), st))
-- libDot (P p) (P q)   =    (\ k state  ->                             p (q k) state)
-- libApply             =    (\ k state  -> let (~(result, msgs), st) =      k  state in ((applyR    result, msgs), st))

libDollar f (P p)  = P(\ k state  -> let (~(result, msgs), st) = p k     state in ((dollarR f result, msgs), st))

libGreedy (P pp) (P pq)
 =  let succeeds  (Ok _)      = True
        succeeds  NoMoreSteps = True
        succeeds  _           = False
    in  P (\k state     -> let pres@(pv, pl) = pp k state
                               qres@(qv, ql) = pq k state
                           in if      succeeds pl then  pres
                              else if succeeds ql then  qres
                              else                      libCorrect  qres pres "libGreedy")
-- =======================================================================================
-- ===== SELECTING THE BEST RESULT  ======================================================
-- =======================================================================================
libCorrect (~lv@(lr,lm), ls) (~rv@(rr, rm), rs) _
 = let  cost _               0 = 0
        cost (Ok l)          n =     cost l (n-1)
        cost (Cost i _ l)    n = i + cost l (n-1)
        cost (Best _ l r)    n = cost l n `min` cost r n
        cost (NoMoreSteps) n = 0
   in (if cost ls 4 <= cost rs 4 then (lr, addexpecting (starting rs) lm)
                                 else (rr, addexpecting (starting ls) rm)
      , Best (starting ls `unionExp` starting rs) ls rs
      )
-- =======================================================================================
-- ===== TRACING  and ERRORS  and MISC ===================================================
-- =======================================================================================
usererror   m = error ("Your grammar contains a problem:\n" ++ m)
systemerror modname m
  = error ("I apologise: I made a mistake in my design. This should not have happened.\n"
                       ++
           " Please report: " ++ modname ++": " ++ m ++ " to doaitse@cs.uu.nl\n")