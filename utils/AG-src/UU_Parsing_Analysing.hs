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

module UU_Parsing_Analysing
where
--import IOExts
--import List
import UU_BinaryTrees
import UU_Parsing_Core
import Maybe

-- =======================================================================================
-- ===== DESCRIPTORS =====================================================================
-- =======================================================================================
data AnaParser  state result s a
 = AnaParser { pars     :: RealParser state result s a
             , zerop    :: Maybe (Bool, Either a (RealParser state result s a))
             , onep     :: Maybe (      RealParser state result s a
                                 ,      OneDescr   state result s a
                                 )
             } deriving Show
data OneDescr state result s a
 = OneDescr  { leng     :: Nat
             , firsts   :: Exp s
             , table    :: [(SymbolR s, (Int, s, RealParser state result s a))]
             , dynone   :: Maybe                (RealParser state result s a)
             } deriving Show
-- =======================================================================================
-- ===== ANALYSING COMBINATORS ===========================================================
-- =======================================================================================
anaGetFirsts (AnaParser  _ _  Nothing       ) = ESeq []
anaGetFirsts (AnaParser  p z (Just (pp, od))) = firsts od

anaSetFirsts _ (AnaParser  p z Nothing        )  = usererror "Analysing" ("You cannot set the label of an Empty Parser.")
anaSetFirsts newexp (AnaParser  p z (Just (pp, od)))
 = let newod = mkParser (od{firsts = newexp })
   in AnaParser  (combinePars z newod) z newod

anaFail = AnaParser {  pars    = pfail
                    , zerop   = Nothing
                    , onep    = Nothing
                    }
          where pfail = P (\ _  _  -> (usererror  "calling an always failing parser", failalways))
                failalways = Cost 1000 (EStr "Failsalways") failalways
infinite = Succ infinite
anaEmpty p zp = AnaParser { pars    = p
                          , zerop   = Just zp
                          , onep    = Nothing
                          }

anaSucceed  v = anaEmpty (libSucceed v) (False, Left v)
anaLow      v = anaEmpty (libSucceed v) (True,  Left v)
anaDynE     p = anaEmpty p              (False, Right p)
anaDynL     p = anaEmpty p              (True , Right p)
anaDynN  fi len p = AnaParser p  Nothing (Just(p, OneDescr len fi [] (Just p)))

--anaOr  ~ld@(AnaParser pl zl ol)  ~rd@(AnaParser pr zr or)
-- =  let
--    in  (if (anaLength ld) `nat_le`  (anaLength rd) then id else flip) anaOr' ld rd

anaLength (AnaParser _ Nothing  Nothing      ) = infinite
anaLength (AnaParser _ (Just _) _            ) = Zero
anaLength (AnaParser _ Nothing (Just (_, od))) = leng od

anaOr ~ld@(AnaParser pl zl ol)  ~rd@(AnaParser  pr zr or)
 = let newzerop  = maybeComb (moreThanOneEmpty newonep) zl zr
       newonep   = orOneOnePars ol or False
   in AnaParser (combinePars newzerop newonep) newzerop newonep

anaSeq (AnaParser  pl zl ol)  ~rd@(AnaParser pr zr or)
 = case zl of
   Just (b, zp ) -> let newonep = let newoneone  = mapOnePars (   `libSeq` pr) (const infinite) ol
                                      newzeroone = case zp of
                                                   Left  f -> mapOnePars (f `libDollar`   ) id or
                                                   Right p -> mapOnePars (p `libSeq`      ) id or
                                  in orOneOnePars newoneone newzeroone b -- length comes from the right
                        newzerop = seqZeroZeroPars zl zr
                    in AnaParser  (combinePars newzerop newonep) newzerop newonep
   _    ->             AnaParser  (pl `libSeq` pr)               Nothing  (mapOnePars (`libSeq` pr) (`nat_add` anaLength rd) ol)

anaDollar f (AnaParser p z o) = AnaParser (f `libDollar` p)
                                          (case z of
                                           Nothing     -> Nothing
                                           Just (b, v) -> Just (b, case v of
                                                                   Left w   -> Left (f w)
                                                                   Right pp -> Right (f `libDollar` pp))
                                          ) (mapOnePars (f `libDollar`) id o)
anaRange _        _     EmptyR = anaFail
anaRange ins_cost ins_sym range
  = let onedescr           = OneDescr (Succ Zero) (ESym range) [(range, (ins_cost, ins_sym, libAccept))] Nothing
        onep@(Just (rp,_)) = mkParser onedescr
    in AnaParser  rp Nothing onep

anaCostSym   i ins sym = anaRange i ins (Range sym sym)
anaCostRange i ins ran = anaRange i ins ran

-- =======================================================================================
-- ===== UTILITIES ========================================================================
-- =======================================================================================
mapOnePars fp fl ol  = case ol of
                       Just (pp, OneDescr l fi t d) -> Just  (fp pp, OneDescr (fl l) fi [(k, (c, s, fp p))| (k, (c, s, p)) <- t] (fmap fp d))
                       Nothing                      -> Nothing

seqZeroZeroPars zl zr
 = do { (llow, left)  <- zl
      ; (rlow, right) <- zr
      ; return ( llow || rlow
               , case left of
                 Left  lv  -> case right of
                              Left  rv -> Left (lv rv)
                              Right rp -> Right (lv `libDollar` rp)
                 Right lp  -> case right of
                              Left  rv  -> Right (lp `libSeq` libSucceed rv)
                              Right rp  -> Right (lp `libSeq` rp)
               )
      }

orOneOnePars Nothing                    or                                 b = or
orOneOnePars ol                         Nothing                            b = ol
orOneOnePars (Just (pl, OneDescr ll fl tl dl)) (Just (pr, OneDescr lr fr tr dr)) b
 = let newfirsts = ESeq [(fl `unionExp` fr), EStr "..."]
       (newlength, maybeflip) = ll `nat_min` lr
       newtab                 = maybeflip (++) tl tr
       bothp                  = maybeflip libGreedy pl pr
   in if b then Just (bothp, OneDescr newlength newfirsts []     (Just bothp)           )
           else    mkParser (OneDescr newlength newfirsts newtab (maybeComb (maybeflip libOr) dl dr))

maybeComb f Nothing  r        = r
maybeComb f l        Nothing  = l
maybeComb f (Just l) (Just r) = Just (f l r)

combinePars pz po    = case maybeComb (if (fst(fromJust pz)) then libGreedy else libOr)
                                      (anagetonep  po)
                                      (anagetzerop pz)
                       of Nothing -> systemerror "Library" "CombinePars"
                          Just p  -> p

moreThanOneEmpty (Just (_, descr)) _ _ = usererror "Lib" ("Two empty dynamic alternatives, where expecting"++show (firsts descr))

anagetzerop Nothing               = Nothing
anagetzerop (Just (_, Left v  ))  = Just (libSucceed v)
anagetzerop (Just (_, Right pv))  = Just pv
anagetonep lo = maybe Nothing (Just . fst) lo

-- =======================================================================================
-- ===== MKPARSER ========================================================================
-- =======================================================================================
mkParser descr@(OneDescr _ firsts []  (Just dlr)) = Just (dlr, descr)
mkParser descr@(OneDescr _ _      []  Nothing   ) = systemerror "Lib" "mkParser has no alternatives"
mkParser descr@(OneDescr _ firsts tab dlr)
 = let parstab            = foldr1 mergeTables  [[(k, p)]                    | (k, (_   , _  , p)) <- tab]
       insertions firsts  = foldr1 libOr        [libInsert cost sym firsts p | (_, (cost, sym, p)) <- tab]
       locfind = case parstab of
                 [(ran, pp)] -> let comp = symInRange ran
                                in \ s -> if comp s then Just pp else Nothing
                 _   -> btFind symRS.tab2tree $ parstab
       tabpars = P (\k inp
                   -> case splitStateE inp of
                      Left (s, ss) ->   case locfind s of
                                        Just (P p) -> p k inp
                                        Nothing    -> libCorrect
                                                        (unP (libDelete   firsts tabpars) k inp)
                                                        (unP (insertions  firsts        ) k  inp)
                                                        "mkParser"
          {- eof -}   Right _      ->                   unP (insertions   firsts )        k inp
                   )

   in case dlr of
      Nothing  -> Just (          tabpars, descr)
      Just p   -> Just (p `libOr` tabpars, descr)

-- =======================================================================================
-- ===== MINIMAL LENGTHS (lazily formulated) =============================================
-- =======================================================================================
data Nat = Zero
         | Succ Nat
         deriving (Eq, Show)

nat_le Zero      _       = True
nat_le _         Zero    = False
nat_le (Succ l) (Succ r) = nat_le l r

nat_min Zero       _  = (Zero, id)
nat_min (Succ ll)  r  = case r of {Zero -> (Zero, flip) ; Succ rr -> let (v, fl) = ll `nat_min` rr in (Succ v, fl)}

nat_add Zero     r = r
nat_add (Succ l) r = Succ (nat_add l r)
-- =======================================================================================
-- ===== CHOICE STRUCTURES   =============================================================
-- =======================================================================================
mergeTables l []  = l
mergeTables [] r  = r
mergeTables lss@(l@(le@(Range a b),ct ):ls) rss@(r@(re@(Range c d),ct'):rs)
 = let ct'' =  ct `libOr` ct'
   in  if      c<a then   mergeTables rss lss     -- swap
       else if b<c then l:mergeTables ls  rss     -- disjoint case
       else if a<c then (Range a (symBefore c),ct) :mergeTables ((Range c b,ct):ls)             rss
       else if b<d then (Range a b,ct'')           :mergeTables ((Range (symAfter b) d,ct'):rs) ls
       else if b>d then mergeTables rss lss
                   else (le,ct'') : mergeTables ls rs-- equals
