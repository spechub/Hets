{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

   static analysis for CoCASL
-}

{- todo:
  correct map_C_FORMULA
  translation of cogen ax
  analysis of modal formulas
  Add cofree axioms
  remove disjointness axioms
  leave out sorts/profiles for pretty printing
-}

module CoCASL.StatAna where

import CoCASL.AS_CoCASL
import CoCASL.Print_AS
import CoCASL.CoCASLSign

import CASL.Sign
import CASL.MixfixParser
import CASL.Utils
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.Overload
import CASL.MapSentence

import Common.AS_Annotation
import qualified Common.Lib.Set as Set
import Common.Lib.State
import Common.Id
import Common.Result

import Data.Maybe
import Data.List

type CSign = Sign C_FORMULA CoCASLSign

resolveMODALITY :: MixResolve MODALITY
resolveMODALITY ga ids m = case m of 
    Term_mod t -> fmap Term_mod $ resolveMixTrm resolveC_FORMULA ga ids t
    _ -> return m

resolveC_FORMULA :: MixResolve C_FORMULA
resolveC_FORMULA ga ids cf = case cf of 
   Box m f ps -> do 
       nm <- resolveMODALITY ga ids m
       nf <- resolveMixFrm resolveC_FORMULA ga ids f
       return $ Box nm nf ps
   Diamond m f ps -> do 
       nm <- resolveMODALITY ga ids m
       nf <- resolveMixFrm resolveC_FORMULA ga ids f
       return $ Diamond nm nf ps
   _ -> error "resolveC_FORMULA"

noExtMixfixCo :: C_FORMULA -> Bool
noExtMixfixCo cf = 
    let noInner = noMixfixF noExtMixfixCo in
    case cf of
    Box _ f _     -> noInner f
    Diamond _ f _ -> noInner f
    _ -> True

minExpForm :: Min C_FORMULA CoCASLSign
minExpForm ga s form = 
    let ops = formulaIds s
        minMod md ps = case md of
                  Simple_mod i -> minMod (Term_mod (Mixfix_token i)) ps
                  Term_mod t -> let
                    r = do 
                      ts <- minExpTerm minExpForm ga s t
                      t2 <- is_unambiguous t ts ps
                      let srt = term_sort t2
                          trm = Term_mod t2
                      if Set.member srt ops 
                         then return trm
                         else Result [mkDiag Error 
                              ("unknown modality '"
                               ++ showId srt "' for term") t ]
                              $ Just trm
                    in case t of
                       Mixfix_token tm -> 
                           if Set.member (simpleIdToId tm) ops 
                              then return $ Simple_mod tm
                              else case maybeResult r of
                                  Nothing -> Result 
                                      [mkDiag Error "unknown modality" tm]
                                      $ Just $ Simple_mod tm
                                  _ -> r
                       _ -> r
    in case form of
        Box m f ps -> 
            do nm <- minMod m ps
               f2 <- minExpFORMULA minExpForm ga s f
               return $ Box nm f2 ps
        Diamond m f ps -> 
            do nm <- minMod m ps
               f2 <- minExpFORMULA minExpForm ga s f
               return $ Diamond nm f2 ps
        phi -> return phi

ana_C_SIG_ITEM :: Ana C_SIG_ITEM C_FORMULA CoCASLSign
ana_C_SIG_ITEM _ mi = 
    case mi of 
    CoDatatype_items al _ -> 
        do let sorts = map (( \ (CoDatatype_decl s _ _) -> s) . item) al
           mapM_ addSort sorts
           mapAnM (ana_CODATATYPE_DECL Loose) al 
           closeSubsortRel
           return mi

-- | return list of constructors 
ana_CODATATYPE_DECL :: GenKind -> CODATATYPE_DECL -> State CSign [Component]
ana_CODATATYPE_DECL gk (CoDatatype_decl s al _) = 
    do ul <- mapM (ana_COALTERNATIVE s . item) al
       let constr = catMaybes ul
           cs = map fst constr              
       if null constr then return ()
          else do addDiags $ checkUniqueness cs
                  let totalSels = Set.unions $ map snd constr
                      wrongConstr = filter ((totalSels /=) . snd) constr
                  addDiags $ map ( \ (c, _) -> mkDiag Error 
                      ("total selectors '" ++ showSepList (showString ",")
                       showPretty (Set.toList totalSels) 
                       "'\n  must appear in alternative") c) wrongConstr
       case gk of 
         Free -> do 
           let allts = map item al
               (alts, subs) = partition ( \ a -> case a of 
                               CoSubsorts _ _ -> False
                               _ -> True) allts
               sbs = concatMap ( \ (CoSubsorts ss _) -> ss) subs
               comps = map (getCoConsType s) alts
               ttrips = map ( \ (a, vs, ses) -> (a, vs, catSels ses))
                            $ map (coselForms1 "X") $ comps 
               sels = concatMap ( \ (_, _, ses) -> ses) ttrips
           addSentences $ catMaybes $ map comakeInjective 
                            $ filter ( \ (_, _, ces) -> not $ null ces) 
                              comps
           addSentences $ catMaybes $ concatMap ( \ as -> map (comakeDisjToSort as) sbs)
                        comps 
           addSentences $ comakeDisjoint comps 
           let ttrips' = [(a,vs,t,ses) | (Just(a,t),vs,ses) <- ttrips]
           addSentences $ catMaybes $ concatMap 
                             ( \ ses -> 
                               map (makeUndefForm ses) ttrips') sels
         _ -> return ()
       return cs

getCoConsType :: SORT -> COALTERNATIVE -> (Maybe Id, OpType, [COCOMPONENTS])
getCoConsType s c = 
    let (part, i, il) = case c of 
                        CoSubsorts _ _ ->  error "getConsType"
                        CoTotal_construct a l _ -> (Total, a, l)
                        CoPartial_construct a l _ -> (Partial, a, l)
        in (i, OpType part (concatMap 
                            (map (opRes . snd) . getCoCompType s) il) s, il)

getCoCompType :: SORT -> COCOMPONENTS -> [(Maybe Id, OpType)]
getCoCompType s (CoSelect l (Total_op_type args res _) _) = 
    map (\ i -> (Just i, OpType Total (args++[s]) res)) l
getCoCompType s (CoSelect l (Partial_op_type args res _) _) = 
    map (\ i -> (Just i, OpType Partial (args++[s]) res)) l

coselForms :: (Maybe Id, OpType, [COCOMPONENTS]) -> [Named (FORMULA f)]
coselForms x = 
  case coselForms1 "X" x of
    (Just (i,f),vs,cs) -> makeSelForms 1 (i,vs,f,cs)
    _ -> []

coselForms1 :: String -> (Maybe Id, OpType, [COCOMPONENTS]) 
          -> (Maybe (Id, TERM f), [VAR_DECL], [(Maybe Id, OpType)])
coselForms1 str (i, ty, il) = 
    let cs = concatMap (getCoCompType $ opRes ty) il
        vs = genSelVars str 1 cs 
        it = case i of
               Nothing -> Nothing
               Just i' -> Just (i',Application (Qual_op_name i' 
                                                 (toOP_TYPE ty) [])
                                              (map toQualVar vs) [])
     in (it, vs, cs)

comakeDisjToSort :: (Maybe Id, OpType, [COCOMPONENTS]) -> SORT 
                     -> Maybe (Named (FORMULA f))
comakeDisjToSort a s = do
    let (i, v, _) = coselForms1 "X" a 
        p = [posOfId s]
    (c,t) <- i 
    return $ NamedSen ("ga_disjoint_" ++ showId c "_sort_" ++ showId s "") $
        mkForall v (Negation (Membership t s p) p) p

comakeInjective :: (Maybe Id, OpType, [COCOMPONENTS]) 
                     -> Maybe (Named (FORMULA f))
comakeInjective a = do
    let (i1, v1, _) = coselForms1 "X" a
        (i2, v2, _) = coselForms1 "Y" a
    (c,t1) <- i1
    (_,t2) <- i2
    let p = [posOfId c]
    return $ NamedSen ("ga_injective_" ++ showId c "") $
       mkForall (v1 ++ v2) 
       (Equivalence (Strong_equation t1 t2 p)
        (let ces = zipWith ( \ w1 w2 -> Strong_equation 
                             (toQualVar w1) (toQualVar w2) p) v1 v2
         in if isSingle ces then head ces else Conjunction ces p)
        p) p

comakeDisjoint :: [(Maybe Id, OpType, [COCOMPONENTS])] -> [Named (FORMULA f)]
comakeDisjoint [] = []
comakeDisjoint (a:as) = catMaybes (map (comakeDisj a) as) ++ comakeDisjoint as
comakeDisj :: (Maybe Id, OpType, [COCOMPONENTS]) 
                           -> (Maybe Id, OpType, [COCOMPONENTS])
                           -> Maybe (Named (FORMULA f))
comakeDisj a1 a2 = do
    let (i1, v1, _) = coselForms1 "X" a1
        (i2, v2, _) = coselForms1 "Y" a2
    (c1,t1) <- i1
    (c2,t2) <- i2
    let p = [posOfId c1, posOfId c2]
    return $ NamedSen ("ga_disjoint_" ++ showId c1 "_" ++ showId c2 "") $
       mkForall (v1 ++ v2) 
       (Negation (Strong_equation t1 t2 p) p) p

-- | return the constructor and the set of total selectors 
ana_COALTERNATIVE :: SORT -> COALTERNATIVE 
                -> State CSign (Maybe (Component, Set.Set Component))
ana_COALTERNATIVE s c = 
    case c of 
    CoSubsorts ss _ ->
        do mapM_ (addSubsort s) ss
           return Nothing
    _ -> do let cons@(i, ty, il) = getCoConsType s c
            ul <- mapM (ana_COCOMPONENTS s) il
            let ts = concatMap fst ul
            addDiags $ checkUniqueness (ts ++ concatMap snd ul)
            addSentences $ coselForms cons
            case i of 
              Nothing -> return Nothing
              Just i' -> do
                addOp ty i'
                return $ Just (Component i' ty, Set.fromList ts) 

 
-- | return total and partial selectors
ana_COCOMPONENTS :: SORT -> COCOMPONENTS 
               -> State CSign ([Component], [Component])
ana_COCOMPONENTS s c = do
    let cs = getCoCompType s c
    sels <- mapM ( \ (mi, ty) -> 
            case mi of 
            Nothing -> return Nothing
            Just i -> do addOp ty i
                         return $ Just $ Component i ty) cs 
    return $ partition ((==Total) . opKind . compType) $ catMaybes sels 

ana_C_BASIC_ITEM :: Ana C_BASIC_ITEM C_FORMULA CoCASLSign
ana_C_BASIC_ITEM ga bi = do
  case bi of
    CoFree_datatype al ps -> 
        do let sorts = map (( \ (CoDatatype_decl s _ _) -> s) . item) al
           mapM_ addSort sorts
           mapAnM (ana_CODATATYPE_DECL Free) al 
           toCoSortGenAx ps True $ getCoDataGenSig al
           closeSubsortRel 
           return bi
    CoSort_gen al ps ->
        do (gs,ul) <- ana_CoGenerated ana_C_SIG_ITEM ga ([], al)
           toCoSortGenAx ps False 
                (Set.unions $ map fst gs, Set.unions $ map snd gs)
           return $ CoSort_gen ul ps

toCoSortGenAx :: [Pos] -> Bool ->
               (Set.Set Id, Set.Set Component) -> State CSign ()
toCoSortGenAx ps isFree (sorts, ops) = do
    let sortList = Set.toList sorts
        opSyms = map ( \ c ->  Qual_op_name (compId c)  
                      (toOP_TYPE $ compType c) []) $ Set.toList ops
        f = ExtFORMULA $ CoSort_gen_ax sortList opSyms isFree
    if null sortList then 
              addDiags[Diag Error "missing cogenerated sort" (headPos ps)]
              else return ()
    addSentences [NamedSen ("ga_cogenerated_" ++ 
                         showSepList (showString "_") showId sortList "") f]

ana_CoGenerated :: Ana C_SIG_ITEM C_FORMULA e 
                -> Ana ([(Set.Set Id, Set.Set Component)], 
                        [Annoted (SIG_ITEMS C_SIG_ITEM C_FORMULA)]) C_FORMULA e
ana_CoGenerated anaf ga (_, al) = do
   ul <- mapAnM (ana_SIG_ITEMS resolveC_FORMULA 
                 noExtMixfixCo anaf ga Generated) al
   return (map (getCoGenSig . item) ul,ul)
   
getCoGenSig :: SIG_ITEMS C_SIG_ITEM C_FORMULA 
                -> (Set.Set Id, Set.Set Component)
getCoGenSig si = case si of 
      Sort_items al _ -> (Set.unions (map (getSorts . item) al), Set.empty)
      Op_items al _ -> (Set.empty, Set.unions (map (getOps . item) al))
      Datatype_items dl _ -> getDataGenSig dl
      Ext_SIG_ITEMS (CoDatatype_items dl _) -> getCoDataGenSig dl
      _ -> (Set.empty, Set.empty)

getCoDataGenSig :: [Annoted CODATATYPE_DECL] -> (Set.Set Id, Set.Set Component)
getCoDataGenSig dl = 
    let get_sel1 s al = case al of 
          CoSubsorts _ _ ->  []
          CoTotal_construct _ l _ -> concatMap (getCoCompType s) l
          CoPartial_construct _ l _ -> concatMap (getCoCompType s) l
        get_sel (s,als) = concatMap (get_sel1 s . item) als 
        alts = map (( \ (CoDatatype_decl s al _) -> (s, al)) . item) dl
        sorts = map fst alts
        sels = concatMap computeComp $ concatMap get_sel alts
        computeComp (Just i,ot) = [Component i ot]
        computeComp _ = []
        in (Set.fromList sorts, Set.fromList sels)

resultToState :: (a -> Result a) -> a -> State (Sign f e) a
resultToState f a = do 
    let r =  f a 
    addDiags $ reverse $ diags r
    case maybeResult r of
        Nothing -> return a
        Just b -> return b


map_C_FORMULA :: MapSen C_FORMULA CoCASLSign ()
map_C_FORMULA mor frm =
    let mapMod m = case m of 
                   Simple_mod _ -> return m
                   Term_mod t -> do newT <- mapTerm map_C_FORMULA mor t
                                    return $ Term_mod newT
        in case frm of
           Box m f ps -> do 
               newF <- mapSen map_C_FORMULA mor f
               newM <- mapMod m 
               return $ Box newM newF ps 
           Diamond m f ps -> do 
               newF <- mapSen map_C_FORMULA mor f
               newM <- mapMod m 
               return $ Diamond newM newF ps 
           phi -> return phi


