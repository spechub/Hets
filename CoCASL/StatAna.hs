{- |
Module      :  $Header$
Description :  static analysis for CoCASL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  hausmann@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis for CoCASL
-}

module CoCASL.StatAna where

import CoCASL.AS_CoCASL
import CoCASL.Print_AS()
import CoCASL.CoCASLSign

import CASL.Sign
import CASL.MixfixParser
import CASL.ShowMixfix
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.Overload
import CASL.Quantification
import CASL.Fold

import Common.AS_Annotation
import Common.GlobalAnnotations
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel
import Common.Lib.State
import Common.Id
import Common.Result
import Common.DocUtils
import Common.ExtSign

import Data.Maybe (catMaybes)
import Data.List (partition)

type CSign = Sign C_FORMULA CoCASLSign

instance FreeVars C_FORMULA where
    freeVarsOfExt sign cf = case cf of
       BoxOrDiamond _ _ f _ -> freeVars sign f
       _ -> Set.empty

basicCoCASLAnalysis
  :: (BASIC_SPEC C_BASIC_ITEM C_SIG_ITEM C_FORMULA,
      Sign C_FORMULA CoCASLSign, GlobalAnnos)
  -> Result (BASIC_SPEC C_BASIC_ITEM C_SIG_ITEM C_FORMULA,
             ExtSign (Sign C_FORMULA CoCASLSign) Symbol,
             [Named (FORMULA C_FORMULA)])
basicCoCASLAnalysis =
    basicAnalysis minExpForm ana_C_BASIC_ITEM ana_C_SIG_ITEM ana_CMix

ana_CMix :: Mix C_BASIC_ITEM C_SIG_ITEM C_FORMULA CoCASLSign
ana_CMix = emptyMix
    { getBaseIds = ids_C_BASIC_ITEM
    , getSigIds = ids_C_SIG_ITEM
    , getExtIds = \ e -> mkIdSets (Map.keysSet $ constructors e) Set.empty
    , putParen = mapC_FORMULA
    , mixResolve = resolveC_FORMULA
    }

ids_C_BASIC_ITEM :: C_BASIC_ITEM -> IdSets
ids_C_BASIC_ITEM ci = case ci of
    CoFree_datatype al _ ->
        (Set.unions $ map (ids_CODATATYPE_DECL . item) al, Set.empty)
    CoSort_gen al _ -> unite $ map (ids_SIG_ITEMS ids_C_SIG_ITEM . item) al

ids_C_SIG_ITEM :: C_SIG_ITEM -> IdSets
ids_C_SIG_ITEM (CoDatatype_items al _) =
    (Set.unions $ map (ids_CODATATYPE_DECL . item) al, Set.empty)

ids_CODATATYPE_DECL :: CODATATYPE_DECL -> Set.Set Id
ids_CODATATYPE_DECL (CoDatatype_decl _ al _) =
    Set.unions $ map (ids_COALTERNATIVE . item) al

ids_COALTERNATIVE :: COALTERNATIVE -> Set.Set Id
ids_COALTERNATIVE a = case a of
    Co_construct _ mi cs _ -> Set.unions $
        maybe Set.empty single mi : map ids_COCOMPONENTS cs
    CoSubsorts _ _ -> Set.empty

ids_COCOMPONENTS :: COCOMPONENTS -> Set.Set Id
ids_COCOMPONENTS (CoSelect l _ _) = Set.unions $ map single l

data CoRecord a b c d = CoRecord
    { foldBoxOrDiamond :: C_FORMULA -> Bool -> d -> a -> Range -> c
    , foldCoSort_gen_ax :: C_FORMULA -> [SORT] -> [OP_SYMB] -> Bool -> c
    , foldTerm_mod :: MODALITY -> b -> d
    , foldSimple_mod :: MODALITY -> SIMPLE_ID -> d
    }

foldC_Formula :: Record C_FORMULA a b -> CoRecord a b c d -> C_FORMULA -> c
foldC_Formula r cr c = case c of
    BoxOrDiamond b m f ps ->
        foldBoxOrDiamond cr c b (foldModality r cr m) (foldFormula r f) ps
    CoSort_gen_ax s o b -> foldCoSort_gen_ax cr c s o b

foldModality :: Record C_FORMULA a b -> CoRecord a b c d -> MODALITY -> d
foldModality r cr m = case m of
    Term_mod t -> foldTerm_mod cr m $ foldTerm r t
    Simple_mod i -> foldSimple_mod cr m i

mapCoRecord :: CoRecord (FORMULA C_FORMULA) (TERM C_FORMULA) C_FORMULA MODALITY
mapCoRecord = CoRecord
    { foldBoxOrDiamond = \ _ -> BoxOrDiamond
    , foldCoSort_gen_ax = \ _ -> CoSort_gen_ax
    , foldTerm_mod = \ _ -> Term_mod
    , foldSimple_mod = \ _ -> Simple_mod
    }

constCoRecord :: ([a] -> a) -> a -> CoRecord a a a a
constCoRecord join c = CoRecord
    { foldBoxOrDiamond = \ _ _ m f _ -> join [m, f]
    , foldCoSort_gen_ax = \ _ _ _ _ -> c
    , foldTerm_mod = \ _ t -> t
    , foldSimple_mod = \ _ _ -> c
    }

mapC_FORMULA :: C_FORMULA -> C_FORMULA
mapC_FORMULA = foldC_Formula (mkMixfixRecord mapC_FORMULA) mapCoRecord

resolveMODALITY :: MixResolve MODALITY
resolveMODALITY ga ids m = case m of
    Term_mod t ->
        fmap Term_mod $ resolveMixTrm mapC_FORMULA resolveC_FORMULA ga ids t
    _ -> return m

resolveC_FORMULA :: MixResolve C_FORMULA
resolveC_FORMULA ga ids cf = case cf of
   BoxOrDiamond b m f ps -> do
       nm <- resolveMODALITY ga ids m
       nf <- resolveMixFrm mapC_FORMULA resolveC_FORMULA ga ids f
       return $ BoxOrDiamond b nm nf ps
   _ -> error "resolveC_FORMULA"

minExpForm :: Min C_FORMULA CoCASLSign
minExpForm s form =
    let ops = formulaIds s
        minMod md ps = case md of
                  Simple_mod i -> minMod (Term_mod (Mixfix_token i)) ps
                  Term_mod t -> let
                    r = do
                      t2 <- oneExpTerm minExpForm s t
                      let srt = sortOfTerm t2
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
        BoxOrDiamond b m f ps ->
            do nm <- minMod m ps
               f2 <- minExpFORMULA minExpForm s f
               return $ BoxOrDiamond b nm f2 ps
        phi -> return phi

ana_C_SIG_ITEM :: Ana C_SIG_ITEM C_BASIC_ITEM C_SIG_ITEM C_FORMULA CoCASLSign
ana_C_SIG_ITEM _ mi =
    case mi of
    CoDatatype_items al _ ->
        do mapM_ (\ i -> case item i of
                  CoDatatype_decl s _ _ -> addSort NonEmptySorts i s) al
           mapAnM (ana_CODATATYPE_DECL Loose) al
           closeSubsortRel
           return mi

isCoConsAlt :: COALTERNATIVE -> Bool
isCoConsAlt a = case a of
                CoSubsorts _ _ -> False
                _ -> True

getCoSubsorts :: COALTERNATIVE -> [SORT]
getCoSubsorts c = case c of
    CoSubsorts cs _ -> cs
    _ -> []

-- | return list of constructors
ana_CODATATYPE_DECL :: GenKind -> CODATATYPE_DECL -> State CSign [Component]
ana_CODATATYPE_DECL gk (CoDatatype_decl s al _) =
    do ul <- mapM (ana_COALTERNATIVE s) al
       let constr = catMaybes ul
           cs = map fst constr
       if null constr then return ()
          else do addDiags $ checkUniqueness cs
                  let totalSels = Set.unions $ map snd constr
                      wrongConstr = filter ((totalSels /=) . snd) constr
                  addDiags $ map ( \ (c, _) -> mkDiag Error
                      ("total selectors '" ++ showSepList (showString ",")
                       showDoc (Set.toList totalSels)
                       "'\n  must appear in alternative") c) wrongConstr
       case gk of
         Free -> do
           let (alts, subs) = partition isCoConsAlt $ map item al
               sbs = concatMap getCoSubsorts subs
               comps = map (getCoConsType s) alts
               ttrips = map ( \ (a, vs, ses) -> (a, vs, catSels ses))
                            $ map (coselForms1 "X") $ comps
               sels = concatMap ( \ (_, _, ses) -> ses) ttrips
           addSentences $ catMaybes $ map comakeInjective
                            $ filter ( \ (_, _, ces) -> not $ null ces)
                              comps
           addSentences $ makeDisjSubsorts s sbs
           addSentences $ catMaybes $ concatMap
                            ( \ c -> map (comakeDisjToSort c) sbs)
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
              CoSubsorts _ _ ->  error "getCoConsType"
              Co_construct k a l _ -> (k, a, l)
        in (i, OpType part (concatMap
                            (map (opRes . snd) . getCoCompType s) il) s, il)

getCoCompType :: SORT -> COCOMPONENTS -> [(Id, OpType)]
getCoCompType s (CoSelect l (Op_type k args res _) _) =
    map (\ i -> (i, OpType k (args++[s]) res)) l

coselForms :: (Maybe Id, OpType, [COCOMPONENTS]) -> [Named (FORMULA f)]
coselForms x =
  case coselForms1 "X" x of
    (Just (i,f),vs,cs) -> makeSelForms 1 (i,vs,f,cs)
    _ -> []

coselForms1 :: String -> (Maybe Id, OpType, [COCOMPONENTS])
          -> (Maybe (Id, TERM f), [VAR_DECL], [(Maybe Id, OpType)])
coselForms1 str (i, ty, il) =
    let cs = concatMap (getCoCompType $ opRes ty) il
        vs = genSelVars str 1 $ map snd cs
        it = case i of
               Nothing -> Nothing
               Just i' -> Just (i',Application (Qual_op_name i'
                                                 (toOP_TYPE ty) nullRange)
                                              (map toQualVar vs) nullRange)
     in (it, vs, map ( \ (j, typ) -> (Just j, typ)) cs)

comakeDisjToSort :: (Maybe Id, OpType, [COCOMPONENTS]) -> SORT
                     -> Maybe (Named (FORMULA f))
comakeDisjToSort a s = do
    let (i, v, _) = coselForms1 "X" a
        p = posOfId s
    (c,t) <- i
    return $ makeNamed ("ga_disjoint_" ++ showId c "_sort_" ++ showId s "")
               $ mkForall v (Negation (Membership t s p) p) p

comakeInjective :: (Maybe Id, OpType, [COCOMPONENTS])
                     -> Maybe (Named (FORMULA f))
comakeInjective a = do
    let (i1, v1, _) = coselForms1 "X" a
        (i2, v2, _) = coselForms1 "Y" a
    (c,t1) <- i1
    (_,t2) <- i2
    let p = posOfId c
    return $ makeNamed ("ga_injective_" ++ showId c "") $
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
    let p = posOfId c1 `appRange` posOfId c2
    return $ makeNamed ("ga_disjoint_" ++ showId c1 "_" ++ showId c2 "")
              $ mkForall (v1 ++ v2) (Negation (Strong_equation t1 t2 p) p) p

-- | return the constructor and the set of total selectors
ana_COALTERNATIVE :: SORT -> Annoted COALTERNATIVE
                -> State CSign (Maybe (Component, Set.Set Component))
ana_COALTERNATIVE s c =
    case item c of
    CoSubsorts ss _ -> do
        mapM_ (addSubsort s) ss
        return Nothing
    ci -> do
        let cons@(i, ty, il) = getCoConsType s ci
        ul <- mapM (ana_COCOMPONENTS s) il
        let ts = concatMap fst ul
        addDiags $ checkUniqueness (ts ++ concatMap snd ul)
        addSentences $ coselForms cons
        case i of
              Nothing -> return Nothing
              Just i' -> do
                addOp c ty i'
                return $ Just (Component i' ty, Set.fromList ts)


-- | return total and partial selectors
ana_COCOMPONENTS :: SORT -> COCOMPONENTS
               -> State CSign ([Component], [Component])
ana_COCOMPONENTS s c = do
    let cs = getCoCompType s c
    sels <- mapM ( \ (i, ty) ->
                   do addOp (emptyAnno ()) ty i
                      return $ Just $ Component i ty) cs
    return $ partition ((==Total) . opKind . compType) $ catMaybes sels

ana_C_BASIC_ITEM
    :: Ana C_BASIC_ITEM C_BASIC_ITEM C_SIG_ITEM C_FORMULA CoCASLSign
ana_C_BASIC_ITEM mix bi = do
  case bi of
    CoFree_datatype al ps ->
        do mapM_ (\ i -> case item i of
                  CoDatatype_decl s _ _ -> addSort NonEmptySorts i s) al
           mapAnM (ana_CODATATYPE_DECL Free) al
           toCoSortGenAx ps True $ getCoDataGenSig al
           closeSubsortRel
           return bi
    CoSort_gen al ps ->
        do (gs,ul) <- ana_CoGenerated ana_C_SIG_ITEM mix ([], al)
           toCoSortGenAx ps False $ unionGenAx gs
           return $ CoSort_gen ul ps

toCoSortGenAx :: Range -> Bool -> GenAx -> State CSign ()
toCoSortGenAx ps isFree (sorts, rel, ops) = do
    let sortList = Set.toList sorts
        opSyms = map ( \ c -> let ide = compId c in  Qual_op_name ide
                      (toOP_TYPE $ compType c) $ posOfId ide) $ Set.toList ops
        injSyms = map ( \ (s, t) -> let p = posOfId s in
                        Qual_op_name (mkUniqueInjName s t)
                        (Op_type Total [s] t p) p) $ Rel.toList rel
    if null sortList then
              addDiags[Diag Error "missing cogenerated sort" ps]
              else return ()
    addSentences [makeNamed ("ga_cogenerated_" ++ showSepList (showString "_")
                              showId sortList "")
                   $ ExtFORMULA $ CoSort_gen_ax sortList
                               (opSyms ++ injSyms) isFree]

ana_CoGenerated :: Ana C_SIG_ITEM C_BASIC_ITEM C_SIG_ITEM C_FORMULA CoCASLSign
                -> Ana ([GenAx], [Annoted (SIG_ITEMS C_SIG_ITEM C_FORMULA)])
                   C_BASIC_ITEM C_SIG_ITEM C_FORMULA CoCASLSign
ana_CoGenerated anaf mix (_, al) = do
   ul <- mapAnM (ana_SIG_ITEMS minExpForm anaf mix Generated) al
   return (map (getCoGenSig . item) ul, ul)

getCoGenSig :: SIG_ITEMS C_SIG_ITEM C_FORMULA -> GenAx
getCoGenSig si = case si of
      Sort_items _ al _ -> unionGenAx $ map (getGenSorts . item) al
      Op_items al _ -> (Set.empty, Rel.empty,
                           Set.unions (map (getOps . item) al))
      Datatype_items _ dl _ -> getDataGenSig dl
      Ext_SIG_ITEMS (CoDatatype_items dl _) -> getCoDataGenSig dl
      _ -> emptyGenAx

getCoDataGenSig :: [Annoted CODATATYPE_DECL] -> GenAx
getCoDataGenSig dl =
    let get_sel (s, a) = case a of
          CoSubsorts _ _ ->  []
          Co_construct _ _ l _ -> concatMap (getCoCompType s) l
        alts = concatMap (( \ (CoDatatype_decl s al _) ->
                       map ( \ a -> (s, item a)) al) . item) dl
        sorts = map fst alts
        (realAlts, subs) = partition (isCoConsAlt . snd) alts
        sels = map ( \ (i, ot) -> Component i ot) $ concatMap get_sel realAlts
        rel = foldr ( \ (t, a) r ->
                  foldr ( \ s ->
                          Rel.insert s t)
                  r $ getCoSubsorts a)
               Rel.empty subs
        in (Set.fromList sorts, rel, Set.fromList sels)

