{- |
Module      :  $Header$
Description :  Mixfix analysis of terms
Copyright   :  Christian Maeder and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Mixfix analysis of terms
-}

module CASL.MixfixParser
    ( resolveFormula, resolveMixfix, MixResolve
    , resolveMixTrm, resolveMixFrm
    , IdSets, mkIdSets, emptyIdSets, unite, unite2
    , makeRules, Mix (..), emptyMix, extendMix
    , ids_BASIC_SPEC, ids_SIG_ITEMS, ids_OP_ITEM, ids_PRED_ITEM)
    where

import CASL.AS_Basic_CASL
import CASL.ShowMixfix
import CASL.ToDoc ()

import Common.AS_Annotation
import Common.ConvertMixfixToken
import Common.DocUtils
import Common.Earley
import Common.GlobalAnnotations
import Common.Id
import Common.Result

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe

data Mix b s f e = MixRecord
    { getBaseIds :: b -> IdSets -- ^ ids of extra basic items
    , getSigIds :: s -> IdSets  -- ^ ids of extra sig items
    , getExtIds :: e -> IdSets  -- ^ ids of signature extensions
    , mixRules :: (Token -> [Rule], Rules) -- ^ rules for Earley
    , putParen :: f -> f -- ^ parenthesize extended formula
    , mixResolve :: MixResolve f -- ^ resolve extended formula
    }

-- | an initially empty record
emptyMix :: Mix b s f e
emptyMix = MixRecord
    { getBaseIds = const emptyIdSets
    , getSigIds = const emptyIdSets
    , getExtIds = const emptyIdSets
    , mixRules = error "emptyMix"
    , putParen = id
    , mixResolve = const $ const return
    }

extendMix :: Set.Set Token -> Mix b s f e -> Mix b s f e
extendMix ts r = r
  { mixRules = extendRules ts $ mixRules r
  , mixResolve = extendMixResolve ts $ mixResolve r }

-- precompute non-simple op and pred identifier for mixfix rules

-- | the precomputed sets of constant, op, and pred identifiers
type IdSets = ((Set.Set Id, Set.Set Id), Set.Set Id) -- ops are first component

-- | the empty 'IdSets'
emptyIdSets :: IdSets
emptyIdSets = let e = Set.empty in ((e, e), e)

unite2 :: [(Set.Set Id, Set.Set Id)] -> (Set.Set Id, Set.Set Id)
unite2 l = (Set.unions $ map fst l, Set.unions $ map snd l)

-- | union 'IdSets'
unite :: [IdSets] -> IdSets
unite l = (unite2 $ map fst l, Set.unions $ map snd l)

-- | get all ids of a basic spec
ids_BASIC_SPEC :: (b -> IdSets) -> (s -> IdSets) -> BASIC_SPEC b s f -> IdSets
ids_BASIC_SPEC f g (Basic_spec al) =
    unite $ map (ids_BASIC_ITEMS f g . item) al

ids_BASIC_ITEMS :: (b -> IdSets) -> (s -> IdSets)
                -> BASIC_ITEMS b s f -> IdSets
ids_BASIC_ITEMS f g bi = case bi of
    Sig_items sis -> ids_SIG_ITEMS g sis
    Free_datatype _ al _ -> ids_anDATATYPE_DECLs al
    Sort_gen al _ -> unite $ map (ids_SIG_ITEMS g . item) al
    Ext_BASIC_ITEMS b -> f b
    _ -> emptyIdSets

ids_anDATATYPE_DECLs :: [Annoted DATATYPE_DECL] -> IdSets
ids_anDATATYPE_DECLs al =
    (unite2 $ map (ids_DATATYPE_DECL . item) al, Set.empty)

-- | get all ids of a sig items
ids_SIG_ITEMS :: (s -> IdSets) -> SIG_ITEMS s f -> IdSets
ids_SIG_ITEMS f si = let e = Set.empty in case si of
    Sort_items _ _ _ -> emptyIdSets
    Op_items al _ -> (unite2 $ map (ids_OP_ITEM . item) al, e)
    Pred_items al _ -> ((e, e), Set.unions $ map (ids_PRED_ITEM . item) al)
    Datatype_items _ al _ -> ids_anDATATYPE_DECLs al
    Ext_SIG_ITEMS s -> f s

-- | get all op ids of an op item
ids_OP_ITEM :: OP_ITEM f -> (Set.Set Id, Set.Set Id)
ids_OP_ITEM o = let e = Set.empty in case o of
    Op_decl ops (Op_type _ args _ _) _ _ ->
      let s = Set.fromList ops in
      if null args then (s, e) else (e, s)
    Op_defn i (Op_head _ args _ _) _ _ ->
      let s = Set.singleton i in
      if null args then (s, e) else (e, s)

-- | get all pred ids of a pred item
ids_PRED_ITEM :: PRED_ITEM f -> Set.Set Id
ids_PRED_ITEM p = case p of
    Pred_decl preds _ _ -> Set.unions $ map Set.singleton preds
    Pred_defn i _ _ _ -> Set.singleton i

ids_DATATYPE_DECL :: DATATYPE_DECL -> (Set.Set Id, Set.Set Id)
ids_DATATYPE_DECL (Datatype_decl _ al _) =
    unite2 $ map (ids_ALTERNATIVE . item) al

ids_ALTERNATIVE :: ALTERNATIVE -> (Set.Set Id, Set.Set Id)
ids_ALTERNATIVE a = let e = Set.empty in case a of
    Alt_construct _ i cs _ -> let s = Set.singleton i in
      if null cs then (s, e) else (e, Set.unions $ s : map ids_COMPONENTS cs)
    Subsorts _ _ -> (e, e)

ids_COMPONENTS :: COMPONENTS -> Set.Set Id
ids_COMPONENTS c = case c of
    Cons_select _ l _ _ -> Set.unions $ map Set.singleton l
    Sort _ -> Set.empty

-- predicates get lower precedence
mkRule :: Id -> Rule
mkRule = mixRule 1

mkSingleArgRule :: Int -> Id -> Rule
mkSingleArgRule b ide = (protect ide, b, getPlainTokenList ide ++ [varTok])

mkArgsRule :: Int -> Id -> Rule
mkArgsRule b ide =
  (protect ide, b, getPlainTokenList ide ++ getTokenPlaceList tupleId)

singleArgId :: Id
singleArgId = mkId [exprTok, varTok]

multiArgsId :: Id
multiArgsId = mkId (exprTok : getPlainTokenList tupleId)

-- | additional scan rules
addRule :: GlobalAnnos -> [Rule] -> Bool -> IdSets -> Token -> [Rule]
addRule ga uRules hasInvisible ((consts, ops), preds) tok =
    let addP = Set.fold (\ i@(Id (t : _) _ _) ->
               Map.insertWith (++) t
                [ mixRule (if Set.member i consts then 1 else 0) i
                , mkSingleArgRule 0 i, mkArgsRule 0 i])
        addO = Set.fold (\ i@(Id (t : _) _ _) ->
               Map.insertWith (++) t
                 $ [mkRule i | not (isSimpleId i)
                   || Set.member i (Set.union consts preds) ]
                 ++ [mkSingleArgRule 1 i, mkArgsRule 1 i])
        addC = Set.fold (\ i@(Id (t : _) _ _) ->
               Map.insertWith (++) t [mkRule i])
        lm = foldr ( \ r@(_, _, t : _) -> Map.insertWith (++) t [r])
             Map.empty $ listRules 1 ga
        (spreds, rpreds) = Set.partition isSimpleId preds
        -- do not add simple ids as preds as these may be variables
        -- with higher precedence
        ops2 = Set.union ops spreds
        sops = Set.union consts ops2
        rConsts = Set.difference consts $ Set.union ops preds
        varR = mkRule varId
        m = Map.insert placeTok uRules
            $ Map.insert varTok [varR]
            $ Map.insert exprTok
                  [varR, mkRule singleArgId, mkRule multiArgsId]
            $ addP (addC (addO lm ops2) rConsts) $ Set.difference rpreds ops
        tId = mkId [tok]
        tPId = mkId [tok, placeTok] -- prefix identifier
    in (if isSimpleToken tok && not (Set.member tId sops)
        then if hasInvisible then [] else mkRule tId
             -- add rule for unknown constant or variable
             : if Set.member tPId ops || Set.member tPId rpreds
               then [] else [mkSingleArgRule 1 tId, mkArgsRule 1 tId]
              -- add also rules for undeclared op
        else []) ++ Map.findWithDefault [] tok m

-- insert only identifiers starting with a place
initRules :: (Set.Set Id, Set.Set Id) -> Rules
initRules (opS, predS) =
    let addR p = Set.fold ((:) . mixRule p)
    in (addR 1 (addR 0 [mkRule typeId] predS) opS, [])

-- | construct rules from 'IdSets' to be put into a 'Mix' record
makeRules :: GlobalAnnos -> IdSets -> (Token -> [Rule], Rules)
makeRules ga ((constS, opS), predS) = let
    (cOps, sOps) = Set.partition begPlace opS
    (cPreds, sPreds) = Set.partition begPlace $ Set.difference predS opS
    addR p = Set.fold ( \ i l ->
           mkSingleArgRule p i : mkArgsRule p i : l)
    uRules = addR 0 (addR 1 [] cOps) cPreds
    in (addRule ga uRules (Set.member applId $ Set.union cOps cPreds)
        ((constS, sOps), sPreds), initRules (cOps, cPreds))

-- | construct application
asAppl :: Id -> [TERM f] -> Range -> TERM f
asAppl f args ps = Application (Op_name f) args
                 $ if isNullRange ps then posOfId f else ps

-- | constructing the parse tree from (the final) parser state(s)
toAppl :: GetRange f => Id -> [TERM f] -> Range -> TERM f
toAppl ide ar ps =
       if elem ide [singleArgId, multiArgsId]
            then case ar of
              har : tar -> case har of
                 Application q [] p ->
                     Application q tar $ appRange ps p
                 Mixfix_qual_pred _ ->
                     Mixfix_term [har, Mixfix_parenthesized tar ps]
                 _ -> error "stateToAppl"
              _ -> error "stateToAppl2"
            else asAppl ide ar ps

addType :: TERM f -> TERM f -> TERM f
addType tt t =
    case tt of
    Mixfix_sorted_term s ps -> Sorted_term t s ps
    Mixfix_cast s ps -> Cast t s ps
    _ -> error "addType"

-- | the type for mixfix resolution
type MixResolve f = GlobalAnnos -> (Token -> [Rule], Rules) -> f -> Result f

iterateCharts :: (GetRange f, Pretty f) => (f -> f)
              -> MixResolve f -> GlobalAnnos -> [TERM f]
              -> Chart (TERM f) -> Chart (TERM f)
iterateCharts par extR g terms c =
    let self = iterateCharts par extR g
        expand = expandPos Mixfix_token
        oneStep = nextChart addType toAppl g c
        ruleS = rules c
        adder = addRules c
        resolveTerm = resolveMixTrm par extR g (adder, ruleS)
    in case terms of
    [] -> c
    hd : tl -> case hd of
            Mixfix_term ts -> self (ts ++ tl) c
            Mixfix_bracketed ts ps ->
                self (expand ("[", "]") ts ps ++ tl) c
            Mixfix_braced ts ps ->
                self (expand ("{", "}") ts ps ++ tl) c
            Mixfix_parenthesized ts ps -> case ts of
              [h] -> let
                Result mds v = resolveTerm h
                c2 = self tl (oneStep (fromMaybe h v, varTok {tokPos = ps}))
                in mixDiags mds c2
              _ -> self (expand ("(", ")") ts ps ++ tl) c
            h@(Conditional t1 f2 t3 ps) -> let
              Result mds v = do
                t4 <- resolveTerm t1
                f5 <- resolveMixFrm par extR g (adder, ruleS) f2
                t6 <- resolveTerm t3
                return (Conditional t4 f5 t6 ps)
              c2 = self tl
                   (oneStep (fromMaybe h v, varTok {tokPos = ps}))
              in mixDiags mds c2
            Mixfix_token t -> let
              (ds1, trm) = convertMixfixToken (literal_annos g) asAppl
                Mixfix_token t
              c2 = self tl $ oneStep $ case trm of
                Mixfix_token tok -> (trm, tok)
                _ -> (trm, varTok {tokPos = tokPos t})
              in mixDiags ds1 c2
            t@(Mixfix_sorted_term _ ps) ->
              self tl (oneStep (t, typeTok {tokPos = ps}))
            t@(Mixfix_cast _ ps) ->
              self tl (oneStep (t, typeTok {tokPos = ps}))
            t@(Qual_var _ _ ps) ->
              self tl (oneStep (t, varTok {tokPos = ps}))
            t@(Application (Qual_op_name _ _ ps) _ _) ->
                self tl (oneStep (t, exprTok {tokPos = ps} ))
            t@(Mixfix_qual_pred (Qual_pred_name _ _ ps)) ->
                self tl (oneStep (t, exprTok {tokPos = ps} ))
            Sorted_term t s ps -> let
              Result mds v = resolveTerm t
              tNew = Sorted_term (fromMaybe t v) s ps
              c2 = self tl (oneStep (tNew, varTok {tokPos = ps}))
              in mixDiags mds c2
            _ -> error "iterateCharts"

-- | construct 'IdSets' from op and pred identifiers
mkIdSets :: Set.Set Id -> Set.Set Id -> Set.Set Id -> IdSets
mkIdSets consts ops preds = ((consts, ops), preds)

-- | top-level resolution like 'resolveMixTrm' that fails in case of diags
resolveMixfix :: (GetRange f, Pretty f) => (f -> f)
              -> MixResolve f -> MixResolve (TERM f)
resolveMixfix par extR g ruleS t =
    let r@(Result ds _) = resolveMixTrm par extR g ruleS t
        in if null ds then r else Result ds Nothing

-- | basic term resolution that supports recursion without failure
resolveMixTrm :: (GetRange f, Pretty f) => (f -> f)
              -> MixResolve f -> MixResolve (TERM f)
resolveMixTrm par extR ga (adder, ruleS) trm =
    getResolved (showTerm par ga) (getRangeSpan trm) toAppl
           $ iterateCharts par extR ga [trm] $ initChart adder ruleS

showTerm :: Pretty f => (f -> f) -> GlobalAnnos -> TERM f -> ShowS
showTerm par ga = showGlobalDoc ga . mapTerm par

-- | top-level resolution like 'resolveMixFrm' that fails in case of diags
resolveFormula :: (GetRange f, Pretty f) => (f -> f)
               -> MixResolve f -> MixResolve (FORMULA f)
resolveFormula par extR g ruleS f =
    let r@(Result ds _) = resolveMixFrm par extR g ruleS f
        in if null ds then r else Result ds Nothing

varDeclTokens :: [VAR_DECL] -> Set.Set Token
varDeclTokens = Set.unions . map (\ (Var_decl vs _ _) -> Set.fromList vs)

extendRules :: Set.Set Token -> (Token -> [Rule], Rules)
  -> (Token -> [Rule], Rules)
extendRules ts (f, rs) =
  (\ t -> let
     l = f t
     r = mkRule $ mkId [t]
     in if Set.member t ts then
         if elem r l then l else r : l
     else l, rs)

extendMixResolve :: Set.Set Token -> MixResolve f -> MixResolve f
extendMixResolve ts f ga = f ga . extendRules ts

-- | basic formula resolution that supports recursion without failure
resolveMixFrm :: (GetRange f, Pretty f) => (f -> f)
              -> MixResolve f -> MixResolve (FORMULA f)
resolveMixFrm par extR g ids frm =
    let self = resolveMixFrm par extR g ids
        resolveTerm = resolveMixTrm par extR g ids in
    case frm of
       Quantification q vs fOld ps ->
           do let ts = varDeclTokens vs
              fNew <- resolveMixFrm par (extendMixResolve ts extR)
                g (extendRules ts ids) fOld
              return $ Quantification q vs fNew ps
       Conjunction fsOld ps ->
           do fsNew <- mapM self fsOld
              return $ Conjunction fsNew ps
       Disjunction fsOld ps ->
           do fsNew <- mapM self fsOld
              return $ Disjunction fsNew ps
       Implication f1 f2 b ps ->
           do f3 <- self f1
              f4 <- self f2
              return $ Implication f3 f4 b ps
       Equivalence f1 f2 ps ->
           do f3 <- self f1
              f4 <- self f2
              return $ Equivalence f3 f4 ps
       Negation fOld ps ->
           do fNew <- self fOld
              return $ Negation fNew ps
       Predication sym tsOld ps ->
           do tsNew <- mapM resolveTerm tsOld
              return $ Predication sym tsNew ps
       Definedness tOld ps ->
           do tNew <- resolveTerm tOld
              return $ Definedness tNew ps
       Existl_equation t1 t2 ps ->
           do t3 <- resolveTerm t1
              t4 <- resolveTerm t2
              return $ Existl_equation t3 t4 ps
       Strong_equation t1 t2 ps ->
           do t3 <- resolveTerm t1
              t4 <- resolveTerm t2
              return $ Strong_equation t3 t4 ps
       Membership tOld s ps ->
           do tNew <- resolveTerm tOld
              return $ Membership tNew s ps
       Mixfix_formula tOld ->
           do tNew <- resolveTerm tOld
              case tNew of
                 Application (Op_name ide) args ps ->
                     return $ Predication (Pred_name ide) args ps
                 Mixfix_qual_pred qide ->
                     return $ Predication qide [] nullRange
                 Mixfix_term [Mixfix_qual_pred qide,
                              Mixfix_parenthesized ts ps] ->
                     return $ Predication qide ts ps
                 _ -> fatal_error
                        ("not a formula: " ++ showTerm par g tNew "")
                        (getRangeSpan tNew)
       ExtFORMULA f ->
           do newF <- extR g ids f
              return $ ExtFORMULA newF
       f -> return f
