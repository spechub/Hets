{- --------------------------------------------------------------------------
  HetCATS/CASL/Static.hs
  $Id$
  Authors: Pascal Schmidt
  Year:    2002
-----------------------------------------------------------------------------
  SUMMARY
  
  This modules provides static analysis for the BASIC_SPEC datatype
  found in AS_Basic_CASL
   
-----------------------------------------------------------------------------
  TODO

  implement meaningful functions

-------------------------------------------------------------------------- -}

-----------------------------------------------------------------------------
-- Export declarations
-----------------------------------------------------------------------------

module Static ( basicAnalysis, statSymbMapItems, statSymbItems,
                symbolToRaw, idToRaw, symOf, symmapOf, matches,
                isSubSig, symName ) where

------------------------------------------------------------------------------
-- Imports from other modules
------------------------------------------------------------------------------

import Maybe
import FiniteMap
import Set
import Id
import AS_Annotation
import GlobalAnnotations
import GlobalAnnotationsFunctions
import AS_Basic_CASL
import Sign
import Result
import Graph
import Latin
import Utils
import Logic ( EndoMap )

------------------------------------------------------------------------------
--
--                               Datatypes
--
------------------------------------------------------------------------------

type Filename = String

data GlobalVars = Global { global :: [VarDecl] }
                  deriving (Eq,Show)

data NamedSentence = NamedSen { senName  :: String,
                                sentence :: Sentence }
                     deriving (Eq,Show)

data Sentences = Sentences { sentences :: [NamedSentence] }
                 deriving (Eq,Show)

data LocalEnv = Env { getName   :: Filename,
                      getGA     :: GlobalAnnos,
                      getSign   :: Sign,
                      getPsi    :: Sentences,
                      getGlobal :: GlobalVars }

type ExtPos = (Pos, TokenKind)

------------------------------------------------------------------------------
--
--                              Helper functions
--
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- helper functions on datatypes
------------------------------------------------------------------------------

emptyGlobal :: GlobalVars
emptyGlobal = Global []

emptySentences :: Sentences
emptySentences = Sentences []

emptyLocalEnv :: LocalEnv
emptyLocalEnv =
  Env "empty" emptyGlobalAnnos emptySign emptySentences emptyGlobal

emptyPos :: Pos
emptyPos = (0,0)

emptyExtPos :: ExtPos
emptyExtPos = (emptyPos, Key)

flattenSentences :: Sentences -> [(String, Sentence)]
flattenSentences sens = map (\x -> (senName x,sentence x)) (sentences sens)

addNamedSentences :: Sentences -> [NamedSentence] -> Sentences
addNamedSentences (Sentences s) l = Sentences (setAdd s l)

myShowList :: Show a => [a] -> String
myShowList []    = "[]"
myShowList [h]   = "'" ++ show h ++ "'"
myShowList (h:t) = "'" ++ (show h) ++ "', " ++ (myShowList t)

cloneAnnos :: Annoted a -> b -> Annoted b
cloneAnnos a b = a { item = b }

labelAnno :: String -> b -> Annoted b
labelAnno name itm = Annoted itm [] [] [Label [name] []]

noAnnos :: a -> Annoted a
noAnnos itm = Annoted itm [] [] []

annoFilter :: Annotation -> Maybe Annotation
annoFilter x = case x of Label _ _ -> Just x;
                                 _ -> Nothing

cloneAnnoFormula :: Annoted a -> b -> Annoted b
cloneAnnoFormula a b = Annoted b [] (mapMaybe annoFilter $ l_annos a)
                                    (mapMaybe annoFilter $ r_annos a)

mergeAnnos :: Annoted a -> Annoted b -> Annoted b
mergeAnnos a b = b { opt_pos = setAdd (opt_pos a) (opt_pos b),
                     l_annos = setAdd (l_annos a) (l_annos b),
                     r_annos = setAdd (r_annos a) (r_annos b) }

------------------------------------------------------------------------------
-- special functions to generate token lists from Pos lists
------------------------------------------------------------------------------

toExtPos :: Maybe ExtPos -> [Pos] -> ([Pos] -> [TokenKind]) -> [ExtPos]
toExtPos pre p f = let
                     tokens = (zip p (f p))
                   in
                     case pre of Nothing -> tokens;
                                 Just ep -> ep:tokens

tokPos_sort_decl :: [Pos] -> [TokenKind]
tokPos_sort_decl l = replicate (length l) Comma

tokPos_subsort_decl :: [Pos] -> [TokenKind]
tokPos_subsort_decl []    = []
tokPos_subsort_decl (h:t) = (replicate (length t) Comma) ++ [Less]

tokPos_subsort_defn :: [Pos] -> [TokenKind]
tokPos_subsort_defn _ = [Equal,Key,Colon,Comma,Key]

tokPos_iso_decl :: [Pos] -> [TokenKind]
tokPos_iso_decl l = replicate (length l) Colon

tokPos_SORT_ITEM :: [Pos] -> [TokenKind]
tokPos_SORT_ITEM []    = []
tokPos_SORT_ITEM (h:t) = Key:(replicate (length t) Semi)

tokPos_pred_decl :: [Pos] -> [TokenKind]
tokPos_pred_decl []    = []
tokPos_pred_decl (h:t) = (replicate (length t) Comma) ++ [Colon]

tokPos_VAR_DECL :: [Pos] -> [TokenKind]
tokPos_VAR_DECL = tokPos_pred_decl

tokPos_pred_defn :: [Pos] -> [TokenKind]
tokPos_pred_defn _ = [Key]

tokPos_ARG_DECL :: [Pos] -> [TokenKind]
tokPos_ARG_DECL = tokPos_pred_decl

tokPos_ARG_DECL_list :: [Pos] -> [TokenKind]
tokPos_ARG_DECL_list []        = []
tokPos_ARG_DECL_list [h]       = []
tokPos_ARG_DECL_list (_:(_:t)) = (Key:(replicate (length t) Semi)) ++ [Key]

tokPos_PRED_ITEM :: [Pos] -> [TokenKind]
tokPos_PRED_ITEM = tokPos_SORT_ITEM

tokPos_VAR_ITEM :: [Pos] -> [TokenKind]
tokPos_VAR_ITEM = tokPos_SORT_ITEM

tokPos_local_var_axioms :: [Pos] -> [TokenKind]
tokPos_local_var_axioms []    = []
tokPos_local_var_axioms (h:t) = Key:(replicate (length t) Key)

tokPos_axiom_items :: [Pos] -> [TokenKind]
tokPos_axiom_items = tokPos_local_var_axioms

tokPos_select :: [Pos] -> [TokenKind]
tokPos_select = tokPos_pred_decl

tokPos_construct :: [Pos] -> [TokenKind]
tokPos_construct = tokPos_SORT_ITEM

tokPos_subsorts :: [Pos] -> [TokenKind]
tokPos_subsorts [] = []
tokPos_subsorts (h:t) = Key:(replicate (length t) Comma)

tokPos_DATATYPE_DECL :: [Pos] -> [TokenKind]
tokPos_DATATYPE_DECL l = replicate (length l) Key

tokPos_datatype_items :: [Pos] -> [TokenKind]
tokPos_datatype_items = tokPos_SORT_ITEM

tokPos_OP_ITEM :: [Pos] -> [TokenKind]
tokPos_OP_ITEM = tokPos_SORT_ITEM

------------------------------------------------------------------------------
-- functions to generate labels
------------------------------------------------------------------------------

someLabel :: String -> Annoted a -> String
someLabel def x =
  let
    labels = filter (\x -> case x of (Label s p) -> True;
                                               _ -> False)
                    ((l_annos x)++(r_annos x))
  in
    case labels of ((Label s p):t) -> concat s;
                                 _ -> def

toLabel :: Show a => a -> String
toLabel x = toASCII $ show x

------------------------------------------------------------------------------
-- conversion from simple to compound datatypes
------------------------------------------------------------------------------

toListPos :: ExtPos -> ListPos
toListPos (pos,tok) = ListPos tok pos

toItemPos :: Filename -> ExtPos -> ItemPos
toItemPos name (pos,tok) = ItemPos name tok [pos]

toVarDecl :: SortId -> ExtPos -> VAR -> VarDecl
toVarDecl sort pos var = VarDecl var sort (toListPos pos)

toVarDecls :: SortId -> [ExtPos] -> [VAR] -> [VarDecl]
toVarDecls sort p v = map (uncurry (toVarDecl sort))
                          (zip (extendList emptyExtPos v p) v)

typeToVarDecl :: OpType -> [VarDecl]
typeToVarDecl t = map (\(s,v) -> VarDecl v s (ListPos Key emptyPos))
                  $ zip (opArgs t) $ map mkSimpleId $ map (\x -> "x" ++ x)
                  $ map show $ [1..(length $ opArgs t)]

toVarId :: VarDecl -> Term
toVarId v = VarId (simpleIdToId $ varId v) (varSort v) Inferred []

opToApplSentence :: OpItem -> [NamedSentence]
opToApplSentence itm =
  let
    name   = case (opId itm) of Id [x] [] [] -> (case x
                                                   of Token name _ -> name;
                                                                 _ -> "");
                                           _ -> ""
    optype = opType itm
    vars   = typeToVarDecl optype
    terms  = map toVarId vars
    res    = opRes optype
  in
    [NamedSen name
     (Axiom (noAnnos (AxiomDecl vars (ElemTest (OpAppl (opId itm) optype terms
                                               Inferred []) res []) [])))]

toGenItems :: [OpItem] -> [Pos] -> NamedSentence
toGenItems ops pos = NamedSen ""
                     (GenItems (map (\x -> Symbol (opId x)
                                          (OpAsItemType (opType x))) ops) pos)

toFunKind :: Bool -> FunKind
toFunKind False = Partial
toFunKind _     = Total

sortToSymbol :: SortId -> Symbol
sortToSymbol s = Symbol s Sign.Sort

opTypeIdToSymbol :: OpType -> Id -> Symbol
opTypeIdToSymbol typ id = Symbol id (OpAsItemType typ)

toNamedSentence :: [VarDecl] -> String -> Annoted Formula -> NamedSentence
toNamedSentence vars str f =
  NamedSen str
    (Axiom (cloneAnnos f (AxiomDecl vars (item f) [])))

------------------------------------------------------------------------------
-- foldTwo: foldResult function over two lists
--  makes sure second list is at least as long as the first
--  add a default element if not
-- foldPos: same for foldl
------------------------------------------------------------------------------

extendList :: b -> [a] -> [b] -> [b]
extendList def a b = if ((length b) < (length a)) then
                       b ++ replicate ((length a)-(length b)) def
                     else b

foldTwo :: a -> c -> (a -> b -> c -> Result a) -> [b] -> [c] -> Result a
foldTwo state def f a b = foldResult state (\st (x, y) -> f st x y)
                                     (zip a (extendList def a b))

foldlTwo :: c -> (a -> b -> c -> a) -> a -> [b] -> [c] -> a
foldlTwo def f init a b = foldl (\st (x, y) -> f st x y) init
                                (zip a (extendList def a b))

foldPos :: (Sign -> a -> ExtPos -> Sign) -> Sign -> [a] -> [ExtPos] -> Sign
foldPos f sigma a pos = foldlTwo emptyExtPos f sigma a pos

chainPos :: b -> (b -> a -> ExtPos -> Result b) -> [a] -> [ExtPos] -> [Pos]
            -> ([Pos] -> [TokenKind]) -> Result b
chainPos env f items positions addPos toStrFun =
  foldTwo env emptyExtPos f items (positions ++ (zip addPos (toStrFun addPos)))

------------------------------------------------------------------------------
-- element test and selector functions for SigItem
------------------------------------------------------------------------------

hasElem :: Sign -> (Id -> SigItem -> Bool) -> Id -> Bool
hasElem sigma f id =
  let
    res = lookupFM (getMap sigma) id
  in
    if (isJust res) then
      or $ map (f id) (fromJust res)
    else
      False

getElem :: Sign -> (Id -> SigItem -> Bool) -> Id -> Maybe SigItem
getElem sigma f id =
  if (hasElem sigma f id) then
    Just (head $ filter (f id) $ fromJust $ lookupFM (getMap sigma) id)
  else
    Nothing

isSigSortItem :: Id -> SigItem -> Bool
isSigSortItem id (ASortItem s) = (sortId $ item s)==id
isSigSortItem _ _ = False

isSigOpItem :: Id -> SigItem -> Bool
isSigOpItem id (AnOpItem o) = (opId $ item o)==id
isSigOpItem _ _ = False

isSigPredItem :: Id -> SigItem -> Bool
isSigPredItem id (APredItem p) = (predId $ item p)==id
isSigPredItem _ _ = False

toSortItem :: Maybe SigItem -> Maybe (Annoted SortItem)
toSortItem (Just (ASortItem s)) = Just s
toSortItem _ = Nothing

toOpItem :: Maybe SigItem -> Maybe (Annoted OpItem)
toOpItem (Just (AnOpItem o)) = Just o
toOpItem _ = Nothing

toPredItem :: Maybe SigItem -> Maybe (Annoted PredItem)
toPredItem (Just (APredItem p)) = Just p
toPredItem _ = Nothing

hasSort :: Sign -> SortId -> Bool
hasSort sigma id = hasElem sigma isSigSortItem id

hasOp :: Sign -> Id -> Bool
hasOp sigma id = hasElem sigma isSigOpItem id

hasPred :: Sign -> Id -> Bool
hasPred sigma id = hasElem sigma isSigPredItem id

lookupSort :: Sign -> SortId -> Maybe (Annoted SortItem)
lookupSort sigma id = toSortItem $ getElem sigma isSigSortItem id

lookupOp :: Sign -> Id -> Maybe (Annoted OpItem)
lookupOp sigma id = toOpItem $ getElem sigma isSigOpItem id

lookupPred :: Sign -> Id -> Maybe (Annoted PredItem)
lookupPred sigma id = toPredItem $ getElem sigma isSigPredItem id

getSort :: Sign -> SortId -> Annoted SortItem
getSort sigma id = fromJust $ lookupSort sigma id

getOp :: Sign -> Id -> Annoted OpItem
getOp sigma id = fromJust $ lookupOp sigma id

getPred :: Sign -> Id -> Annoted PredItem
getPred sigma id = fromJust $ lookupPred sigma id

------------------------------------------------------------------------------
-- update function for SigItem in Sign
------------------------------------------------------------------------------

updateSigItem :: Sign -> Id -> SigItem -> Sign
updateSigItem sigma id itm =
  let
    res = lookupFM (getMap sigma) id
    new = if (isNothing res) then
            [itm]
          else
             [ x | x<-(fromJust res), x /= itm ] ++ [itm]
  in
    sigma { getMap = addToFM (getMap sigma) id new }

------------------------------------------------------------------------------
-- functions for SortItem generation and modification
------------------------------------------------------------------------------

addSuper :: SortRels -> Bool -> [SortId] -> SortRels
addSuper rels _      []         = rels
addSuper rels direct (id:allid) =
  if direct then
    rels { supersorts   = setAddOne (supersorts rels) id,
           allsupersrts = setAdd  (allsupersrts rels) (id:allid) }
  else
    rels { allsupersrts = setAdd (allsupersrts rels) (id:allid) }

addSub :: SortRels -> Bool -> [SortId] -> SortRels
addSub rels _      []         = rels
addSub rels direct (id:allid) =
  if direct then
    rels { subsorts   = setAddOne (subsorts rels) id,
           allsubsrts = setAdd  (allsubsrts rels) (id:allid) }
  else
    rels { allsubsrts = setAdd (allsubsrts rels) (id:allid) }

addSubsort :: SortId -> Sign -> SortId -> Sign
addSubsort super sigma sub =
  let
    subItem   = getSort sigma sub
    allSubs   = allsubsrts $ sortRels $ item subItem
    superItem = getSort sigma super
    allSupers = allsupersrts $ sortRels $ item superItem
    newSub    = ASortItem (subItem { item = (item subItem)
                { sortRels =
                  addSuper (sortRels $ item subItem) True (super:allSupers)}})
    newSuper  = ASortItem (superItem { item = (item superItem)
                { sortRels =
                  addSub (sortRels $ item superItem) True (sub:allSubs) }})
    withSub   = updateSigItem (updateSigItem sigma sub newSub) super newSuper
    iterSuper = foldl (addSubsorts (sub:allSubs)) withSub allSupers
  in
    foldl (addSupersorts (super:allSupers)) iterSuper allSubs

addSubsorts :: [SortId] -> Sign -> SortId -> Sign
addSubsorts subs sigma super =
  let
    res = getSort sigma super
    new = res { item = (item res)
                       { sortRels =
                         addSub (sortRels $ item res) False subs } }
  in
    updateSigItem sigma super (ASortItem new)
    
addSupersorts :: [SortId] -> Sign -> SortId -> Sign
addSupersorts supers sigma sub =
  let
    res = getSort sigma sub
    new = res { item = (item res)
                       { sortRels =
                         addSuper (sortRels $ item res) False supers } }
  in
    updateSigItem sigma sub (ASortItem new)

addIsoSubsorting :: [SortId] -> Sign -> SortId -> Sign
addIsoSubsorting all sigma sort =
  let
    others = [ x | x<-all, x/=sort ]
    res    = getSort sigma sort
    old    = sortRels $ item res
    new    = old { subsorts = setAdd (subsorts old) others,
                   supersorts = setAdd (supersorts old) others,
                   allsubsrts = setAdd (allsubsrts old) others,
                   allsupersrts = setAdd (allsupersrts old) others }
    ext     = (item res) { sortRels = new }
  in
    updateSigItem sigma sort (ASortItem (res { item = ext }))

updateSortItem :: Filename -> Annoted a -> Maybe SortDefn -> Sign -> SortId
                  -> ExtPos -> Sign
updateSortItem name ann defn sigma id kwpos =
  let
    res = lookupSort sigma id
    pos = toItemPos name kwpos
    new = if (isJust res) then
            let
              itm = fromJust res
              old = item itm
            in
              mergeAnnos itm (cloneAnnos ann
              old { sortDef  = case defn of Nothing -> sortDef old;
                                               defn -> defn,
                    sortPos  = pos,
                    altSorts = (altSorts old) ++ [sortPos old] })
          else
            cloneAnnos ann (SortItem id emptySortRels defn pos [])
  in
    updateSigItem sigma id (ASortItem new)

------------------------------------------------------------------------------
-- PredItem generation
------------------------------------------------------------------------------

updatePredItem :: Filename -> Annoted PRED_ITEM -> PredType -> Maybe PredDefn
                  -> Sign -> Id -> ExtPos -> Sign
updatePredItem name ann typ defn sigma id pos =
  let
    res  = lookupPred sigma id
    ppos = toItemPos name pos
    new  = if (isJust res) then
             let
               old = fromJust res
               itm = item old
             in
               mergeAnnos old (cloneAnnos ann
               itm { predDefn = case defn of Nothing -> predDefn itm;
                                              Just x -> Just x,
                     predPos  = ppos,
                     altPreds = (altPreds itm) ++ [predPos itm] })
           else
             cloneAnnos ann (PredItem id typ defn ppos [])
  in
    updateSigItem sigma id (APredItem new)

------------------------------------------------------------------------------
-- OpItem generation
------------------------------------------------------------------------------

updateOpItem :: Filename -> Annoted a -> OpType -> Maybe OpDefn -> Sign
                -> Id -> ExtPos -> Sign
updateOpItem name ann typ defn sigma id pos = sigma

------------------------------------------------------------------------------
--
--                             Static Analysis
--                                BASIC-SPEC
--
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- FORMULA
-- FIXME, dummy implementation
------------------------------------------------------------------------------

ana_FORMULA :: LocalEnv -> Annoted FORMULA -> Result (Annoted Formula)
ana_FORMULA sigma f = return (cloneAnnoFormula f (TrueAtom []))

ana_no_anno_FORMULA :: LocalEnv -> Annoted FORMULA -> Result Formula
ana_no_anno_FORMULA sigma f = ana_FORMULA sigma f >>= (return . item)

------------------------------------------------------------------------------
-- SORT-DECL
------------------------------------------------------------------------------

ana_sort_decl :: LocalEnv -> Annoted SORT_ITEM -> [SortId] -> [ExtPos]
                 -> Result LocalEnv
ana_sort_decl sigma _itm s _pos =
  return sigma { getSign = foldPos (updateSortItem (getName sigma) _itm
                                    Nothing) (getSign sigma) s _pos }

------------------------------------------------------------------------------
-- SUBSORT-DECL
------------------------------------------------------------------------------

checkSubsDistinctSuper :: Pos -> [SortId] -> SortId -> Result ()
checkSubsDistinctSuper _pos s_n s =
  if (s `notElem` s_n) then
    return ()
  else
    fatal_error "subsort not distinct from supersort" _pos

ana_subsort_decl :: LocalEnv -> Annoted SORT_ITEM -> Maybe SortDefn -> [SortId]
                    -> SortId -> [ExtPos] -> Result LocalEnv
ana_subsort_decl sigma _itm _defn s_n s _pos =
  do checkSubsDistinctSuper (fst $ head _pos) s_n s
     let _delta = foldPos (updateSortItem (getName sigma) _itm _defn)
                           (getSign sigma) (s:s_n) _pos
     let embed  = foldl (addSubsort s) _delta s_n
     return sigma { getSign = embed }

------------------------------------------------------------------------------
-- SUBSORT-DEFN
------------------------------------------------------------------------------

subsortLabel :: SortId -> SortId -> String
subsortLabel s s' = "ga_subsort_defn_" ++ (toLabel s) ++ "_"
                     ++ (toLabel s') ++ "_"

checkSortExists :: LocalEnv -> Pos -> SortId -> Result ()
checkSortExists sigma _pos s' =
  if ((getSign sigma) `hasSort` s') then
    return ()
  else
    fatal_error ("sort '"++(show s')++"' is not declared") _pos

ana_subsort_defn :: LocalEnv -> Annoted SORT_ITEM -> SortId -> VAR -> SortId
                    -> Annoted FORMULA -> [ExtPos] -> Result LocalEnv
ana_subsort_defn sigma _itm s v s' f _pos =
  let
    _colpos = head $ drop 3 _pos
    f'      = cloneAnnoFormula f (Quantification Universal [(Var_decl [v] s'
                            [fst _colpos])] (Equivalence (item f) (Membership
                            (Simple_id v) s []) []) [])
  in
    do checkSortExists sigma (fst $ head _pos) s'
       _f       <- ana_no_anno_FORMULA sigma f
       let _defn = SubsortDefn (toVarDecl s' _colpos v) _f
                               (map fst $ tail _pos)
       delta    <- ana_subsort_decl sigma _itm (Just _defn) [s] s' _pos
       _f'      <- ana_FORMULA delta { getGlobal = emptyGlobal } f'
       let phi   = toNamedSentence [] (someLabel (subsortLabel s s') f) _f'
       return delta { getPsi = addNamedSentences (getPsi delta) [phi] }

------------------------------------------------------------------------------
-- ISO-DECL
------------------------------------------------------------------------------

checkAllUnique :: Pos -> [SortId] -> Result ()
checkAllUnique _pos s_n =
  if (allUnique s_n) then
    return ()
  else
    fatal_error ("multiple occurences of sort(s): "
                 ++ (myShowList $ notUnique s_n)) _pos

checkGreaterOrEqualTwo :: Pos -> [SortId] -> Result ()
checkGreaterOrEqualTwo _pos s_n =
  if ((length s_n)>=2) then
    return ()
  else
    fatal_error "single sort in isomorphism decl" _pos

ana_iso_decl :: LocalEnv -> Annoted SORT_ITEM -> [SortId] -> [ExtPos]
                -> Result LocalEnv
ana_iso_decl sigma _itm s_n _pos =
  do checkAllUnique (fst $ head _pos) s_n
     checkGreaterOrEqualTwo (fst $ head _pos) s_n
     let _delta = foldPos (updateSortItem (getName sigma) _itm Nothing)
                          (getSign sigma) s_n _pos
     let embed  = foldl (addIsoSubsorting s_n) _delta s_n
     return sigma { getSign = embed }

------------------------------------------------------------------------------
-- SORT-ITEM
------------------------------------------------------------------------------

ana_SORT_ITEM :: LocalEnv -> Annoted SORT_ITEM -> ExtPos -> Result LocalEnv
ana_SORT_ITEM sigma _itm _pos =
  case (item _itm) of
    (Sort_decl s_n _p)
      -> ana_sort_decl sigma _itm s_n
                       (toExtPos (Just _pos) _p tokPos_sort_decl);
    (Subsort_decl s_n s _p)
      -> ana_subsort_decl sigma _itm Nothing s_n s
                          (toExtPos (Just _pos) _p tokPos_subsort_decl);
    (Subsort_defn s v s' f _p)
      -> ana_subsort_defn sigma _itm s v s' f
                          (toExtPos (Just _pos) _p tokPos_subsort_defn);
    (Iso_decl s_n _p)
      -> ana_iso_decl sigma _itm s_n
                      (toExtPos (Just _pos) _p tokPos_iso_decl)

------------------------------------------------------------------------------
-- PRED-DECL
------------------------------------------------------------------------------

ana_PRED_TYPE' :: LocalEnv -> PredType -> PRED_TYPE -> ExtPos 
                 -> Result PredType
ana_PRED_TYPE' sigma w (Pred_type [] _) _pos = return w
ana_PRED_TYPE' sigma w (Pred_type (s_n:_t) _) _pos =
  do checkSortExists sigma (fst _pos) s_n
     ana_PRED_TYPE' sigma (w++[s_n]) (Pred_type _t []) _pos

ana_PRED_TYPE :: LocalEnv -> PRED_TYPE -> ExtPos -> Result PredType
ana_PRED_TYPE sigma _t _pos = ana_PRED_TYPE' sigma [] _t _pos

ana_pred_decl :: LocalEnv -> Annoted PRED_ITEM -> [PRED_NAME] -> PRED_TYPE
                 -> [ExtPos] -> Result LocalEnv
ana_pred_decl sigma _itm p_n _t _pos =
  do w <- ana_PRED_TYPE sigma _t (head _pos)
     let delta = foldPos (updatePredItem (getName sigma) _itm w Nothing)
                         (getSign sigma) p_n _pos
     return sigma { getSign = delta }

------------------------------------------------------------------------------
-- PRED-DEFN
------------------------------------------------------------------------------

predDefnLabel :: PRED_NAME -> [VarDecl] -> String
predDefnLabel n v = "ga_pred_defn_" ++ (toLabel n) ++ "_" ++
                     (concat $ map (\x -> toLabel (varId x) ++ "_") v)

checkVarsUnique :: [VAR] -> Pos -> Result ()
checkVarsUnique x_n _pos =
  if (allUnique x_n) then
    return ()
  else
    fatal_error ("variables not unique in arg-decl: (" ++
                  (myShowList $ notUnique x_n) ++ ")") _pos

ana_ARG_DECL :: LocalEnv -> [VAR] -> SortId -> [ExtPos]
                -> Result ([VAR],SortId)
ana_ARG_DECL sigma x_n s _pos =
  do checkSortExists sigma (fst $ last _pos) s
     checkVarsUnique x_n (fst $ head _pos)
     return (x_n,s)

checkQualVarsUnique :: Pos -> [VarDecl] -> [VarDecl] -> Result ()
checkQualVarsUnique _pos a b =
  if (allUnique (a++b)) then
    return ()
  else
    fatal_error "overlapping variable names" _pos

ana_ARG_DECL_list' :: LocalEnv -> ([VarDecl],[SortId]) -> [ARG_DECL]
               -> Result ([VarDecl],[SortId])
ana_ARG_DECL_list' sigma (x_s_n,w) [] = return (x_s_n,w)
ana_ARG_DECL_list' sigma (x_s_n,w) ((Arg_decl _v _s _pos):_t) =
  do let _extPos = zip _pos (tokPos_ARG_DECL _pos)
     (x_n,s) <- ana_ARG_DECL sigma _v _s _extPos
     let _qual = toVarDecls s _extPos x_n
     checkQualVarsUnique (head _pos) x_s_n _qual
     ana_ARG_DECL_list' sigma (x_s_n ++ _qual,w ++ [s]) _t

ana_ARG_DECL_list :: LocalEnv -> [ARG_DECL] -> Result ([VarDecl],[SortId])
ana_ARG_DECL_list sigma _ad = ana_ARG_DECL_list' sigma ([],[]) _ad

ana_pred_defn :: LocalEnv -> Annoted PRED_ITEM -> PRED_NAME -> PRED_HEAD
                 -> Annoted FORMULA -> [ExtPos] -> Result LocalEnv
ana_pred_defn sigma _ann p (Pred_head _ad _pos') _f _pos =
  do (_x_s_n,w) <- ana_ARG_DECL_list sigma _ad
     let _delta' = updatePredItem (getName sigma) _ann w Nothing
                                  (getSign sigma) p (head _pos)
     phi        <- ana_no_anno_FORMULA (sigma { getSign = _delta',
                                        getGlobal = Global _x_s_n }) _f
     let _defn   = PredDef _x_s_n phi (_pos' ++ [(fst $ last _pos)])
     let delta   = updatePredItem (getName sigma) _ann w (Just _defn)
                                  _delta' p (head _pos)
     return sigma { getSign = delta,
                    getPsi   = addNamedSentences (getPsi sigma)
                               [toNamedSentence [] (someLabel
                               (predDefnLabel p (_x_s_n)) _f)
                               (cloneAnnos _f (Quantified Forall _x_s_n
                               (Connect EquivOp [PredAppl p w
                               (map toVarId _x_s_n) Inferred [],phi]
                               [])[]))] }

------------------------------------------------------------------------------
-- PRED-ITEM
------------------------------------------------------------------------------

ana_PRED_ITEM :: LocalEnv -> Annoted PRED_ITEM -> ExtPos -> Result LocalEnv
ana_PRED_ITEM sigma _itm _pos =
  case (item _itm) of
    (Pred_decl p_n _t _p)  -> ana_pred_decl sigma _itm p_n _t
                              (toExtPos (Just _pos) _p tokPos_pred_decl);
    (Pred_defn p _h _f _p) -> ana_pred_defn sigma _itm p _h _f
                              (toExtPos (Just _pos) _p tokPos_pred_defn)

------------------------------------------------------------------------------
-- OP-ITEMS
------------------------------------------------------------------------------

ana_OP_ITEM :: LocalEnv -> Annoted OP_ITEM -> ExtPos -> Result LocalEnv
ana_OP_ITEM sigma _itm _pos =
  return sigma

------------------------------------------------------------------------------
-- DATATYPE-ITEMS
------------------------------------------------------------------------------

ana_sig_COMPONENTS' :: LocalEnv -> SortId -> [Id] -> SortId -> [SortId]
                      -> Result (LocalEnv, [SortId])
ana_sig_COMPONENTS' sigma s f_n s' w' =
  return
       (sigma { getSign = foldPos
                           (updateOpItem (getName sigma) (noAnnos s')
                                         (OpType Partial [s'] s) Nothing)
                                         (getSign sigma) f_n [] },
        w'++[s'])

ana_sig_COMPONENTS :: SortId -> (LocalEnv, [SortId]) -> COMPONENTS
                      -> Result (LocalEnv, [SortId])
ana_sig_COMPONENTS s (sigma,_s) _c =
  let
    (f_n,s') = case _c of Total_select   _a _b _ -> (_a,_b);
                          Partial_select _a _b _ -> (_a,_b);
                          AS_Basic_CASL.Sort  _a -> ([],_a)
  in
    ana_sig_COMPONENTS' sigma s f_n s' _s

ana_sig_ALTERNATIVE :: SortId -> Id -> LocalEnv -> [COMPONENTS]
                       -> Result LocalEnv
ana_sig_ALTERNATIVE s f sigma _cl =
  do (delta,s_n) <- foldResult (sigma,[]) (ana_sig_COMPONENTS s) _cl
     return delta
              { getSign = updateOpItem (getName sigma) (noAnnos s)
                                       (OpType Total s_n s) Nothing
                                       (getSign sigma) f emptyExtPos }
                                       

ana_sig_DATATYPE_DECL :: LocalEnv -> SortId -> [Annoted ALTERNATIVE]
                         -> Result LocalEnv
ana_sig_DATATYPE_DECL sigma s _alt =
  let
    _sigma = sigma { getSign = updateSortItem (getName sigma) (noAnnos s)
                               Nothing (getSign sigma) s emptyExtPos }
    _getComps = (\x -> case (item x)
                         of Total_construct _id _cl _   -> Just (_id,_cl);
                            Partial_construct _id _cl _ -> Just (_id,_cl);
                            Subsorts _ _                -> Nothing)
    _alist = mapMaybe _getComps _alt
  in
    foldResult _sigma (\st x -> ana_sig_ALTERNATIVE s (fst x) st (snd x))
               _alist

ana_sig_datatype_items :: LocalEnv -> Annoted DATATYPE_DECL
                          -> Result LocalEnv
ana_sig_datatype_items sigma _dd =
  let
    (s,_alt) = case (item _dd) of Datatype_decl _a _b _ -> (_a,_b)
  in
    do ana_sig_DATATYPE_DECL sigma s _alt

ana_COMPONENTS' :: (LocalEnv, LocalEnv) -> Annoted DATATYPE_DECL -> SortId
                   -> SortId -> [Id] -> Bool -> ExtPos -> [ExtPos] ->
                   [SortId] -> Result (LocalEnv, LocalEnv, OpType, [SortId])
ana_COMPONENTS' (sigma, sigma') _ann s s' f_n _total _pos _p w' =
  do checkSortExists sigma (fst _pos) s'
     let _t = OpType (toFunKind _total) [s'] s
     return (case f_n of [] -> (sigma,sigma',_t,w'++[s']);
                          _ -> (sigma,sigma' { getSign = foldPos (updateOpItem
                                (getName sigma') _ann _t Nothing)
                                (getSign sigma') f_n _p },_t,w'++[s']))

ana_COMPONENTS :: Annoted DATATYPE_DECL -> SortId
                  -> (LocalEnv, LocalEnv, [([Id], OpType)], [SortId])
                  -> COMPONENTS -> ExtPos ->
                  Result (LocalEnv, LocalEnv, [([Id], OpType)], [SortId])
ana_COMPONENTS _ann s (sigma, sigma',_ws,_w') _c _pos =
  let
    (_total,f_n,s',_p) =
      case _c of Total_select _ids _s' _p   -> (True,_ids,_s',_p);
                 Partial_select _ids _s' _p -> (False,_ids,_s',_p);
                 AS_Basic_CASL.Sort _s'     -> (True,[],_s',[])
    _pos' = toExtPos (Just _pos) _p tokPos_select
  in
    do (delta,delta',_t,w') <- ana_COMPONENTS' (sigma,sigma') _ann s s' f_n
                                               _total _pos _pos' []
       return (delta,delta',_ws++[(f_n,_t)],_w'++w')

ana_ALTERNATIVE :: (LocalEnv, LocalEnv, FiniteMap Symbol [Symbol], Bool)
                   -> Annoted DATATYPE_DECL -> SortId -> Bool -> Id
                   -> [COMPONENTS] -> ExtPos -> [Pos] ->
                   Result (LocalEnv, LocalEnv, FiniteMap Symbol [Symbol],
                           Bool)
ana_ALTERNATIVE (sigma,sigma',w,flag) _ann s _total f _comps _pos _p =
  do (delta,delta',_ws,w') <- chainPos (sigma,sigma',[],[])
                              (ana_COMPONENTS _ann s)
                              _comps [] _p tokPos_construct
     let _t = OpType (toFunKind _total) w' s
     let _w = concat $ map (\(o,typ) -> map (\id -> opTypeIdToSymbol typ id) o)
                           _ws
     return (delta { getSign = updateOpItem (getName delta) _ann _t
                               (Just (Constr (sortToSymbol s))) (getSign delta)
                               f _pos },delta',
                     addToFM_C (++) w (opTypeIdToSymbol _t f) _w,
                     flag)

ana_subsorts :: (LocalEnv, LocalEnv, FiniteMap Symbol [Symbol])
                -> SortId -> [SortId] -> [Pos] ->
                Result (LocalEnv, LocalEnv, FiniteMap Symbol [Symbol], Bool)
ana_subsorts (sigma,sigma',w) s s_n _p =
  do chainPos () (\_ s' _pos -> checkSortExists sigma (fst _pos) s') s_n []
              _p tokPos_subsorts
     return (sigma { getSign = foldl (addSubsort s) (getSign sigma) s_n },
             sigma',w,True)

ana_DATATYPE_DECL :: SortId -> Annoted DATATYPE_DECL
                     -> (LocalEnv, LocalEnv, FiniteMap Symbol [Symbol], Bool)
                     -> Annoted ALTERNATIVE -> ExtPos ->
                     Result (LocalEnv, LocalEnv, FiniteMap Symbol [Symbol],
                             Bool)
ana_DATATYPE_DECL s _ann (sigma,sigma',w,flag) _alt _pos =
  case (item _alt) of
    Total_construct _id _comps _p   -> ana_ALTERNATIVE (sigma,sigma',w,flag)
                                       _ann s True _id _comps _pos _p;
    Partial_construct _id _comps _p -> ana_ALTERNATIVE (sigma,sigma',w,flag)
                                       _ann s False _id _comps _pos _p;
    Subsorts s_n _p                 -> ana_subsorts (sigma,sigma',w)
                                       s s_n _p
 
ana_datatype_items' :: (LocalEnv, LocalEnv, FiniteMap Symbol [Symbol], Bool)
                       -> Annoted DATATYPE_DECL -> ExtPos ->
                       Result (LocalEnv, LocalEnv, FiniteMap Symbol [Symbol],
                               Bool)
ana_datatype_items' (sigma,sigma',w,flag) _dd _pos =
  let
    (s,_alt,_p) = case (item _dd) of Datatype_decl _a _b _c -> (_a,_b,_c)
    _sigma      = sigma { getSign = updateSortItem (getName sigma)
                                    (noAnnos _dd) Nothing
                                    (getSign sigma) s _pos }
  in
    chainPos (_sigma,sigma',w,flag) (ana_DATATYPE_DECL s _dd) _alt [_pos] _p
             tokPos_DATATYPE_DECL

ana_datatype_items :: LocalEnv -> [Annoted DATATYPE_DECL] -> [Pos] ->
                      Result (LocalEnv, LocalEnv, FiniteMap Symbol [Symbol],
                              Bool)
ana_datatype_items sigma _dd _pos =
  do sigma' <- foldResult sigma ana_sig_datatype_items _dd
     chainPos (sigma,sigma',emptyFM,False) ana_datatype_items' _dd [] _pos
              tokPos_datatype_items

------------------------------------------------------------------------------
-- SIG-ITEMS
------------------------------------------------------------------------------

ana_SIG_ITEMS :: (LocalEnv, LocalEnv) -> SIG_ITEMS
                 -> Result (LocalEnv, LocalEnv)
ana_SIG_ITEMS (sigma,_) _itm =
  case _itm of
    Sort_items _l _p     -> do _res <- chainPos sigma ana_SORT_ITEM _l [] _p
                                                tokPos_SORT_ITEM
                               return (_res,_res);
    Op_items _l _p       -> do _res <- chainPos sigma ana_OP_ITEM _l [] _p
                                                tokPos_OP_ITEM
                               return (_res,_res);
    Pred_items _l _p     -> do _res <- chainPos sigma ana_PRED_ITEM _l [] _p
                                                tokPos_PRED_ITEM
                               return (_res,_res);
    Datatype_items _l _p -> do (_res,_res',_,_) <- ana_datatype_items
                                                   sigma _l _p
                               return (_res,_res')

------------------------------------------------------------------------------
-- VAR-DECL
------------------------------------------------------------------------------

ana_VAR_DECL :: LocalEnv -> VAR_DECL -> ExtPos -> Result LocalEnv
ana_VAR_DECL sigma (Var_decl x_n s _pos') _pos =
  do checkSortExists sigma (fst _pos) s
     let _extPos = toExtPos Nothing _pos' tokPos_VAR_DECL
     let _decls  = toVarDecls s _extPos x_n
     return sigma { getGlobal = Global (setAdd (global $ getGlobal sigma)
                                                _decls) }

------------------------------------------------------------------------------
-- VAR-ITEMS
------------------------------------------------------------------------------

ana_VAR_ITEMS :: LocalEnv -> [VAR_DECL] -> [Pos] -> Result LocalEnv
ana_VAR_ITEMS sigma _v _pos =
  chainPos sigma ana_VAR_DECL _v [] _pos tokPos_VAR_ITEM

------------------------------------------------------------------------------
-- LOCAL-VAR-AXIOMS
------------------------------------------------------------------------------

ana_local_var_axioms' :: LocalEnv -> Annoted FORMULA -> ExtPos ->
                         Result LocalEnv
ana_local_var_axioms' sigma _f _pos =
  do _phi     <- ana_FORMULA sigma _f
     let _phi' = toNamedSentence (global $ getGlobal sigma)
                                 (someLabel "" _phi) _phi
     return sigma { getPsi = addNamedSentences (getPsi sigma) [_phi'] }

ana_local_var_axioms :: LocalEnv -> [VAR_DECL] -> [Pos] ->
                        [Annoted FORMULA] -> [Pos] -> Result LocalEnv
ana_local_var_axioms sigma _v _vpos _f _apos =
  do _delta <- ana_VAR_ITEMS sigma _v _vpos
     chainPos _delta ana_local_var_axioms' _f [] _apos tokPos_local_var_axioms

------------------------------------------------------------------------------
-- AXIOM-ITEMS
------------------------------------------------------------------------------

ana_axiom_items :: LocalEnv -> [Annoted FORMULA] -> [Pos] -> Result LocalEnv
ana_axiom_items sigma _f _pos =
  chainPos sigma ana_local_var_axioms' _f [] _pos tokPos_axiom_items

------------------------------------------------------------------------------
-- SORT-GEN
------------------------------------------------------------------------------

checkSortsExist :: Sign -> Pos -> Result ()
checkSortsExist sigma _pos =
  let
    _sorts = filter (\x -> case x of ASortItem _ -> True;
                                               _ -> False)
                    (concat $ map snd $ fmToList $ getMap sigma)
  in 
    if (null _sorts) then
      fatal_error "sort-gen did not declare any sorts" _pos
    else
      return ()

toGenEmbedLabel :: SortId -> SortId -> String
toGenEmbedLabel s s' = "ga_embedding_" ++ (toLabel s) ++ "_" ++ (toLabel s')

toGenProjLabel :: SortId -> SortId -> String
toGenProjLabel s s' = "ga_projection_" ++ (toLabel s) ++ "_" ++ (toLabel s')

toEmAndPr :: LocalEnv -> Pos -> [OpItem]
toEmAndPr delta' pos =
  let
    _embed = let
               _sit = (\x -> ASortItem (noAnnos (SortItem x emptySortRels
                                     Nothing (toItemPos "" emptyExtPos) [])))
               _rem = (\x -> case x of ASortItem s -> Just (item s);
                                                 _ -> Nothing)
               _all = foldFM (\id itm l -> (mapMaybe _rem
                                           (filter ((==) (_sit id)) itm))
                                           ++l) [] (getMap $ getSign delta')
             in
               concat $ map (\x -> map ((\i j -> (i,j)) (sortId x))
                            (allsupersrts $ sortRels x)) _all
    em     = (\(s,s') -> OpItem (simpleIdToId $ mkSimpleId $ (toGenEmbedLabel
                                 s s')) (OpType Total [s] s') [] Nothing
                                 (ItemPos "" Key []) [])
    pr     = (\(s,s') -> OpItem (simpleIdToId $ mkSimpleId  $ (toGenProjLabel
                                 s s')) (OpType Partial [s'] s) [] Nothing
                                 (ItemPos "" Key []) [])
  in
    (map em _embed) ++ (map pr _embed)

ana_sort_gen :: LocalEnv -> [Annoted SIG_ITEMS] -> [Pos] -> Result LocalEnv
ana_sort_gen sigma _si _pos =
  do let _pos' = if (null _pos) then emptyPos else (head _pos)
     (delta,delta') <- foldResult (sigma, sigma) ana_SIG_ITEMS (map item _si)
     checkSortsExist (getSign delta) _pos'
     let f = toEmAndPr delta' _pos'
     return delta' { getPsi = addNamedSentences (getPsi delta')
                              ((toGenItems f _pos):
                               (concat $ map opToApplSentence f)) }

------------------------------------------------------------------------------
-- BASIC-ITEMS
------------------------------------------------------------------------------

ana_BASIC_ITEMS :: LocalEnv -> Annoted BASIC_ITEMS -> Result LocalEnv
ana_BASIC_ITEMS sigma _itm =
  case (item _itm) of
    (Sig_items _s)              -> do (_res,_) <- ana_SIG_ITEMS (sigma,sigma)
                                                  _s
                                      return _res;
    (Free_datatype _l _p)       -> return sigma;
    (Sort_gen _s _p)            -> ana_sort_gen sigma _s _p;
    (Var_items _v _p)           -> ana_VAR_ITEMS sigma _v _p;
    (Local_var_axioms _v _f _p) -> ana_local_var_axioms sigma _v
                                   ((head _p):(take ((length _v)-1) _p))
                                   _f (drop (length _v) _p);
    (Axiom_items _f _p)         -> ana_axiom_items sigma _f _p

------------------------------------------------------------------------------
-- BASIC-SPEC
------------------------------------------------------------------------------

ana_BASIC_SPEC :: LocalEnv -> BASIC_SPEC -> Result LocalEnv
ana_BASIC_SPEC sigma (Basic_spec _l) = foldResult sigma ana_BASIC_ITEMS _l

basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos)
                 -> Result (Sign,Sign,[(String,Sentence)])
basicAnalysis (spec,sigma,ga) =
  do env <- ana_BASIC_SPEC
            (Env "unknown" ga sigma emptySentences emptyGlobal) spec
     let sigma' = getSign env
     let delta  = signDiff sigma sigma'
     return (delta,sigma',flattenSentences $ getPsi env)

------------------------------------------------------------------------------
--
--                             Static Analysis
--                         Signature computations
--
------------------------------------------------------------------------------

-- FIXME
--
signDiff :: Sign -> Sign -> Sign
signDiff a b = b

checkItem :: Sign -> (Id,SigItem) -> Bool
checkItem sigma (id,si) =
  let
    res   = lookupFM (getMap sigma) id
    items = if (isJust res) then
              fromJust res
            else
              []
  in
    si `elem` items

unfoldSigItems :: (Id, [SigItem]) -> [(Id, SigItem)]
unfoldSigItems (id,[])  = []
unfoldSigItems (id,h:t) = (id,h):(unfoldSigItems (id,t))

isSubSig :: Sign -> Sign -> Bool
isSubSig sub super =
  and $ map (checkItem super) $ concat $ map unfoldSigItems
      $ fmToList $ getMap sub

------------------------------------------------------------------------------
--
--                             Static Analysis
--                             Symbol functions
--
------------------------------------------------------------------------------

symbTypeToKind :: SymbType -> Kind
symbTypeToKind (OpAsItemType optype) = FunKind
symbTypeToKind (PredType predtype)   = PredKind
symbTypeToKind (Sign.Sort)           = SortKind

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw (Symbol id typ) = AKindedId (symbTypeToKind typ) id

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

sigItemToSymbol :: SigItem -> Symbol
sigItemToSymbol (ASortItem s) = Symbol (sortId $ item s) Sign.Sort
sigItemToSymbol (AnOpItem  o) = Symbol (opId $ item o)
                                       (OpAsItemType (opType $ item o))
sigItemToSymbol (APredItem p) = Symbol (predId $ item p)
                                       (PredType (predType $ item p))

symOf :: Sign -> Set Symbol
symOf sigma = mkSet $ map sigItemToSymbol $ concat $ eltsFM $ getMap sigma

idToSortSymbol :: Id -> Symbol
idToSortSymbol id = Symbol id Sign.Sort

idToOpSymbol :: Id -> OpType -> Symbol
idToOpSymbol id typ = Symbol id (OpAsItemType typ)

idToPredSymbol :: Id -> PredType -> Symbol
idToPredSymbol id typ = Symbol id (PredType typ)

funMapEntryToSymbol :: Sign -> (Id,[(OpType,Id,Bool)]) -> [(Symbol,Symbol)]
funMapEntryToSymbol sigma (id,[]) = []
funMapEntryToSymbol sigma (id,(typ,newId,_):t) =
  let
    origType = opType $ item $ getOp sigma id
  in
    (idToOpSymbol id origType,idToOpSymbol newId typ):
    (funMapEntryToSymbol sigma (id,t)) 

predMapEntryToSymbol :: Sign -> (Id,[(PredType,Id)]) -> [(Symbol,Symbol)]
predMapEntryToSymbol sigma (id,[]) = []
predMapEntryToSymbol sigma (id,(typ,newId):t) =
  let
    origType = predType $ item $ getPred sigma id
  in
    (idToPredSymbol id origType,idToPredSymbol newId typ):
    (predMapEntryToSymbol sigma (id,t))

symmapOf :: Morphism -> EndoMap Symbol
symmapOf (Morphism src trg sorts funs preds) =
  let
    sortMap = listToFM $ zip (map idToSortSymbol $ keysFM sorts)
                             (map idToSortSymbol $ eltsFM sorts)
    funMap  = listToFM $ concat $ map (funMapEntryToSymbol src)
                                      (fmToList funs)
    predMap = listToFM $ concat $ map (predMapEntryToSymbol src)
                                      (fmToList preds)
  in
    foldl plusFM emptyFM [sortMap,funMap,predMap]

matches :: Symbol -> RawSymbol -> Bool
matches x                            (ASymbol y)             =  x==y
matches (Symbol id _)                (AnID di)               = id==di
matches (Symbol id Sign.Sort)        (AKindedId SortKind di) = id==di
matches (Symbol id (OpAsItemType _)) (AKindedId FunKind di)  = id==di
matches (Symbol id (PredType _))     (AKindedId PredKind di) = id==di
matches _                            _                       = False

symName :: Symbol -> Id
symName (Symbol id _) = id

statSymbMapItems :: SYMB_MAP_ITEMS -> Result (EndoMap RawSymbol)
statSymbMapItems (Symb_map_items kind l _) =
  return (listToFM $ map (symbOrMapToRaw kind) l)
  
symbOrMapToRaw :: SYMB_KIND -> SYMB_OR_MAP -> (RawSymbol,RawSymbol)
symbOrMapToRaw k (Symb s) = (symbToRaw k s,symbToRaw k s)
symbOrMapToRaw k (Symb_map s t _) = (symbToRaw k s,symbToRaw k t)

statSymbItems :: SYMB_ITEMS -> Result [RawSymbol]
statSymbItems (Symb_items kind l _) =
  return (map (symbToRaw kind) l)

symbToRaw :: SYMB_KIND -> SYMB -> RawSymbol
symbToRaw k (Symb_id id)       = symbKindToRaw k id
symbToRaw k (Qual_id id typ _) = symbKindToRaw k id

symbKindToRaw :: SYMB_KIND -> Id -> RawSymbol
symbKindToRaw Implicit     id = AnID id
symbKindToRaw (Sorts_kind) id = AKindedId SortKind id
symbKindToRaw (Ops_kind)   id = AKindedId FunKind  id
symbKindToRaw (Preds_kind) id = AKindedId PredKind id

typeToRaw :: SYMB_KIND -> TYPE -> Id -> RawSymbol
typeToRaw k (O_type _) id = AKindedId FunKind  id
typeToRaw k (P_type _) id = AKindedId PredKind id
typeToRaw k (A_type _) id = symbKindToRaw k id

------------------------------------------------------------------------------
-- THE END
------------------------------------------------------------------------------
