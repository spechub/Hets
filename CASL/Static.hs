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

  datatypes

  Speicherzugriffsfehler bei Analyse von

  sort Nat 
  preds  even: Nat

  deshalb gibt basic_analysis erstmal nur triviale Werte zurück
-------------------------------------------------------------------------- -}

-----------------------------------------------------------------------------
-- Export declarations
-----------------------------------------------------------------------------

module CASL.Static {-( basicAnalysis, statSymbMapItems, statSymbItems,
                symbolToRaw, idToRaw, symOf, symmapOf, matches,
                isSubSig, symName )-} where

------------------------------------------------------------------------------
-- Imports from other modules
------------------------------------------------------------------------------

import Data.Maybe
import Control.Monad(foldM) -- instead of foldResult
import Common.Lib.Map hiding (map, filter)
import Prelude hiding (lookup)
import qualified Common.Lib.Set as Set
import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.GlobalAnnotationsFunctions
import CASL.AS_Basic_CASL
import CASL.Sign
import Common.Result
import CASL.Latin
import Common.Utils
import Logic.Logic ( EndoMap )

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
	      deriving Show

data SigLocalEnv = SigEnv { localEnv  :: LocalEnv,
                            selectors :: [Annoted OpItem],
                            w         :: Map Symbol [Symbol],
                            flag      :: Bool }

data Annotations = Annotations { annosOptPos :: [Pos],
                                 annosLeft, annosRight :: [Annotation] }

type ExtPos = (Pos, TokenKind)

------------------------------------------------------------------------------
--
--                              Helper functions
--
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- helper functions on datatypes
------------------------------------------------------------------------------

toAnnotations :: Annoted a -> Annotations
toAnnotations a = Annotations (opt_pos a) (l_annos a) (r_annos a)

toAnnoted :: a ->Annotations -> Annoted a
toAnnoted a (Annotations x y z) = Annoted a x y z

toSigLocalEnv :: LocalEnv -> SigLocalEnv
toSigLocalEnv env = SigEnv env [] empty False

emptyGlobal :: GlobalVars
emptyGlobal = Global []

emptySentences :: Sentences
emptySentences = Sentences []

emptyLocalEnv :: LocalEnv
emptyLocalEnv =
  Env "empty" emptyGlobalAnnos emptySign emptySentences emptyGlobal

emptyExtPos :: ExtPos
emptyExtPos = (nullPos, Key)

emptyAnnotations :: Annotations
emptyAnnotations = Annotations [] [] []

flattenSentences :: Sentences -> [(String, Sentence)]
flattenSentences sens = map (\x -> (senName x,sentence x)) (sentences sens)

addNamedSentences :: Sentences -> [NamedSentence] -> Sentences
addNamedSentences (Sentences s) l = Sentences (setAdd s l)

myShowList :: Show a => [a] -> String
myShowList []    = "[]"
myShowList [h]   = "'" ++ show h ++ "'"
myShowList (h:t) = "'" ++ (show h) ++ "', " ++ (myShowList t)

emptyFilename :: Filename
emptyFilename = ""

cloneAnnos :: Annoted a -> b -> Annoted b
cloneAnnos a b = a { item = b }

labelAnno :: String -> b -> Annoted b
labelAnno name itm = Annoted itm [] [] [Label [name] []]

noAnnos :: a -> Annoted a
noAnnos itm = toAnnoted itm emptyAnnotations

emptyAnnos :: Annoted ()
emptyAnnos = noAnnos ()

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
toExtPos pref p f = let
                      tokens = (zip p (f p))
                    in
                      case pref of Nothing -> tokens;
                                   Just ep -> ep:tokens

tokPos_sort_decl :: [Pos] -> [TokenKind]
tokPos_sort_decl l = replicate (length l) Comma

tokPos_subsort_decl :: [Pos] -> [TokenKind]
tokPos_subsort_decl []    = []
tokPos_subsort_decl (_:t) = (replicate (length t) Comma) ++ [Less]

tokPos_subsort_defn :: [Pos] -> [TokenKind]
tokPos_subsort_defn _ = [Equal,Key,Colon,Comma,Key]

tokPos_iso_decl :: [Pos] -> [TokenKind]
tokPos_iso_decl l = replicate (length l) Colon

tokPos_SORT_ITEM :: [Pos] -> [TokenKind]
tokPos_SORT_ITEM []    = []
tokPos_SORT_ITEM (_:t) = Key:(replicate (length t) Semi)

tokPos_pred_decl :: [Pos] -> [TokenKind]
tokPos_pred_decl []    = []
tokPos_pred_decl (_:t) = (replicate (length t) Comma) ++ [Colon]

tokPos_VAR_DECL :: [Pos] -> [TokenKind]
tokPos_VAR_DECL = tokPos_pred_decl

tokPos_pred_defn :: [Pos] -> [TokenKind]
tokPos_pred_defn _ = [Key]

tokPos_ARG_DECL :: [Pos] -> [TokenKind]
tokPos_ARG_DECL = tokPos_pred_decl

tokPos_ARG_DECL_list :: [Pos] -> [TokenKind]
tokPos_ARG_DECL_list []        = []
tokPos_ARG_DECL_list [_]       = []
tokPos_ARG_DECL_list (_:(_:t)) = (Key:(replicate (length t) Semi)) ++ [Key]

tokPos_PRED_ITEM :: [Pos] -> [TokenKind]
tokPos_PRED_ITEM = tokPos_SORT_ITEM

tokPos_VAR_ITEM :: [Pos] -> [TokenKind]
tokPos_VAR_ITEM = tokPos_SORT_ITEM

tokPos_local_var_axioms :: [Pos] -> [TokenKind]
tokPos_local_var_axioms []    = []
tokPos_local_var_axioms (_:t) = Key:(replicate (length t) Key)

tokPos_axiom_items :: [Pos] -> [TokenKind]
tokPos_axiom_items = tokPos_local_var_axioms

tokPos_select :: [Pos] -> [TokenKind]
tokPos_select = tokPos_pred_decl

tokPos_construct :: [Pos] -> [TokenKind]
tokPos_construct = tokPos_SORT_ITEM

tokPos_subsorts :: [Pos] -> [TokenKind]
tokPos_subsorts [] = []
tokPos_subsorts (_:t) = Key:(replicate (length t) Comma)

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
    labels = filter (\y -> case y of (Label _ _) -> True;
                                               _ -> False)
                    ((l_annos x)++(r_annos x))
  in
    case labels of ((Label s _):_) -> concat s;
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

fromItemPos :: ItemPos -> ExtPos
fromItemPos (ItemPos _ kind []) = (nullPos,kind)
fromItemPos (ItemPos _ kind l)  = (head l,kind)

toVarDecl :: SortId -> ExtPos -> VAR -> VarDecl
toVarDecl sort pos var = VarDecl var sort (toListPos pos)

toVarDecls :: SortId -> [ExtPos] -> [VAR] -> [VarDecl]
toVarDecls sort p v = map (uncurry (toVarDecl sort))
                          (zip (extendList emptyExtPos v p) v)

typeToVarDecl :: OpType -> [VarDecl]
typeToVarDecl t = map (\(s,v) -> VarDecl v s (ListPos Key nullPos))
                  $ zip (opArgs t) $ map mkSimpleId $ map (\x -> "x" ++ x)
                  $ map show $ [1..(length $ opArgs t)]

toVarId :: VarDecl -> Term
toVarId v = VarId (simpleIdToId $ varId v) (varSort v) Inferred []

opToApplSentence :: OpItem -> [NamedSentence]
opToApplSentence itm =
  let
    name   = case (opId itm) of Id [Token n _] [] [] -> n;
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
sortToSymbol s = Symbol s CASL.Sign.Sort

opTypeIdToSymbol :: OpType -> Id -> Symbol
opTypeIdToSymbol typ idt = Symbol idt (OpAsItemType typ)

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
foldTwo state def f a b = foldM (\st (x, y) -> f st x y) state
                                     (zip a (extendList def a b))

foldlTwo :: c -> (a -> b -> c -> a) -> a -> [b] -> [c] -> a
foldlTwo def f ini a b = foldl (\st (x, y) -> f st x y) ini
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
hasElem sigma f idt =
  let
    res = lookup idt (getMap sigma)
  in
    if (isJust res) then
      or $ map (f idt) (fromJust res)
    else
      False

getElem :: Sign -> (Id -> SigItem -> Bool) -> Id -> Maybe SigItem
getElem sigma f idt =
  if (hasElem sigma f idt) then
    Just (head $ filter (f idt) $ fromJust $ lookup idt $ getMap sigma)
  else
    Nothing

isSigSortItem :: Id -> SigItem -> Bool
isSigSortItem idt (ASortItem s) = (sortId $ item s)==idt
isSigSortItem _ _ = False

isSigOpItem :: Id -> SigItem -> Bool
isSigOpItem idt (AnOpItem o) = (opId $ item o)==idt
isSigOpItem _ _ = False

isSigPredItem :: Id -> SigItem -> Bool
isSigPredItem idt (APredItem p) = (predId $ item p)==idt
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
hasSort sigma idt = hasElem sigma isSigSortItem idt

hasOp :: Sign -> Id -> Bool
hasOp sigma idt = hasElem sigma isSigOpItem idt

hasPred :: Sign -> Id -> Bool
hasPred sigma idt = hasElem sigma isSigPredItem idt

lookupSort :: Sign -> SortId -> Maybe (Annoted SortItem)
lookupSort sigma idt = toSortItem $ getElem sigma isSigSortItem idt

lookupOp :: Sign -> Id -> Maybe (Annoted OpItem)
lookupOp sigma idt = toOpItem $ getElem sigma isSigOpItem idt

lookupPred :: Sign -> Id -> Maybe (Annoted PredItem)
lookupPred sigma idt = toPredItem $ getElem sigma isSigPredItem idt

getSort :: Sign -> SortId -> Annoted SortItem
getSort sigma idt = fromJust $ lookupSort sigma idt

getOp :: Sign -> Id -> Annoted OpItem
getOp sigma idt = fromJust $ lookupOp sigma idt

getPred :: Sign -> Id -> Annoted PredItem
getPred sigma idt = fromJust $ lookupPred sigma idt

------------------------------------------------------------------------------
-- update function for SigItem in Sign
------------------------------------------------------------------------------

updateSigItem :: Sign -> Id -> SigItem -> Sign
updateSigItem sigma idt itm =
  let
    res = lookup idt $ getMap sigma
    new = if (isNothing res) then
            [itm]
          else
             [ x | x<-(fromJust res), x /= itm ] ++ [itm]
  in
    sigma { getMap = insert idt new (getMap sigma)}

------------------------------------------------------------------------------
-- functions for SortItem generation and modification
------------------------------------------------------------------------------

addSuper :: SortRels -> Bool -> [SortId] -> SortRels
addSuper rels _      []         = rels
addSuper rels direct (idt:allid) =
  if direct then
    rels { supersorts   = setAddOne (supersorts rels) idt,
           allsupersrts = setAdd  (allsupersrts rels) (idt:allid) }
  else
    rels { allsupersrts = setAdd (allsupersrts rels) (idt:allid) }

addSub :: SortRels -> Bool -> [SortId] -> SortRels
addSub rels _      []         = rels
addSub rels direct (idt:allid) =
  if direct then
    rels { subsorts   = setAddOne (subsorts rels) idt,
           allsubsrts = setAdd  (allsubsrts rels) (idt:allid) }
  else
    rels { allsubsrts = setAdd (allsubsrts rels) (idt:allid) }

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
addIsoSubsorting sorts sigma sort =
  let
    others = [ x | x<-sorts, x/=sort ]
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
updateSortItem name ann defn sigma idt kwpos =
  let
    res = lookupSort sigma idt
    pos = toItemPos name kwpos
    new = if (isJust res) then
            let
              itm = fromJust res
              old = item itm
            in
              mergeAnnos itm (cloneAnnos ann
              old { sortDef  = case defn of Nothing -> sortDef old;
                                                  x -> x,
                    sortPos  = pos,
                    altSorts = (altSorts old) ++ [sortPos old] })
          else
            cloneAnnos ann (SortItem idt emptySortRels defn pos [])
  in
    updateSigItem sigma idt (ASortItem new)

updateSortDefn :: Sign -> SortId -> Maybe SortDefn -> Sign
updateSortDefn sigma idt defn =
  let
    res = getSort sigma idt
    new = res { item = (item res) { sortDef = defn } }
  in
    updateSigItem sigma idt (ASortItem new) 

------------------------------------------------------------------------------
-- PredItem generation
------------------------------------------------------------------------------

updatePredItem :: Filename -> Annoted PRED_ITEM -> PredType -> Maybe PredDefn
                  -> Sign -> Id -> ExtPos -> Sign
updatePredItem name ann typ defn sigma idt pos =
  let
    res  = lookupPred sigma idt
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
             cloneAnnos ann (PredItem idt typ defn ppos [])
  in
    updateSigItem sigma idt (APredItem new)

updatePredDefn :: Sign -> Id -> Maybe PredDefn -> Sign
updatePredDefn sigma idt defn =
  let
    res = getPred sigma idt
    new = res { item = (item res) { predDefn = defn } }
  in
    updateSigItem sigma idt (APredItem new) 

------------------------------------------------------------------------------
-- OpItem generation
------------------------------------------------------------------------------

updateOpItem :: Filename -> Annoted a -> OpType -> Maybe OpDefn -> [OpAttr]
                -> Sign -> Id -> ExtPos -> Sign
updateOpItem name ann typ defn attr sigma idt pos =
  let
    res  = lookupOp sigma idt
    opos = toItemPos name pos
    new  = if (isJust res) then
             let
               old = fromJust res
               itm = item old
             in
               mergeAnnos old (cloneAnnos ann
               itm { opDefn  = case defn of Nothing -> opDefn itm;
                                                  x -> x,
                     opAttrs = setAdd (opAttrs itm) attr,
                     opPos   = opos,
                     altOps  = (altOps itm) ++ [opPos itm] })
           else
             cloneAnnos ann (OpItem idt typ attr defn opos [])
  in
    updateSigItem sigma idt (AnOpItem new)

updateOpItems :: Filename -> Sign -> [Annoted OpItem] -> Sign
updateOpItems _ sigma [] = sigma
updateOpItems fn sigma
              (ann@(Annoted (OpItem idt typ attr defn pos _) _ _ _):t) =
  updateOpItems fn (updateOpItem fn ann typ defn attr sigma idt
                    (fromItemPos pos)) t

mergeOpDefn :: Maybe OpDefn -> OpDefn -> OpDefn
mergeOpDefn Nothing  x = x
mergeOpDefn (Just y) x =
  case x of OpDef _ _ _ -> x;
            Constr _    -> x;
            Select l1 s -> (case y of Select l2 _ -> Select (setAdd l1 l2) s;
                                                _ -> x)

updateOpDefn :: Sign -> Id -> OpDefn -> Sign
updateOpDefn sigma idt defn =
  let
    res = getOp sigma idt
    new = res { item = (item res) { opDefn = Just (mergeOpDefn
                                    (opDefn $ item res) defn) } }
  in
    updateSigItem sigma idt (AnOpItem new) 
                                  
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
ana_FORMULA _ f = return (cloneAnnoFormula f (TrueAtom []))

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
     let _delta   = foldPos (updateSortItem (getName sigma) _itm _defn)
                            (getSign sigma) (s:s_n) _pos
     let embedRel = foldl (addSubsort s) _delta s_n
     return sigma { getSign = embedRel }

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
     let _delta   = foldPos (updateSortItem (getName sigma) _itm Nothing)
                            (getSign sigma) s_n _pos
     let embedRel = foldl (addIsoSubsorting s_n) _delta s_n
     return sigma { getSign = embedRel }

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
ana_PRED_TYPE' _ w' (Pred_type [] _) _pos = return w'
ana_PRED_TYPE' sigma w' (Pred_type (s_n:_t) _) _pos =
  do checkSortExists sigma (fst _pos) s_n
     ana_PRED_TYPE' sigma (w'++[s_n]) (Pred_type _t []) _pos

ana_PRED_TYPE :: LocalEnv -> PRED_TYPE -> ExtPos -> Result PredType
ana_PRED_TYPE sigma _t _pos = ana_PRED_TYPE' sigma [] _t _pos

ana_pred_decl :: LocalEnv -> Annoted PRED_ITEM -> [PRED_NAME] -> PRED_TYPE
                 -> [ExtPos] -> Result LocalEnv
ana_pred_decl sigma _itm p_n _t _pos =
  do w' <- ana_PRED_TYPE sigma _t (head _pos)
     let delta = foldPos (updatePredItem (getName sigma) _itm w' Nothing)
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
ana_ARG_DECL_list' _ (x_s_n,w') [] = return (x_s_n,w')
ana_ARG_DECL_list' sigma (x_s_n,w') ((Arg_decl _v _s _pos):_t) =
  do let _extPos = zip _pos (tokPos_ARG_DECL _pos)
     (x_n,s) <- ana_ARG_DECL sigma _v _s _extPos
     let _qual = toVarDecls s _extPos x_n
     checkQualVarsUnique (head _pos) x_s_n _qual
     ana_ARG_DECL_list' sigma (x_s_n ++ _qual,w' ++ [s]) _t

ana_ARG_DECL_list :: LocalEnv -> [ARG_DECL] -> Result ([VarDecl],[SortId])
ana_ARG_DECL_list sigma _ad = ana_ARG_DECL_list' sigma ([],[]) _ad

ana_pred_defn :: LocalEnv -> Annoted PRED_ITEM -> PRED_NAME -> PRED_HEAD
                 -> Annoted FORMULA -> [ExtPos] -> Result LocalEnv
ana_pred_defn sigma _ann p (Pred_head _ad _pos') _f _pos =
  do (_x_s_n,w') <- ana_ARG_DECL_list sigma _ad
     let _delta' = updatePredItem (getName sigma) _ann w' Nothing
                                  (getSign sigma) p (head _pos)
     phi        <- ana_no_anno_FORMULA (sigma { getSign = _delta',
                                        getGlobal = Global _x_s_n }) _f
     let _defn   = PredDef _x_s_n phi (_pos' ++ [(fst $ last _pos)])
     let delta   = updatePredDefn _delta' p (Just _defn)
     return sigma { getSign = delta,
                    getPsi   = addNamedSentences (getPsi sigma)
                               [toNamedSentence [] (someLabel
                               (predDefnLabel p (_x_s_n)) _f)
                               (cloneAnnos _f (Quantified Forall _x_s_n
                               (Connect EquivOp [PredAppl p w'
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

sig_COMPONENTS :: COMPONENTS -> [SortId]
sig_COMPONENTS (Total_select   f_n s' _) = replicate (length f_n) s'
sig_COMPONENTS (Partial_select f_n s' _) = replicate (length f_n) s'
sig_COMPONENTS (CASL.AS_Basic_CASL.Sort s'  ) = [s']

sig_COMPONENTS_list :: [COMPONENTS] -> [SortId]
sig_COMPONENTS_list l = concat $ map sig_COMPONENTS l

sig_ALTERNATIVE :: SortId -> Sign -> ALTERNATIVE -> Sign
sig_ALTERNATIVE s sigma (Total_construct f components_list _) =
  updateOpItem emptyFilename emptyAnnos
               (OpType Total (sig_COMPONENTS_list components_list) s)
               Nothing [] sigma f emptyExtPos
sig_ALTERNATIVE s sigma (Partial_construct f components_list _) =
  updateOpItem emptyFilename emptyAnnos
               (OpType Partial (sig_COMPONENTS_list components_list) s)
               Nothing [] sigma f emptyExtPos
sig_ALTERNATIVE _ sigma (Subsorts _ _) = sigma

sig_ALTERNATIVE_list :: Sign -> SortId -> [ALTERNATIVE] -> Sign
sig_ALTERNATIVE_list sigma s l = foldl (sig_ALTERNATIVE s) sigma l
                                       
sig_DATATYPE_DECL :: Sign -> DATATYPE_DECL -> Sign
sig_DATATYPE_DECL sigma (Datatype_decl s alternative_list _) =
  updateSortItem emptyFilename emptyAnnos Nothing
                 (sig_ALTERNATIVE_list sigma s (map item alternative_list))
                 s emptyExtPos

ana_select :: Annotations -> SortId -> Id -> OpType
              -> (SigLocalEnv, [Component]) -> [Id] -> SortId -> [Pos]
              -> FunKind -> ExtPos -> (SigLocalEnv, [Component])
ana_select ann s f ws (sigma,c) f_n s' pos kind top_pos =
  let
    optype = OpType kind [opRes ws] s'
  in
    (sigma { selectors = (selectors sigma) ++
                         (map (\(x,p) -> toAnnoted
                                         (OpItem x optype []
                                          (Just (Select [opTypeIdToSymbol ws f]
                                                 (idToSortSymbol s)))
                                          (toItemPos (getName $ localEnv sigma) p)
                                         []) ann)
                              (zip f_n (toExtPos Nothing pos
                                                 tokPos_select))) },
              c ++ (map (\x -> Component (Just x) optype
                                         (Just (toListPos top_pos))) f_n));

ana_COMPONENTS :: Annotations -> SortId -> Id -> OpType
                  -> (SigLocalEnv, [Component]) -> COMPONENTS -> ExtPos
                  -> Result (SigLocalEnv, [Component])
ana_COMPONENTS ann s f ws (sigma,c) components top_pos =
  return
   (case components of
      Total_select f_n s' pos
        -> ana_select ann s f ws (sigma,c) f_n s' pos Total top_pos
      Partial_select f_n s' pos
        -> ana_select ann s f ws (sigma,c) f_n s' pos Partial top_pos
      CASL.AS_Basic_CASL.Sort s'
        -> (sigma,c ++ [Component Nothing (OpType Total [s'] s)
                                  (Just (toListPos top_pos))]))

ana_subsort :: Annoted ALTERNATIVE -> (SigLocalEnv, [Annoted Alternative])
               -> SortId -> ExtPos
               -> Result (SigLocalEnv, [Annoted Alternative])
ana_subsort ann (sigma,alternatives) s_n pos =
  do checkSortExists (localEnv sigma) (fst pos) s_n
     return (sigma { flag = True },
             alternatives ++ [cloneAnnos ann (Subsort s_n (toListPos pos))])

ana_construct :: Annoted ALTERNATIVE
                 -> Sign -> SortId -> (SigLocalEnv, [Annoted Alternative])
                 -> Id -> [COMPONENTS] -> [Pos] -> ExtPos
                 -> Result (SigLocalEnv, [Annoted Alternative])
ana_construct ann sigma' s (sigma,alternatives) f components pos top_pos =
  let
    ws    = opType $ item $ getOp sigma' f
    annos = toAnnotations ann
  in
    do (delta,c) <- chainPos (sigma,[]) (ana_COMPONENTS annos s f ws)
                             components [top_pos] pos tokPos_construct
       return (delta { localEnv = (localEnv delta)
                     { getSign = updateOpItem (getName $ localEnv delta)
                                              ann ws
                                              (Just (Constr
                                                     (idToSortSymbol s)))
                                              []
                                              (getSign $ localEnv delta)
                                              f top_pos } },
               alternatives ++ [toAnnoted (Construct f ws c pos) annos])

ana_ALTERNATIVE :: Sign -> SortId -> (SigLocalEnv, [Annoted Alternative])
                   -> Annoted ALTERNATIVE -> ExtPos
                   -> Result (SigLocalEnv, [Annoted Alternative])
ana_ALTERNATIVE sigma' s (sigma,alternatives) alternative top_pos =
  case (item alternative) of
    Total_construct f components pos
     -> ana_construct alternative sigma' s (sigma,alternatives) f
                      components pos top_pos
    Partial_construct f components pos
     -> ana_construct alternative sigma' s (sigma,alternatives) f
                      components pos top_pos
    Subsorts sorts pos
     -> chainPos (sigma,alternatives) (ana_subsort alternative) sorts
                 [top_pos] pos tokPos_subsorts

ana_ALTERNATIVE_list :: Sign -> SortId -> SigLocalEnv -> [Annoted ALTERNATIVE]
                        -> ExtPos -> [Pos] ->
                        Result (SigLocalEnv, [Annoted Alternative])
ana_ALTERNATIVE_list sigma' s sigma alternative_list top_pos pos =
  chainPos (sigma,[]) (ana_ALTERNATIVE sigma' s) alternative_list [top_pos]
           pos tokPos_DATATYPE_DECL

ana_DATATYPE_DECL :: Sign -> SigLocalEnv -> Annoted DATATYPE_DECL
                     -> ExtPos -> Result SigLocalEnv
ana_DATATYPE_DECL sigma' sigma decl@(Annoted (Datatype_decl s alternative_list
                  pos) _ _ _) top_pos =
  do (delta,alternatives) <- ana_ALTERNATIVE_list sigma' s sigma
                                                  alternative_list top_pos pos
     let embedRel = mapMaybe (\x -> case x of Subsort sort _ -> Just sort;
                                                           _ -> Nothing)
                             (map item alternatives)
     let defn  = let
                   gen_items = concat $ map (\(x,y) -> x:y)
                                            (toList $ w delta)
                 in
                   Datatype alternatives Loose gen_items pos
     return delta { localEnv = (localEnv delta)
                  { getSign = foldl (addSubsort s)
                                    (updateSortItem (getName $ localEnv sigma)
                                                    decl (Just defn)
                                                    (getSign $ localEnv delta)
                                                    s top_pos)
                                    embedRel } }

ana_datatype_items :: SigLocalEnv -> [Annoted DATATYPE_DECL] -> [Pos] ->
                      Result SigLocalEnv
ana_datatype_items sigma datatype_decl_list pos =
  let
    sigma' = foldl sig_DATATYPE_DECL (getSign $ localEnv sigma)
                   (map item datatype_decl_list)
  in
    chainPos sigma (ana_DATATYPE_DECL sigma') datatype_decl_list [] pos
             tokPos_datatype_items

------------------------------------------------------------------------------
-- SIG-ITEMS
------------------------------------------------------------------------------

ana_SIG_ITEMS :: SigLocalEnv -> SIG_ITEMS -> Result SigLocalEnv
ana_SIG_ITEMS sigma (Sort_items sort_items loc_pos) =
  chainPos (localEnv sigma) ana_SORT_ITEM sort_items [] loc_pos
           tokPos_SORT_ITEM >>= return . toSigLocalEnv
ana_SIG_ITEMS sigma (Op_items op_items loc_pos) =
  chainPos (localEnv sigma) ana_OP_ITEM op_items [] loc_pos
           tokPos_OP_ITEM >>= return . toSigLocalEnv
ana_SIG_ITEMS sigma (Pred_items pred_items loc_pos) =
  chainPos (localEnv sigma) ana_PRED_ITEM pred_items [] loc_pos
           tokPos_PRED_ITEM >>= return . toSigLocalEnv
ana_SIG_ITEMS sigma (Datatype_items datatype_items loc_pos) =
  ana_datatype_items sigma datatype_items loc_pos

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
                    (concat $ map snd $ toList $ getMap sigma)
  in 
    if (null _sorts) then
      fatal_error "sort-gen did not declare any sorts" _pos
    else
      return ()

ana_sort_gen :: LocalEnv -> [Annoted SIG_ITEMS] -> [Pos] -> Result LocalEnv
ana_sort_gen sigma _si _pos =
  return sigma

------------------------------------------------------------------------------
-- BASIC-ITEMS
------------------------------------------------------------------------------

ana_BASIC_ITEMS :: LocalEnv -> Annoted BASIC_ITEMS -> Result LocalEnv
ana_BASIC_ITEMS sigma _itm =
  case (item _itm) of
    (Sig_items sig_items )
      -> do sigma' <- ana_SIG_ITEMS (toSigLocalEnv sigma) sig_items
            return (localEnv sigma')
                    { getSign = updateOpItems (getName $ localEnv sigma')
                                              (getSign $ localEnv sigma')
                                              (selectors sigma') }
    (Free_datatype _free_types _pos)
      -> return sigma;
    (Sort_gen sig_items pos)
      -> ana_sort_gen sigma sig_items pos;
    (Var_items var_items pos)
      -> ana_VAR_ITEMS sigma var_items pos;
    (Local_var_axioms vars formulas pos)
      -> ana_local_var_axioms sigma vars ((head pos):
                                          (take ((length vars)-1) pos))
                              formulas (drop (length vars) pos);
    (Axiom_items formulas pos)
      -> ana_axiom_items sigma formulas pos

------------------------------------------------------------------------------
-- BASIC-SPEC
------------------------------------------------------------------------------

ana_BASIC_SPEC :: LocalEnv -> BASIC_SPEC -> Result LocalEnv
ana_BASIC_SPEC sigma (Basic_spec l) = foldM ana_BASIC_ITEMS sigma l

basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos)
                 -> Result (Sign,Sign,[(String,Sentence)])
basicAnalysis (spec,sigma,ga) = -- return(emptySign,emptySign,[])
  do env <- ana_BASIC_SPEC
            (Env "unknown" ga sigma emptySentences emptyGlobal) spec
     let sigma' = getSign env
     let delta  = signDiff sigma' sigma
     return (sigma', delta,flattenSentences $ getPsi env)

------------------------------------------------------------------------------
--
--                             Static Analysis
--                         Signature computations
--
------------------------------------------------------------------------------

-- FIXME
--
signDiff :: Sign -> Sign -> Sign
signDiff a b = emptySign {getMap = difference (getMap a) (getMap b)}

checkItem :: Sign -> (Id,SigItem) -> Bool
checkItem sigma (idt,si) =
  let
    res   = lookup idt $ getMap sigma
    items = if (isJust res) then
              fromJust res
            else
              []
  in
    si `elem` items

unfoldSigItems :: (Id, [SigItem]) -> [(Id, SigItem)]
unfoldSigItems (_,[])    = []
unfoldSigItems (idt,h:t) = (idt,h):(unfoldSigItems (idt,t))

isSubSig :: Sign -> Sign -> Bool
isSubSig sub super =
  and $ map (checkItem super) $ concat $ map unfoldSigItems
      $ toList $ getMap sub

------------------------------------------------------------------------------
--
--                             Static Analysis
--                             Symbol functions
--
------------------------------------------------------------------------------

symbTypeToKind :: SymbType -> Kind
symbTypeToKind (OpAsItemType _) = FunKind
symbTypeToKind (PredType _)     = PredKind
symbTypeToKind (CASL.Sign.Sort)      = SortKind

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw (Symbol idt typ) = AKindedId (symbTypeToKind typ) idt

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

sigItemToSymbol :: SigItem -> Symbol
sigItemToSymbol (ASortItem s) = Symbol (sortId $ item s) CASL.Sign.Sort
sigItemToSymbol (AnOpItem  o) = Symbol (opId $ item o)
                                       (OpAsItemType (opType $ item o))
sigItemToSymbol (APredItem p) = Symbol (predId $ item p)
                                       (PredType (predType $ item p))

symOf :: Sign -> Set.Set Symbol
symOf sigma = Set.fromList $ map sigItemToSymbol 
	      $ concat $ elems $ getMap sigma

idToSortSymbol :: Id -> Symbol
idToSortSymbol idt = Symbol idt CASL.Sign.Sort

idToOpSymbol :: Id -> OpType -> Symbol
idToOpSymbol idt typ = Symbol idt (OpAsItemType typ)

idToPredSymbol :: Id -> PredType -> Symbol
idToPredSymbol idt typ = Symbol idt (PredType typ)

funMapEntryToSymbol :: Sign -> (Id,[(OpType,Id,Bool)]) -> [(Symbol,Symbol)]
funMapEntryToSymbol _ (_,[]) = []
funMapEntryToSymbol sigma (idt,(typ,newId,_):t) =
  let
    origType = opType $ item $ getOp sigma idt
  in
    (idToOpSymbol idt origType,idToOpSymbol newId typ):
    (funMapEntryToSymbol sigma (idt,t)) 

predMapEntryToSymbol :: Sign -> (Id,[(PredType,Id)]) -> [(Symbol,Symbol)]
predMapEntryToSymbol _ (_,[]) = []
predMapEntryToSymbol sigma (idt,(typ,newId):t) =
  let
    origType = predType $ item $ getPred sigma idt
  in
    (idToPredSymbol idt origType,idToPredSymbol newId typ):
    (predMapEntryToSymbol sigma (idt,t))

symmapOf :: Morphism -> EndoMap Symbol
symmapOf (Morphism src _ sorts funs preds) =
  let
    sortMap = fromList $ zip (map idToSortSymbol $ keys sorts)
                             (map idToSortSymbol $ elems sorts)
    funMap  = fromList $ concat $ map (funMapEntryToSymbol src)
                                      (toList funs)
    predMap = fromList $ concat $ map (predMapEntryToSymbol src)
                                      (toList preds)
  in
    foldl union empty [sortMap,funMap,predMap]

matches :: Symbol -> RawSymbol -> Bool
matches x                            (ASymbol y)              =  x==y
matches (Symbol idt _)                (AnID di)               = idt==di
matches (Symbol idt CASL.Sign.Sort)        (AKindedId SortKind di) = idt==di
matches (Symbol idt (OpAsItemType _)) (AKindedId FunKind di)  = idt==di
matches (Symbol idt (PredType _))     (AKindedId PredKind di) = idt==di
matches _                            _                        = False

symName :: Symbol -> Id
symName (Symbol idt _) = idt

statSymbMapItems :: [SYMB_MAP_ITEMS] -> Result (EndoMap RawSymbol)
statSymbMapItems sl =  return (fromList $ concat $ map s1 sl)
  where
  s1 (Symb_map_items kind l _) = map (symbOrMapToRaw kind) l
 
  
symbOrMapToRaw :: SYMB_KIND -> SYMB_OR_MAP -> (RawSymbol,RawSymbol)
symbOrMapToRaw k (Symb s) = (symbToRaw k s,symbToRaw k s)
symbOrMapToRaw k (Symb_map s t _) = (symbToRaw k s,symbToRaw k t)

statSymbItems :: [SYMB_ITEMS] -> Result [RawSymbol]
statSymbItems sl = 
  return (concat (map s1 sl))
  where s1 (Symb_items kind l _) = map (symbToRaw kind) l

symbToRaw :: SYMB_KIND -> SYMB -> RawSymbol
symbToRaw k (Symb_id idt)     = symbKindToRaw k idt
symbToRaw k (Qual_id idt _ _) = symbKindToRaw k idt

symbKindToRaw :: SYMB_KIND -> Id -> RawSymbol
symbKindToRaw Implicit     idt = AnID idt
symbKindToRaw (Sorts_kind) idt = AKindedId SortKind idt
symbKindToRaw (Ops_kind)   idt = AKindedId FunKind  idt
symbKindToRaw (Preds_kind) idt = AKindedId PredKind idt

typeToRaw :: SYMB_KIND -> TYPE -> Id -> RawSymbol
typeToRaw _ (O_type _) idt = AKindedId FunKind  idt
typeToRaw _ (P_type _) idt = AKindedId PredKind idt
typeToRaw k (A_type _) idt = symbKindToRaw k idt

------------------------------------------------------------------------------
-- THE END
------------------------------------------------------------------------------
