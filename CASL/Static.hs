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

module Static where

------------------------------------------------------------------------------
-- Imports from other modules
------------------------------------------------------------------------------

import Maybe
import FiniteMap
import Id
import AS_Annotation
import AS_Basic_CASL
import Sign

------------------------------------------------------------------------------
-- types
------------------------------------------------------------------------------

type Err = ([String],Bool)

------------------------------------------------------------------------------
-- Functions on signature element
------------------------------------------------------------------------------

newRels :: SortRels
newRels = SortRels [] [] [] []

isUnique :: Eq a => [a] -> Bool
isUnique [] = False
isUnique [h] = True
isUnique (h:t) = ([ x | x<-t, x == h ]==[]) && isUnique t

illArg :: Pos -> String -> String -> Maybe Err
illArg p s c = mkErr True p ("illegal argument passed to function " ++ s
                             ++ " (constructor " ++ c ++ ")")

mkErr :: Bool -> Pos -> String -> Maybe Err
mkErr fatal (l,c) s = Just ([  (if fatal then "error" else "warning") ++
                              "(" ++ (show l) ++ "," ++ (show c) ++ "): "
                              ++ s ], fatal )

-- add error strings in chronological order
-- propagate fatal errors
--
addFromMaybe :: Maybe Err -> Maybe Err -> Maybe Err
addFromMaybe Nothing  Nothing          = Nothing
addFromMaybe Nothing  e                = e
addFromMaybe e        Nothing          = e
addFromMaybe (Just (a,x)) (Just (b,y)) = Just (a ++ b, x || y)

getTokenKind :: String -> TokenKind
getTokenKind s =      if (s==",") then Comma
                 else if (s==";") then Semi
                 else if (s=="<") then Less
                 else if (s=="=") then Equal
                 else if (s==":") then Colon
                 else Key 

getMap :: Sign -> FiniteMap Id [SigItem]
getMap (SignAsMap m _) = m

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
  let
    res = lookupFM (getMap sigma) id
  in
    if (hasElem sigma f id) then
      Just (head $ filter (f id) $ fromJust $ lookupFM (getMap sigma) id)
    else
      Nothing

hasSigSortItem :: Id -> SigItem -> Bool
hasSigSortItem id (ASortItem s) = (sortId $ item s)==id
hasSigSortItem _ _ = False

fromSigSortItem :: Maybe SigItem -> Maybe (Annoted SortItem)
fromSigSortItem (Just (ASortItem s)) = Just s
fromSigSortItem _ = Nothing

hasSort :: Sign -> SortId -> Bool
hasSort sigma id = hasElem sigma hasSigSortItem id

getSort :: Sign -> SortId -> Maybe SigItem
getSort sigma id = getElem sigma hasSigSortItem id

hasSigOpItem :: Id -> SigItem -> Bool
hasSigOpItem id (AnOpItem o) = (opId $ item o)==id
hasSigOpItem _ _ = False

hasOp :: Sign -> Id -> Bool
hasOp sigma id = hasElem sigma hasSigOpItem id

getOp :: Sign -> Id -> Maybe SigItem
getOp sigma id = getElem sigma hasSigOpItem id

hasSigPredItem :: Id -> SigItem -> Bool
hasSigPredItem id (APredItem p) = (predId $ item p)==id
hasSigPredItem _ _ = False

hasPred :: Sign -> Id -> Bool
hasPred sigma id = hasElem sigma hasSigPredItem id

getPred :: Sign -> Id -> Maybe SigItem
getPred sigma id = getElem sigma hasSigPredItem id

copyAnnoted :: Annoted a -> b -> Annoted b
copyAnnoted a b = Annoted b (opt_pos a) (l_annos a) (r_annos a)

mergeAnnoted :: Annoted a -> Annoted b -> Annoted b
mergeAnnoted a b = b { opt_pos = (opt_pos a) ++ (opt_pos b),
                       l_annos = (l_annos a) ++ (l_annos b),
                       r_annos = (r_annos a) ++ (r_annos b) }

addSuper :: SortRels -> Maybe SortId -> SortRels
addSuper x Nothing = x
addSuper x (Just id) = x { supersorts = relAdd (supersorts x) [id],
                           allsupersrts = relAdd (allsupersrts x) [id] }

addSortItem :: Annoted a -> Sign -> SortId -> Maybe SortId -> Maybe SortDefn
               -> Pos -> String -> Sign
addSortItem ann sigma id super defn kwpos kw =
  let
    res = fromSigSortItem $ getSort sigma id
    pos = ItemPos kw (getTokenKind kw) [kwpos]
  in
    if (isJust res) then
      let
        itm = fromJust res
        old = item itm
        new = old { sortDef = if (isJust defn) then defn else (sortDef old),
                    sortPos = pos,
                    sortRels = addSuper (sortRels old) super,
                    altSorts = (altSorts old) ++ [sortPos old] }
      in
        updateSigItem sigma id (ASortItem (copyAnnoted ann new))
    else
      let
        new = SortItem id (addSuper newRels super) defn pos []
      in
        updateSigItem sigma id (ASortItem (copyAnnoted ann new))

updateSigItem :: Sign -> Id -> SigItem -> Sign
updateSigItem (SignAsMap m g) id itm =
  let
    res = lookupFM m id
  in
    if (isNothing res) then
      SignAsMap (addToFM m id [itm]) g
    else
      let
        lst = fromJust res
        new = [ x | x<-lst, x /= itm ] ++ [itm]
      in
        SignAsMap (addToFM m id new) g

addSubSort :: Bool -> SortId -> Sign -> SortId -> Sign
addSubSort direct sub sigma super =
  let
    res = fromJust $ fromSigSortItem $ getSort sigma super
    ol  = item res
    old = sortRels ol
    new = if (direct) then
            old { subsorts = relAdd (subsorts old) [sub],
                  allsubsrts = relAdd (allsubsrts old) [sub] }
          else
            old { allsubsrts = relAdd (allsubsrts old) [sub] }
    ne  = ol { sortRels = new }
    s'  = updateSigItem sigma super (ASortItem (res { item = ne }))
    s'' = chain s' (addSubSort False sub) (allsupersrts old)
  in
    chain s'' (addSuperSorts (allsupersrts old)) (allsubsrts old)
    
addSuperSorts :: [SortId] -> Sign -> SortId -> Sign
addSuperSorts supers sigma sub =
  let
    res = fromJust $ fromSigSortItem $ getSort sigma sub
    ol  = item res
    old = sortRels ol
    new = old { allsupersrts = relAdd (allsupersrts old) supers }
    ne  = ol { sortRels = new }
  in
    updateSigItem sigma sub (ASortItem (res { item = ne }))

chainPos' :: Sign -> (Sign -> a -> (Pos, String) -> (Maybe Sign, Maybe Err))
            -> [a] -> [(Pos,String)] -> Maybe Err -> (Maybe Sign, Maybe Err)
chainPos' sigma f [] [] e = (Just sigma, e)
chainPos' sigma f [] (h::t) e = (Just sigma, e) 
chainPos' sigma f (a:as) ((p,tok):ps) e =
  let
    (res,err) = f sigma a (p,tok)
    err_sum   = addFromMaybe err e
  in
    if (isJust res) then
      chainPos' (fromJust res) f as ps err_sum
    else
      (Nothing, err_sum)

-- given a signature, chain through a list of items taking care of
--   passing positions and tokens to subfunctions
-- arguments:
--  sigma: input signature
--      f: function to run on individual items
--    itm: list of items to traverse in order
--     ps: position and token list from higher level item if needed
--    pos: position list that comes with itm
--     pf: function that can turn the position into tokens
--
chainPos :: Sign -> (Sign -> a -> (Pos, String) -> (Maybe Sign, Maybe Err))
            -> [a] -> [(Pos, String)] -> [Pos] -> ([Pos] -> [String])
            -> (Maybe Sign, Maybe Err)
chainPos sigma f itm ps pos pf =
  chainPos' sigma f itm (ps ++ (zip pos (pf pos))) Nothing

chain :: Sign -> (Sign -> a -> Sign) -> [a] -> Sign
chain sigma f l = foldl f sigma l

genSemi :: [Pos] -> [String]
genSemi [] = []
genSemi (h:t) = ";":(genSemi t)

genComma :: [Pos] -> [String]
genComma [] = []
genComma (h:t) = ",":(genComma t)

genColon :: [Pos] -> [String]
genColon [] = []
genColon (h:t) = ":":(genColon t)

str_pos_SORT_ITEM :: [Pos] -> [String]
str_pos_SORT_ITEM [] = []
str_pos_SORT_ITEM (h:t) = "sorts":(genSemi t)

str_pos_Sort_decl :: [Pos] -> [String]
str_pos_Sort_decl = genComma

str_pos_Subsort_decl :: [Pos] -> [String]
str_pos_Subsort_decl l = (genComma $ init l) ++ ["<"]

str_pos_Subsort_defn :: [Pos] -> [String]
str_pos_Subsort_defn _ = ["=","{",":",".","}"]

add_Sort_items :: Sign -> SIG_ITEMS -> (Maybe Sign, Maybe Err)
add_Sort_items sigma (Sort_items l p) = chainPos sigma add_SORT_ITEM l 
                                              [] p str_pos_SORT_ITEM
add_Sort_items _ (Op_items _ p) = (Nothing, illArg (head p) "add_Sort_items" "Op_items")
add_Sort_items _ (Pred_items _ p) = (Nothing, illArg (head p) "add_Sort_items" "Pred_items")
add_Sort_items _ (Datatype_items _ p) = (Nothing, illArg (head p) "add_Sort_items" "Datatype_items")

val_Sort_decl :: Sign -> SORT -> (Pos, String) -> Maybe Err
val_Sort_decl sigma s _ = Nothing

addf_Sort_decl :: Annoted SORT_ITEM -> Sign -> SORT -> (Pos, String) -> (Maybe Sign, Maybe Err)
addf_Sort_decl ann sigma id (pos,tok) =
    (Just (addSortItem ann sigma id Nothing Nothing pos tok), Nothing)

add_decl :: Sign -> a -> (Pos, String)
            -> (Sign -> a -> (Pos, String) -> (Maybe Sign, Maybe Err))
            -> (Sign -> a -> (Pos, String) -> Maybe Err)
            -> (Maybe Sign, Maybe Err)
add_decl sigma itm startpos addf valf =
  let
    val   = valf sigma itm startpos
    fatal = if (isJust val) then
              let (_,e) = (fromJust val) in e
                else
              False
    (res,err2) = if fatal then (Nothing, Nothing) else
                               addf sigma itm startpos
  in
    if fatal then
      (Nothing, val)
    else
      (res,addFromMaybe val err2)

add_Sort_decl :: Annoted SORT_ITEM -> Sign -> SORT -> (Pos, String) -> (Maybe Sign, Maybe Err)
add_Sort_decl ann sigma itm pos = add_decl sigma itm pos
                                  (addf_Sort_decl ann) val_Sort_decl

addf_Subsort_decl :: Annoted SORT_ITEM -> SORT -> Sign -> SORT -> (Pos, String)
                     -> (Maybe Sign, Maybe Err)
addf_Subsort_decl ann super sigma sub (pos,tok) =
  let
    res = addSortItem ann sigma sub (Just super) Nothing pos tok
  in
    (Just (addSubSort True sub res super), Nothing)

val_Subsort_decl :: SORT -> Sign -> SORT -> (Pos, String) -> Maybe Err
val_Subsort_decl super _ sub (pos,tok) =
  if (super==sub) then
    mkErr True pos ("subsort not distinct from supersort ("++(show sub)++")")
  else
    Nothing

add_Subsort_decl :: Annoted SORT_ITEM -> SORT -> Sign -> SORT
                    -> (Pos, String) -> (Maybe Sign, Maybe Err)
add_Subsort_decl elem s sigma itm pos = add_decl sigma itm pos 
                                         (addf_Subsort_decl elem s)
                                         (val_Subsort_decl s)

toVarDecl :: VAR -> SortId -> Pos -> VarDecl
toVarDecl var id pos = VarDecl var id (ListPos Colon pos)

-- FIXME
--
toFormula :: Annoted FORMULA -> Formula
toFormula _ = TrueAtom []

addf_Subsort_defn :: Annoted SORT_ITEM -> SORT -> VAR -> [Pos] ->
                     Annoted FORMULA -> Sign -> SORT -> (Pos, String)
                     -> (Maybe Sign, Maybe Err)
addf_Subsort_defn ann sub var p f sigma super (pos,tok) =
  let
    colpos = head $ drop 2 p
    defn   = SubsortDefn (toVarDecl var super colpos) (toFormula f) p
    res    = addSortItem ann sigma sub (Just super) (Just defn) pos tok
  in
    (Just (addSubSort True sub res super), Nothing)

varFreeInFormula :: Sign -> VAR -> FORMULA -> Bool
varFreeInFormula sigma var f = True

val_Subsort_defn :: SORT -> VAR -> Annoted FORMULA -> Sign ->
                    SORT -> (Pos, String) -> (Maybe Err)
val_Subsort_defn super var f sigma sub (pos,tok) =
  let 
    super_ex = hasSort sigma super
    distinct = sub/=super
    var_free = varFreeInFormula sigma var (item f)
    err1     = if super_ex then Nothing else mkErr True pos
               ("supersort not in environment ("++(show super)++")")
    err2     = if distinct then Nothing else mkErr True pos
               ("subsort not distinct from supersort ("++(show sub)++")")
    err3     = if var_free then Nothing else mkErr False pos
               ("variable "++(show var)++" not free in formula")
  in
    addFromMaybe err1 $ addFromMaybe err2 err3

add_Subsort_defn :: Annoted SORT_ITEM -> Sign -> SORT -> VAR -> SORT ->
                    (Annoted FORMULA) -> (Pos, String) -> [Pos]
                    -> (Maybe Sign, Maybe Err)
add_Subsort_defn itm sigma sub var super f pos p =
    add_decl sigma sub pos (addf_Subsort_defn itm super var p f)
                            (val_Subsort_defn super var f)

relAdd :: [SortId] -> [SortId] -> [SortId]
relAdd x y = x ++ [ z | z<-y, not $ elem z x ]

addIsos :: [SORT] -> Sign -> SORT -> Sign
addIsos isos sigma iso =
  let
    others = [ x | x<-isos, x/=iso ]
    res    = fromJust $ fromSigSortItem $ getSort sigma iso
    ol     = item res
    old    = sortRels ol
    new    = old { subsorts = relAdd (subsorts old) others,
                   supersorts = relAdd (supersorts old) others,
                   allsubsrts = relAdd (allsubsrts old) others,
                   allsupersrts = relAdd (allsupersrts old) others }
    ne     = ol { sortRels = new }
  in
    updateSigItem sigma iso (ASortItem (res { item = ne }))

add_Iso_decl :: Annoted SORT_ITEM -> Sign -> [SORT] -> (Pos, String)
                -> [Pos] -> (Maybe Sign, Maybe Err)
add_Iso_decl ann sigma isos pos p =
  let
    (res, err) = chainPos sigma (add_Sort_decl ann) isos [pos] p
                          str_pos_Iso_decl
  in
    if (isJust res) then
      let
        all = foldl (addIsos isos) (fromJust res) isos
      in
        (Just all, err)
    else
      (res, err)

str_pos_Iso_decl :: [Pos] -> [String]
str_pos_Iso_decl = genColon

add_SORT_ITEM :: Sign -> Annoted SORT_ITEM -> (Pos, String)
                 -> (Maybe Sign, Maybe Err)
add_SORT_ITEM sigma itm pos =
    case (item itm) of
             (Sort_decl l p) -> chainPos sigma (add_Sort_decl itm) l [pos] p
                                           str_pos_Sort_decl;
             (Subsort_decl l s p) -> chainPos sigma (add_Subsort_decl itm s) l
                                              [pos] p str_pos_Subsort_decl;
             (Subsort_defn s v t f p) -> add_Subsort_defn itm sigma s v t f
                                 pos p;
             (Iso_decl l p) -> add_Iso_decl itm sigma l pos p

------------------------------------------------------------------------------
-- THE END
------------------------------------------------------------------------------
