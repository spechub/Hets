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
import Result
import Graph

------------------------------------------------------------------------------
-- types
------------------------------------------------------------------------------

type Err = ([String],Bool)

type Sentences = [(String,Sentence)]

type LocalEnv = (Sign, Sentences)

------------------------------------------------------------------------------
-- Functions on signature element
------------------------------------------------------------------------------

emptySign :: Sign
emptySign = SignAsMap emptyFM empty

emptyLocalEnv :: LocalEnv
emptyLocalEnv = (emptySign,[])

newRels :: SortRels
newRels = SortRels [] [] [] []

allUnique :: Eq a => [a] -> Bool
allUnique [] = False
allUnique [h] = True
allUnique (h:t) = ([ x | x<-t, x == h ]==[]) && allUnique t

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
    old = sortRels $ item res
    new = if (direct) then
            old { subsorts = relAdd (subsorts old) [sub],
                  allsubsrts = relAdd (allsubsrts old) [sub] }
          else
            old { allsubsrts = relAdd (allsubsrts old) [sub] }
    ext  = (item res) { sortRels = new }
    s'  = updateSigItem sigma super (ASortItem (res { item = ext }))
    s'' = chain s' (addSubSort False sub) (allsupersrts old)
  in
    chain s'' (addSuperSorts (allsupersrts old)) (allsubsrts old)
    
addSuperSorts :: [SortId] -> Sign -> SortId -> Sign
addSuperSorts supers sigma sub =
  let
    res = fromJust $ fromSigSortItem $ getSort sigma sub
    old = sortRels $ item res
    new = old { allsupersrts = relAdd (allsupersrts old) supers }
    ext = (item res) { sortRels = new }
  in
    updateSigItem sigma sub (ASortItem (res { item = ext }))

chainPos' :: LocalEnv -> (LocalEnv -> a -> (Pos, String) -> Result LocalEnv)
             -> [a] -> [(Pos,String)] -> Result LocalEnv
chainPos' env f [] [] = return env
chainPos' env f [] (h:t) = return env
chainPos' env f (a:as) (p:ps) =
  do env' <- f env a p
     chainPos' env' f as ps

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
chainPos :: LocalEnv -> (LocalEnv -> a -> (Pos, String) -> Result LocalEnv)
            -> [a] -> [(Pos,String)] -> [Pos] -> ([Pos] -> [String])
            -> Result LocalEnv
chainPos env f itm ps pos pf =
  chainPos' env f itm (ps ++ (zip pos (pf pos)))

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

strPosSORT_ITEM :: [Pos] -> [String]
strPosSORT_ITEM [] = []
strPosSORT_ITEM (h:t) = "sorts":(genSemi t)

strPosSortDecl :: [Pos] -> [String]
strPosSortDecl = genComma

strPosSubsortDecl :: [Pos] -> [String]
strPosSubsortDecl l = (genComma $ init l) ++ ["<"]

strPosSubsortDefn :: [Pos] -> [String]
strPosSubsortDefn _ = ["=","{",":",".","}"]

addSortDecl :: Annoted SORT_ITEM -> LocalEnv -> SORT -> (Pos, String)
               -> Result LocalEnv
addSortDecl itm (sigma,psi) sort (pos,token) =
  return (addSortItem itm sigma sort Nothing Nothing pos token,psi)

checkSubDistinctSuper :: LocalEnv -> Pos -> SORT -> SORT -> Result LocalEnv
checkSubDistinctSuper env pos sub super =
  if (super /= sub) then
    return env
  else
    fatal_error "subsort not distinct from supersort in subsort declaration"
                pos

addSubsortDecl :: Annoted SORT_ITEM -> Maybe SortDefn -> SORT -> LocalEnv
                  -> SORT -> (Pos, String) -> Result LocalEnv
addSubsortDecl itm defn super env sub (pos,tok) =
  do (sigma,psi) <- checkSubDistinctSuper env pos super sub
     return (addSubSort True sub
             (addSortItem itm sigma sub (Just super) defn pos tok) super,psi)

toVarDecl :: VAR -> SortId -> Pos -> VarDecl
toVarDecl var id pos = VarDecl var id (ListPos Colon pos)

-- FIXME
--
toFormula :: Annoted FORMULA -> Formula
toFormula _ = TrueAtom []

varFreeInFormula :: Sign -> VAR -> FORMULA -> Bool
varFreeInFormula sigma var f = True

toSentence :: String -> Formula -> (String, Sentence)
toSentence str f = (str, Axiom (Annoted (AxiomDecl [] f []) [] [] []))

checkSuperExists :: LocalEnv -> Pos -> SORT -> Result LocalEnv
checkSuperExists (sigma,psi) pos super =
  if (hasSort sigma super) then
    return (sigma,psi)
  else
    fatal_error "supersort does not exist in subsort definition" pos

addSubsortFormula :: LocalEnv -> Pos -> VAR -> SORT -> SORT -> Annoted FORMULA
                     -> Result LocalEnv
addSubsortFormula (sigma,psi) colpos var sub super f =
  let
    f' = copyAnnoted f (Quantification Universal [(Var_decl [var] super
                        [colpos])] (Equivalence (item f) (Membership
                        (Simple_id var) sub []) []) [])
  in
    return (sigma,psi ++ [(toSentence "") $ toFormula f'])

addSubsortDefn :: Annoted SORT_ITEM -> LocalEnv -> SORT -> VAR -> SORT
                  -> Annoted FORMULA -> (Pos, String) -> [Pos]
                  -> Result LocalEnv
addSubsortDefn itm env sub var super f (pos,token) p =
  let
    colpos = head $ drop 2 p
    defn   = SubsortDefn (toVarDecl var super colpos) (toFormula f) p
  in
    do env'   <- checkSuperExists env pos super
       env''  <- checkSubDistinctSuper env' pos sub super
       env''' <- addSubsortDecl itm (Just defn) super env sub (pos,token)
       addSubsortFormula env''' colpos var sub super f

relAdd :: [SortId] -> [SortId] -> [SortId]
relAdd x y = x ++ [ z | z<-y, not $ elem z x ]

addIsoSubsorting :: [SORT] -> Sign -> SORT -> Sign
addIsoSubsorting isos sigma iso =
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

checkAllUnique :: LocalEnv -> Pos -> [SORT] -> Result LocalEnv
checkAllUnique env pos sorts =
  if (allUnique sorts) then
    return env
  else
    fatal_error "sort occurs more than once in isomorphism declaration" pos

checkMoreThanOne :: LocalEnv -> Pos -> [SORT] -> Result LocalEnv
checkMoreThanOne env pos sorts =
  if ((length sorts)>=2) then
    return env
  else
    fatal_error "only one sort in isomorphism declaration" pos

addIsoDecl :: Annoted SORT_ITEM -> LocalEnv -> [SORT] -> (Pos, String)
                -> [Pos] -> Result LocalEnv
addIsoDecl itm env sorts pos p =
  do env'        <- checkAllUnique env (fst pos) sorts
     env''       <- checkMoreThanOne env (fst pos) sorts
     (sigma,psi) <- chainPos env'' (addSortDecl itm) sorts [pos]
                             p strPosIsoDecl
     return (foldl (addIsoSubsorting sorts) sigma sorts,psi)

strPosIsoDecl :: [Pos] -> [String]
strPosIsoDecl = genColon

addSORT_ITEM :: LocalEnv -> Annoted SORT_ITEM -> (Pos, String)
                 -> Result LocalEnv
addSORT_ITEM env itm pos =
    case (item itm) of
      (Sort_decl l p)          -> chainPos env (addSortDecl itm) l [pos] p
                                           strPosSortDecl;
      (Subsort_decl l s p)     -> chainPos env (addSubsortDecl itm Nothing s)
                                           l [pos] p strPosSubsortDecl;
      (Subsort_defn s v t f p) -> addSubsortDefn itm env s v t f pos p;
      (Iso_decl l p)           -> addIsoDecl itm env l pos p

addSIG_ITEMS :: LocalEnv -> SIG_ITEMS -> Result LocalEnv
addSIG_ITEMS env (Sort_items l p) = chainPos env addSORT_ITEM l 
                                              [] p strPosSORT_ITEM
addSIG_ITEMS env (Op_items _ p) = return env
addSIG_ITEMS env (Pred_items _ p) = return env
addSIG_ITEMS env (Datatype_items _ p) = return env

------------------------------------------------------------------------------
-- THE END
------------------------------------------------------------------------------
