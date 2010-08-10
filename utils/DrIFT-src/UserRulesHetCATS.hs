{- |
Module      :  $Id$
Copyright   :  (c) K. Luettich, C. Maeder and Uni Bremen 2002-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

generate ShATermConvertible instances
-}

module UserRulesHetCATS (hetcatsrules) where

import RuleUtils -- gives some examples
import DataP
import Text.PrettyPrint.HughesPJ
import Data.List

hetcatsrules :: [RuleDef]
hetcatsrules =
  [ ("ShATermConvertible", shatermfn False, "", "", Nothing)
  , ("ShATermLG", shatermfn True, "", "", Nothing)
  , ("XmlContent", userRuleXmlNew, "Representation"
    , "encode terms as XML (HaXml>=1.14)", Nothing)
  , ("Binary", binaryfn False, "", "", Nothing)
  , ("BinaryLG", binaryfn True, "", "", Nothing)
  , ("Typeable", typeablefn, "", "", Nothing)
  , ("GetRange", getrangefn, "", "", Nothing)]

-- useful helper things
addPrime :: Doc -> Doc
addPrime = (<> char '\'')

ppCons' :: Body -> [Doc] -> Doc
ppCons' b = fsep . (text (constructor b) :)

-- XmlContent
userRuleXmlNew :: Data -> Doc
userRuleXmlNew dat =
  let cs = body dat             -- constructors
      cvs = mknss cs namesupply -- variables
  in
  instanceheader "HTypeable" dat $$
  block [toHTfn cs cvs dat] $$
  instanceheader "XmlContent" dat $$
  block (
    case cs of
      [c] -> text "parseContents = do"
             $$ nest 4 (text "{ inElementWith (flip isPrefixOf)"
                       <+> text (show (constructor c)) <+> text "$"
                       $$ parseFn True (head cvs) c
                       $$ text "}"
                       )
      _ -> text "parseContents = do"
            $$ nest 4 (text "{ e@(Elem t _ _) <- elementWith (flip isPrefixOf)"
                      <+> text (show (preorder cs (map constructor cs)))
                      $$ text "; case t of"
                      $$ nest 2 (text "_"
                                $$ nest 2 (vcat (preorder cs
                                                       (zipWith (parseFn False)
                                                                cvs cs))))
                      $$ text "}"
                      )
    : zipWith3 showsfn [0 ..] cvs cs)

toHTfn :: [Body] -> [[Doc]] -> Data -> Doc
toHTfn cs cvs dat =
  let typ = name dat
      fvs = vars dat
      pats = concat (zipWith mkpat cvs cs)
  in
  text "toHType v =" $$
  nest 4 (
    text "Defined" <+>
    fsep [ text "\"" <> text typ <> text "\""
         , bracketList (map text fvs)
         , bracketList (zipWith toConstr cvs cs)
         ]
    ) $$
  if null pats then empty
  else nest 2 (text "where") $$
       nest 4 (vcat (map (<+> text "= v") pats)) $$
       nest 4 (vcat (map (simplest typ (zip cvs cs)) fvs))

namesupply :: [Doc]
namesupply =
  [text [x, y] | x <- ['a' .. 'z'], y <- ['a' .. 'z'] ++ ['A' .. 'Z']]

mknss :: [Body] -> [a] -> [[a]]
mknss [] _ = []
mknss (c : cs) ns =
  let (thisns, rest) = splitAt (length (types c)) ns
  in thisns : mknss cs rest

mkpat :: [Doc] -> Body -> [Doc]
mkpat ns c =
  if null ns then []
  else [mypattern (constructor c) (types c) ns]


toConstr :: [Doc] -> Body -> Doc
toConstr ns c =
  let cn = constructor c
      ts = types c
      fvs = nub (concatMap deepvars ts)
  in
  text "Constr" <+>
  fsep [ text "\"" <> text cn <> text "\""
       , bracketList (map text fvs)
       , bracketList (map (text "toHType" <+>) ns)
       ]
  where
    deepvars (Arrow _ _) = []
    -- deepvars (Apply t1 t2)  = deepvars t1 ++ deepvars t2
    deepvars (LApply _ ts) = concatMap deepvars ts
    deepvars (Var s) = [s]
    deepvars (Con _) = []
    deepvars (Tuple ts) = concatMap deepvars ts
    deepvars (List t) = deepvars t

simplest :: String -> [([Doc], Body)] -> String -> Doc
simplest typ cs fv =
  let npats = [ (depth, (n, pat)) | (ns, c) <- cs
                                , (n, t) <- zip ns (types c)
                                , (depth, pat) <- [ findT fv t ]
              ]
      (_, (r, rpat)) =
          foldl closest (Nothing, error "free tyvar not found") npats
  in
  parens rpat <+> text "= toHType" <+> r
  where
    findT :: String -> Type -> (Maybe Int, Doc)
    findT v ty = case ty of
      Arrow _ _ ->
        (Nothing, error "can't derive Haskell2Xml/HTypeable for arrow type")
      LApply c ts
        | c == Con typ -> (Nothing, text "_")
        | otherwise -> let
            (_, cpat) = findT v c
            dpats = map (findT v) ts
            (ds, _) = unzip dpats
            in perhaps (combine ds)
               $ cpat <+> bracketList (map (snd . uncurry perhaps) dpats)
               <+> text "_"
      Var s -> perhaps (if v == s then Just 0 else Nothing) (text v)
      Con s -> (Nothing, text "Defined" <+> text "\"" <> text s <> text "\"")
      Tuple ts -> let
        dpats = map (findT v) ts
        (ds, _) = unzip dpats
        in perhaps (combine ds)
           $ text "Tuple" <+> bracketList (map (snd . uncurry perhaps) dpats)
      List t -> let (d, pat) = findT v t
        in perhaps (inc d) (text "List" <+> parens pat)
    perhaps jn doc = (jn, maybe (text "_") (const doc) jn)
    combine ds = let js = [ n | Just n <- ds ] in
        if null js then Nothing else inc (Just (minimum js))
    inc = fmap (+ 1)
    closest :: (Maybe Int, a) -> (Maybe Int, a) -> (Maybe Int, a)
    closest a b = case (a, b) of
      ((Nothing, _), (Just _, _)) -> b
      ((Just n, _), (Just m, _)) | m >= n -> b
      _ -> a


-- showsfn (n = index) (ns = variables) (cn = constructor body)
showsfn :: Int -> [Doc] -> Body -> Doc
showsfn n ns cn =
  let cons = constructor cn
      typ = types cn
      sc = parens (text "showConstr" <+> text (show n) <+>
                     parens (text "toHType" <+> text "v"))
      cfn [] = text "[]"
      cfn [x] = parens (text "toContents" <+> x)
      cfn xs = parens
        (text "concat" <+> bracketList (map (text "toContents" <+>) xs))
  in
  text "toContents" <+>
  text "v@" <> mypattern cons typ ns <+> text "=" $$
  nest 4 (text "[mkElemC" <+> sc <+> cfn ns <> text "]")

preorder :: [Body] -> [b] -> [b]
preorder cs =
    map snd . reverse . sortBy (\ (a, _) (b, _) -> compare a b)
    . zip (map constructor cs)


-- parseFn (ns = variables) (cn = constructor body)
parseFn :: Bool -> t -> Body -> Doc
parseFn single _ cn =
  let cons = constructor cn
      arity = length (types cn)
      intro = if single then empty
              else text "|" <+> text (show cons)
                   <+> text "`isPrefixOf` t -> interior e $"
  in
  case arity of
    0 -> intro <+> nest 8 (text "return" <+> text cons)
    1 -> intro <+> nest 8 (text "fmap" <+> text cons <+> text "parseContents")
    _ -> intro $$ nest 8 (text "return" <+> text cons
                          <+> fsep (replicate arity
                                    (text "`apply` parseContents")))

instanceheader :: String -> Data -> Doc
instanceheader cls dat =
  let fv = vars dat
      tycon = name dat
      ctx = map (\ v -> text cls <+> text v)
      parenSpace = parens . hcat . sepWith space
  in
  hsep [ text "instance"
       , opt fv (\ v -> parenList (ctx v) <+> text "=>")
       , text cls
       , opt1 (texts (tycon : fv)) parenSpace id
       , text "where"
       ]

mypattern :: Constructor -> [a] -> [Doc] -> Doc
mypattern c l ns =
  if null l then text c else parens (hsep (text c : take (length l) ns))

-- begin of GetRange derivation
getrangefn :: Data -> Doc
getrangefn dat =
       instanceSkeleton "GetRange" [] dat
       $$ (if any (elem posLC . types) (body dat) then
              text "  getRange x = case x of"
              $$ block (map makeGetPosFn $ body dat)
          else text "  getRange = const nullRange")
       $$ text "  rangeSpan x = case x of"
       $$ block (map makeSpanFn $ body dat)

posLC :: Type
posLC = Con "Range"

makeGetPosFn :: Body -> Doc
makeGetPosFn b =
       let (r, vs) = mapAccumL accFun True (types b)
           p = text "p"
           accFun f t =
               if f && t == posLC then (False, p) else (f, text "_")
       in ppCons' b vs <+> rArrow <+> if r then text "nullRange" else p

makeSpanFn :: Body -> Doc
makeSpanFn b =
  let vs = varNames $ types b
  in ppCons' b vs <+> rArrow
      <+> if null vs then text "[]" else
       text "joinRanges" <+> bracketList (map (text "rangeSpan" <+>) vs)

-- end of GetRange derivation

binaryfn :: Bool -> Data -> Doc
binaryfn forLG dat =
  let dn = strippedName dat
      cs = body dat
      moreCs = length cs > 1
      u = text "u"
  in instanceSkeleton (if forLG then "BinaryLG" else "Binary")
         [] dat
     $$ text ("  put" ++ (if forLG then "LG" else "") ++ " xv = case xv of")
     $$ block (zipWith (makePutBinary forLG moreCs) cs [0 .. ])
     $$ text ("  get" ++ (if forLG then "LG lg" else "") ++ " = "
              ++ if moreCs then "getWord8 >>= \\ tag -> case tag of" else "do")
     $$ block (zipWith (makeGetBinary forLG moreCs) cs [0 .. ] ++
       [u <+> rArrow <+> text "fromBinaryError"
         <+> doubleQuotes (text dn) <+> u | moreCs])

makePutBinary :: Bool -> Bool -> Body -> Int -> Doc
makePutBinary forLG moreCs b i =
    let vs = varNames $ types b
        putComp v = text ("put" ++ if forLG then "LG" else "") <+> v
        hl = if moreCs then text ("putWord8 " ++ show i) else
                 if null vs then text "return ()" else empty
    in ppCons' b vs <+> rArrow <+> (if null vs then hl else text "do")
          $$ if null vs then empty else nest 2 . vcat $ hl : map putComp vs

makeGetBinary :: Bool -> Bool -> Body -> Int -> Doc
makeGetBinary forLG moreCs b i =
    let vs = varNames $ types b
        getComp v =
          v <+> lArrow <+> text ("get" ++ if forLG then "LG lg" else "")
        rl = text ("return" ++ if null vs then "" else " $") <+> ppCons' b vs
    in (if moreCs then text (show i) <+> rArrow else empty)
       <+> (if null vs then rl else if moreCs then text "do" else empty)
       $$ if null vs then empty else nest 2 . vcat $ map getComp vs ++ [rl]

-- begin of ShATermConvertible derivation
shatermfn :: Bool -> Data -> Doc
shatermfn forLG dat =
  let dn = strippedName dat
      cs = body dat
      u = text "u"
  in instanceSkeleton (if forLG then "ShATermLG" else "ShATermConvertible")
         [] dat
     $$ text ("  toShATerm" ++ (if forLG then "LG" else "Aux")
              ++ " att0 xv = case xv of")
     $$ block (map (makeToShATerm forLG) cs)
     $$ text ("  fromShATerm" ++ (if forLG then "LG lg" else "Aux")
                 ++ " ix att0 = case getShATerm ix att0 of")
     $$ block (map (makeFromShATerm forLG) cs ++
               [u <+> rArrow <+> text "fromShATermError"
                <+> doubleQuotes (text dn) <+> u])

att :: Int -> Doc
att i = text $ "att" ++ show (i :: Int)

closeBraces :: [b] -> Doc
closeBraces = hcat . map (const $ char '}')

pair :: Doc -> Doc -> Doc
pair f s = parens $ f <> comma <+> s

makeToShATerm :: Bool -> Body -> Doc
makeToShATerm forLG b =
    let ts = types b
        tooLong = length (constructor b) > 15
        vs = varNames ts
        rl = text "return $ addATerm (ShAAppl" <+>
            doubleQuotes (text (constructor b)) <+>
            bracketList (varNames' ts) <+> text "[])" <+>
            att (length ts)
    in ppCons' b vs <+> rArrow <+>
       (if null vs then if tooLong then empty else rl else text "do")
       $$ if null vs then if tooLong then nest 2 rl else empty
          else nest 2 . vcat $ zipWith (childToShATerm forLG) vs [0 :: Int ..]
                   ++ [rl]

childToShATerm :: Bool -> Doc -> Int -> Doc
childToShATerm forLG v i = pair (att $ i + 1) (addPrime v) <+> lArrow
    <+> text ("toShATerm" ++ if forLG then "LG'" else "'") <+> att i <+> v

makeFromShATerm :: Bool -> Body -> Doc
makeFromShATerm forLG b =
    let ts = types b
        vs = varNames ts
        childFromShATerm v i =
          text ("case fromShATerm" ++ if forLG then "LG' lg" else "'")
          <+> v <+> att i <+> text "of"
          $$ text "{" <+> pair (att $ i + 1) (addPrime v) <+> rArrow
        rl = pair (att $ length ts) (ppCons' b $ varNames' ts)
             <+> closeBraces ts
    in text "ShAAppl" <+> doubleQuotes (text $ constructor b) <+>
       bracketList vs <+> text "_" <+> rArrow
       <+> (if null vs then rl else empty)
       $$ if null vs then empty else
          nest 2 . vcat $ zipWith childFromShATerm vs [0 :: Int ..] ++ [rl]
-- end of ATermConvertible derivation

typeablefn :: Data -> Doc
typeablefn dat =
    let vs = vars dat
        dn = strippedName dat
        ntext str = str ++ if null vs then "" else show $ length vs
        tcname = text $ "_tc" ++ dn ++ "Tc"
    in tcname <+> text ":: TyCon"
       $$ tcname <+> equals <+> text "mkTyCon"
           <+> doubleQuotes (text $ name dat)
       $$ text ("instance " ++ ntext "Typeable" ++ " " ++ dn ++ " where")
       $$ block [ text (ntext "typeOf" ++ " _ = mkTyConApp")
                  <+> tcname <+> brackets empty]
