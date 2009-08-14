{- |
Module      :  $Id$
Copyright   :  (c) K. Luettich, C. Maeder and Uni Bremen 2002-2006
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
  , ("Binary", binaryfn False, "", "", Nothing)
  , ("BinaryLG", binaryfn True, "", "", Nothing)
  , ("Typeable", typeablefn, "", "", Nothing)
  , ("GetRange", getrangefn, "", "", Nothing)]

-- useful helper things
addPrime :: Doc -> Doc
addPrime doc = doc <> char '\''

ppCons' :: Body -> [Doc] -> Doc
ppCons' b vs = fsep $ text (constructor b) : vs

-- begin of GetRange derivation
getrangefn :: Data -> Doc
getrangefn dat =
    if any ((elem posLC) . types) (body dat) then
       let vs = vars dat in
       text "instance GetRange" <+> (if null vs then id else parens)
            (hsep . texts $ strippedName dat : vs) <+> text "where"
       $$ text "  getRange x = case x of"
       $$ block (map makeGetPosFn $ body dat)
    else empty

posLC :: Type
posLC = Con "Range"

makeGetPosFn :: Body -> Doc
makeGetPosFn b =
       let (r, vs) = mapAccumL accFun True (types b)
           p = text "p"
           accFun f t = if f && t == posLC
                 then (False, p)
                 else (f, text "_")
       in ppCons' b vs <+> rArrow <+> if r then text "nullRange" else p
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
       if moreCs then [u <+> rArrow <+> text "fromBinaryError"
         <+> doubleQuotes (text dn) <+> u] else [])

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
          <+> v <+> att i <+> text "of {"
          <+> pair (att $ i + 1) (addPrime v) <+> rArrow
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
        tcname = text $ "_tc" ++ dn  ++ "Tc"
    in tcname <+> text ":: TyCon"
       $$ tcname <+> equals <+> text "mkTyCon"
           <+> doubleQuotes (text $ name dat)
       $$ text ("instance " ++ ntext "Typeable" ++ " " ++ dn ++ " where")
       $$ block [ text (ntext "typeOf" ++ " _ = mkTyConApp")
                  <+> tcname <+> brackets empty]
