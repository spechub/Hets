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
import Pretty
import List

hetcatsrules :: [RuleDef]
hetcatsrules = [ ("ShATermConvertible", shatermfn False, "", "", Nothing)
               , ("ShATermLG", shatermfn True, "", "", Nothing)
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

-- begin of ShATermConvertible derivation
shatermfn :: Bool -> Data -> Doc
shatermfn forLG dat =
  let dn = strippedName dat
      u = text "u"
  in instanceSkeleton (if forLG then "ShATermLG" else "ShATermConvertible")
         [] dat
     $$ text ("  toShATerm" ++ (if forLG then "LG" else "Aux")
              ++ " att0 xv = case xv of")
     $$ block (map (makeToShATerm forLG) $ body dat)
     $$ text ("  fromShATerm" ++ (if forLG then "LG lg" else "Aux")
                 ++ " ix att0 = case getShATerm ix att0 of")
     $$ block (map (makeFromShATerm forLG) (body dat) ++
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
       $$ if null vs then if tooLong then block [rl] else empty
          else block $ zipWith (childToShATerm forLG) vs [0 :: Int ..] ++ [rl]

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
          block $ zipWith childFromShATerm vs [0 :: Int ..] ++ [rl]
-- end of ATermConvertible derivation

typeablefn :: Data -> Doc
typeablefn dat =
    let vs = vars dat
        dn = strippedName dat
        ntext str = str ++ if null vs then "" else show $ length vs
        tcname = text $ "_tc_" ++ dn  ++ "Tc"
    in tcname <+> equals <+> text "mkTyCon"
           <+> doubleQuotes (text $ name dat)
       $$ text ("instance " ++ ntext "Typeable" ++ " " ++ dn ++ " where")
       $$ block [ text (ntext "typeOf" ++ " _ = mkTyConApp")
                  <+> tcname <+> brackets empty]
