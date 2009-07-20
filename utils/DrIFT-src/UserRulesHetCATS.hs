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
hetcatsrules = [ ("ShATermConvertible", shatermfn, "", "", Nothing)
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
shatermfn :: Data -> Doc
shatermfn dat =
  let dn = strippedName dat
      u = text "u"
  in instanceSkeleton "ShATermConvertible" [] dat
     $$ text "  toShATermAux" <+> text "att0 xv = case xv of"
     $$ block (map makeToShATerm $ body dat)
     $$ text "  fromShATermAux" <+> text "ix att0 = case getShATerm ix att0 of"
     $$ block (map makeFromShATerm (body dat) ++
               [u <+> rArrow <+> text "fromShATermError"
                <+> doubleQuotes (text dn) <+> u])

att :: Int -> Doc
att i = text $ "att" ++ show (i :: Int)

closeBraces :: [b] -> Doc
closeBraces = hcat . map (const $ char '}')

pair :: Doc -> Doc -> Doc
pair f s = parens $ f <> comma <+> s

makeToShATerm :: Body -> Doc
makeToShATerm b =
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
          else block $ zipWith childToShATerm vs [0 :: Int ..] ++ [rl]

childToShATerm :: Doc -> Int -> Doc
childToShATerm v i = pair (att $ i + 1) (addPrime v) <+> lArrow
    <+> text "toShATerm'" <+> att i <+> v

makeFromShATerm :: Body -> Doc
makeFromShATerm b =
    let ts = types b
        vs = varNames ts
        childFromShATerm v i = text "case fromShATerm'"
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
