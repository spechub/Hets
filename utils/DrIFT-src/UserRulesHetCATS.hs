{- |
Module      :  $Id$
Copyright   :  (c) K. Lüttich, C. Maeder and Uni Bremen 2002-2006
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
               , ("UpPos", getrangefn, "", "", Nothing)]

-- useful helper things
addPrime doc = doc <> char '\''

dc = text "::"

ppCons' b vs = fsep $ text (constructor b) : vs

-- begin of PosItem derivation
getrangefn dat =
    if any ((elem posLC) . types) (body dat) then
       let vs = vars dat in
       text "instance PosItem" <+> (if null vs then id else parens)
            (hsep . texts $ strippedName dat : vs) <+> text "where"
       $$ text "  getRange x = case x of"
       $$ block (map makeGetPosFn $ body dat)
    else empty

posLC = Con "Range"

makeGetPosFn b =
       let (r, vs) = mapAccumL accFun True (types b)
           p = text "p"
           accFun b t = if b && t == posLC
                 then (False, p)
                 else (b, text "_")
       in ppCons' b vs <+> rArrow <+> if r then text "nullRange" else p
-- end of PosItem derivation

-- begin of ShATermConvertible derivation
shatermfn dat =
  let dn = strippedName dat
      tn = "_" ++ dn
      tc = text ("_toATC" ++ tn)
      fc = text ("_fromATC" ++ tn)
      u = text "u"
  in tc <+> text "att0 xv = case xv of"
     $$ block (map makeToShATerm $ body dat)
     $$ fc <+> text "ix att0 = case getShATerm ix att0 of"
     $$ block (map makeFromShATerm (body dat) ++
               [u <+> rArrow <+> text "fromShATermError"
                <+> doubleQuotes (text dn) <+> u])
     $$ instanceSkeleton "ShATermConvertible" [] dat
     $$ block
        [ text "toShATermAux" <+> equals <+> tc
        , text "fromShATermAux" <+> equals <+> fc]

att i = text $ "att" ++ show (i :: Int)

closeBraces = hcat . map (const $ char '}')

pair f s = parens $ f <> comma <+> s

makeToShATerm b =
    let ts = types b
        vs = varNames ts
        rl = text "return $ addATerm (ShAAppl" <+>
            doubleQuotes (text (constructor b)) <+>
            bracketList (varNames' ts) <+> text "[])" <+>
            att (length ts)
    in ppCons' b vs <+> rArrow <+> (if null vs then rl else text "do")
       $$ if null vs then empty
          else block $ zipWith childToShATerm vs [0 :: Int ..] ++ [rl]

childToShATerm v i = pair (att $ i + 1) (addPrime v) <+> lArrow
    <+> text "toShATerm'" <+> att i <+> v

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
