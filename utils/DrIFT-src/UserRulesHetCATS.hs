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
               , ("UpPos", updateposfn, "", "", Nothing)]

-- useful helper things
addPrime doc = doc <> char '\''

dc = text "::"

ppCons b vs = let c = ppCons' b vs in
    if null vs then c else parens c

ppCons' b vs = fsep $ text (constructor b) : vs

-- begin of PosItem derivation
updateposfn dat =
    if any ((elem posLC) . types) (body dat) then
       let tc = strippedName dat
           tn = "_" ++ tc
           td = text ("getRange" ++ tn)
       in
       vcat [ hsep $ [td, dc] ++ texts (tc : vars dat) ++ [text "-> Range"]
            , hsep [td, text "x", equals, text "case x of"]
            , block $ map makeGetPosFn $ body dat]
       $$ instanceSkeleton "PosItem" [] dat
       $$ block [text "getRange" <+> equals <+> td]
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
shatermfn dat
  = let tn = "_" ++ strippedName dat
  in vcat (map (makeToShATerm tn) $ body dat)
     $$ makeFromShATermFn dat
     $$ instanceSkeleton "ShATermConvertible"
      [] dat
      $$ block
        [ text "toShATermAux" <+> equals <+> text ("_toShATermAux" ++ tn)
        , text "fromShATermAux" <+> equals <+> text ("_fromShATermAux" ++ tn)]

att i = text $ "att" ++ show (i :: Int)

closeBraces = hcat . map (const $ char '}')

pair f s = parens $ f <> comma <+> s

makeToShATerm tn b
  = let ts = types b
        vs = varNames ts
    in text ("_toShATermAux" ++ tn) <+> att 0 <+>
       ppCons b vs <+>
       equals <+> text "do" $$ nest 4
       (vcat (zipWith childToShATerm vs [0 :: Int ..]) $$
            text "return $ addATerm (ShAAppl" <+>
            doubleQuotes (text (constructor b)) <+>
            bracketList (varNames' ts) <+> text "[])" <+>
            att (length ts))

childToShATerm v i = pair (att $ i + 1) (addPrime v) <+> lArrow
    <+> text "toShATerm'" <+> att i <+> v

makeFromShATermFn dat =
    vcat [text ("_fromShATermAux" ++ "_" ++ strippedName dat)
                    <+> text "ix att0 =",
           block [fnstart, block $ cases ++ [def_case]]]
        where
        fnstart     = text "case getShATerm ix att0 of"
        cases       = map makeFromShATerm (body dat)
        typename    = strippedName dat
        u           = text "u"
        def_case    = u <+> rArrow <+> text "fromShATermError" <+>
                      doubleQuotes (text typename) <+> u

makeFromShATerm b
  = let ts = types b
        cvs = varNames ts
        childFromShATerm v i =
            text "case fromShATerm'"
                  <+> v <+> att i <+> text "of {"
                       <+> pair (att $ i + 1) (addPrime v) <+> rArrow
    in text "ShAAppl" <+> doubleQuotes (text $ constructor b) <+>
       bracketList cvs <+> text "_" <+> rArrow
       $$ nest 4 (
            block (zipWith childFromShATerm cvs [0 :: Int ..] ++
                   [pair (att $ length ts) (ppCons' b $ varNames' ts)
                             <+> closeBraces ts]))
-- end of ATermConvertible derivation

typeablefn :: Data -> Doc
typeablefn  dat
  = tcname <+> equals <+> text "mkTyCon" <+>
         doubleQuotes (text $ name dat) $$
    instanceSkeleton "Typeable" [] dat $$ block (
        [ text "typeOf" <+> text (if null tvars then "_" else "x")
              <+> equals <+> text "mkTyConApp"  <+>
          tcname <+>
          brackets (hcat $ sepWith comma $ map getV' tvars) $$
          wheres ])
    where
      tvars = vars dat
      tcname = text $ "_tc_" ++ strippedName dat  ++ "Tc"
      wheres = where_decls $ map getV tvars
      tpe    = text (strippedName dat) <+>
               hcat (sepWith space $ map text tvars)
      getV' var
        = text "typeOf" <+> parens (text "get" <> text var <+> text "x")
      getV var
        = text "get" <> text var <+> dc <+> tpe <+> rArrow
          <+> text var $$
          text "get" <> text var <+> equals <+> text "undefined"
      where_decls [] = empty
      where_decls ds = text "  where" $$ block ds
