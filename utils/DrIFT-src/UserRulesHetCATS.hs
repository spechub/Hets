{- |
Module      :  $Header$
Copyright   :  (c) K. Lüttich, C. Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

generate ShATermConvertible instances

-}

module UserRulesHetCATS (hetcatsrules) where

import RuleUtils -- gives some examples
import Pretty
import List

hetcatsrules :: [RuleDef]
hetcatsrules = [("ShATermConvertible",shatermfn, "", "", Nothing),
	       	("UpPos",updateposfn, "", "", Nothing)]

-- useful helper things
addPrime doc = doc <> char '\''

ppCons b vs = let c = ppCons' b vs in
    if null vs then c else parens c

ppCons' b vs = fsep $ text (constructor b) : vs

-- begin of PosItem derivation
updateposfn dat =
    if any ((elem posLC) . types) (body dat) then
       instanceSkeleton "PosItem" [ (makeGetPosFn, empty) ] dat
    else empty

posLC = Con "Range"

makeGetPosFn b =
       let (e, vs) = mapAccumL accFun empty (types b)
           accFun d t = if isEmpty d && t == posLC
                 then (text "p", text "p")
	         else (d, text "_")
       in hang (text "getRange" <+> ppCons b vs <+> text "=")
	       4 $ if isEmpty e then text "nullRange" else e
-- end of PosItem derivation

-- begin of ShATermConvertible derivation
-- Author: luettich@tzi.de

shatermfn dat
  = instanceSkeleton "ShATermConvertible"
      [ (makeToShATerm, empty) ]
      dat
      $$ makeFromShATermFn dat
      $$ makeTypeOf dat

makeToShATerm b
  = let ts = types b
        vs = varNames ts
    in text "toShATerm att0" <+> -- this first Argument is an ATermTable
       ppCons b vs <+>
       text "=" $$ nest 4
       (vcat (zipWith childToShATerm vs [0 :: Int ..]) $$
	    text "addATerm (ShAAppl" <+>
	    doubleQuotes (text (constructor b)) <+>
	    bracketList (varNames' ts) <+> text "[])" <+>
	    text ("att" ++ show (length ts)) <+>
            closeBraces ts)

closeBraces = hcat . map (const $ char '}')

childToShATerm v i = let
	   attN_v' = parenList [text ("att" ++ show (i+1)), addPrime v]
           attO = text ("att" ++ show i)
	   in text "case" <+> text "toShATerm" <+> attO <+> v
	       <+> text "of {" <+> attN_v' <+> text "->"

makeFromShATermFn dat =
    block [text "fromShATerm att =",
	   block [fnstart, block cases]]
	where
	fnstart     = text "case getATerm att of"
        cases       = map makeFromShATerm (body dat) ++ [def_case]
        u = text "u"
	def_case    = u <+> text "-> fromShATermError" <+>
		      doubleQuotes (text $ name dat) <+> u

makeFromShATerm b
  = let ts = types b
        cvs = varNames ts
        childFromShATerm v = text "case fromShATerm $ getATermByIndex1"
	          <+> v <+> text "att of {" <+> addPrime v <+> text "->"
    in text "ShAAppl" <+> doubleQuotes (text $ constructor b) <+>
       bracketList cvs <+> text "_ ->"
       $$ nest 4 (
	    block (map childFromShATerm cvs ++
		   [ppCons' b (varNames' ts) <+> closeBraces ts]))

makeTypeOf dat =
    block [text "type_of _ =" <+> doubleQuotes (text $ name dat)]

-- end of ATermConvertible derivation
