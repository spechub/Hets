-- stub module to add your own rules.
module UserRules where

import List (nub,intersperse,mapAccumL)
import StandardRules(Rule,Tag) -- gives some examples 
import RuleUtils -- useful to have a look at this too

{- datatype that rules manipulate :-


data Data = D {	name :: Name,			 -- type's name
			constraints :: [(Class,Var)], 
			vars :: [Var],		 -- Parameters
			body :: [Body],
			derives :: [Class],	 -- derived classes
			statement :: Statement}  -- type of statement
	   | Directive				 --|
	   | TypeName Name			 --| used by derive (ignore)
		deriving (Eq,Show) 

data Body = Body { constructor :: Constructor,
		    labels :: [Name], -- [] for a non-record datatype.
		    types :: [Type]} deriving (Eq,Show) 

data Statement = DataStmt | NewTypeStmt deriving (Eq,Show)

type Name = String
type Var = String
type Class = String
type Constructor = String

type Rule = (Tag, Data->Doc)

-}

-- add your rules to this list
userRules :: [Rule]
userRules = [("Binary", binary),
             ("Term", termfn),
             ("ATermConvertible", atermfn),
             ("Implode", implodefn),
             ("Explode", explodefn)
            ]


-- useful helper things
namesupply   = [text [x,y] | x <- ['a' .. 'z'], 
                             y <- ['a' .. 'z'] ++ ['A' .. 'Z']]
mknss []     _  = []
mknss (c:cs) ns =
  let (thisns,rest) = splitAt (length (types c)) ns
  in thisns: mknss cs rest 

mkpattern :: Constructor -> [a] -> [Doc] -> Doc
mkpattern c l ns =
  if null l then text c
  else parens (hsep (text c : take (length l) ns))

instanceheader cls dat =
  let fv     = vars dat
      tycon  = name dat
      ctx    = map (\v-> text cls <+> text v)
      parenSpace = parens . hcat . sepWith space
  in
  hsep [ text "instance"
       , opt fv (\v -> parenList (ctx v) <+> text "=>")
       , text cls
       , opt1 (texts (tycon: fv)) parenSpace id
       , text "where"
       ]

doublequote str
  = "\""++str++"\""




-- begin here for Binary derivation


binary dat = 
  let cs  = body dat
      cvs = mknss cs namesupply
      k   = (ceiling . logBase 2 . realToFrac . length) cs
  in
  instanceheader "Binary" dat $$
  block (  zipWith3 (putfn k) [0..] cvs cs
        ++ getfn k [0..] cvs cs
        :  getFfn k [0..] cvs cs
        :  zipWith (sizefn k) cvs cs
        )

putfn k n cv c =
  text "put bh" <+> ppCons cv c <+> text "= do" $$
  nest 8 (
    text "pos <- putBits bh" <+> text (show k) <+> text (show n) $$
    vcat (map (text "put bh" <+>) cv) $$
    text "return pos"
  )

ppCons cv c = mkpattern (constructor c) (types c) cv

getfn k ns cvs cs =
  text "get bh = do" $$
  nest 8 (
    text "h <- getBits bh" <+> text (show k) $$
    text "case h of" $$
    nest 2 ( vcat $
      zipWith3 (\n vs c-> text (show n) <+> text "-> do" $$
                          nest 6 (
                            vcat (map (\v-> v <+> text "<-" <+> text "get bh") vs) $$
                            text "return" <+> ppCons vs c
                          ))
               ns cvs cs
    )
  )

getFfn k ns cvs cs =
  text "getF bh p =" <+>
  nest 8 (
    text "let (h,p1) = getBitsF bh 1 p in" $$
    text "case h of" $$
    nest 2 ( vcat $
      zipWith3 (\n vs c-> text (show n) <+> text "->" <+>
                          parens (cons c <> text ",p1") <+>
                          hsep (map (\_-> text "<< getF bh") vs))
               ns cvs cs
    )
  )
  where cons =  text . constructor

sizefn k [] c =
  text "sizeOf" <+> ppCons [] c <+> text "=" <+> text (show k)
sizefn k cv c =
  text "sizeOf" <+> ppCons cv c <+> text "=" <+> text (show k) <+> text "+" <+>
  hsep (intersperse (text "+") (map (text "sizeOf" <+>) cv))


-- end of binary derivation



-- begin of implode derivation
-- Author: Joost.Visser@cwi.nl

termfn dat
  = instanceSkeleton "Term" 
       [ (makeImplode (name dat),defaultImplode (name dat))
       , (makeGetTypeId (name dat),defaultGetTypeId (name dat))
       , (makeExplode (name dat),defaultExplode)
       ] 
       dat

implodefn dat
  = instanceSkeleton "Implode" 
       [ (makeImplode (name dat),defaultImplode (name dat))
       , (makeGetTypeId (name dat),defaultGetTypeId (name dat))
       ] 
       dat


makeImplode name body
  = let cvs = head (mknss [body] namesupply)
    in text "implode" <+> 
       text "(TermRep" <+> text "(TypeRep" <+> text (doublequote name) <+> text "[])" <+>
--       text "(TermRep" <+> text (doublequote name) <+>
       text (doublequote (constructor body)) <+>
       text "[" <+> 
       hcat (intersperse (text ",") cvs) <+> 
       text "])" <+>
       text "=" <+> text "let" <+>
       vcat (map childImplode cvs) <+>
       text "in" <+>
       ppCons (map addPrime cvs) body
defaultImplode name
  = hsep $ texts ["implode", "u", "=", "implodeError", (doublequote name), "u"]
childImplode v
  = (addPrime v) <+> text "=" <+> text "implode" <+> v

addPrime doc = doc <> (text "'")

{- Old monadic variant:
makeImplode name body
  = let cvs = head (mknss [body] namesupply)
    in text "implode" <+> 
       text "(TermRep" <+> text (doublequote name) <+>
       text (doublequote (constructor body)) <+>
       text "[" <+> 
       hcat (intersperse (text ",") cvs) <+> 
       text "])" <+>
       text "=" <+> text "do" <+>
       vcat ( (map childImplode cvs)++[text "return"] ) <+>
       ppCons cvs body
defaultImplode
  = hsep $ texts ["implode", "_", "=" ,"mzero"]
childImplode v
  = v <+> text "<-" <+> text "implode" <+> v
-}

makeGetTypeId name body
  = empty
defaultGetTypeId name
--  = text "getTypeId" <+>
  = text "getTypeRep" <+>
    text "_" <+>
    text "=" <+>
    text "TypeRep" <+> text (doublequote name) <+> text "[]"


-- end of implode derivation




-- begin of explode derivation 
-- Author: Joost.Visser@cwi.nl

explodefn dat
  = instanceSkeleton "Explode" [(makeExplode (name dat),defaultExplode)] dat

makeExplode name body
  = let cvs = head (mknss [body] namesupply)
    in text "explode" <+> 
       ppCons cvs body <+>
       text "=" <+>
--       text "(TermRep" <+> text (doublequote name) <+>
       text "(TermRep" <+> text "(TypeRep" <+> text (doublequote name) <+> text "[])" <+>
       text (doublequote (constructor body)) <+>
       text "[" <+> 
       hcat (intersperse (text ",") (map childExplode cvs)) <+> 
       text "])"
defaultExplode
  = empty

childExplode v
  = text "explode" <+> v

-- end of explode derivation



-- begin of ATermConvertible derivation 
-- Author: Joost.Visser@cwi.nl
-- adapted by: luettich@tzi.de

atermfn dat
  = instanceSkeleton "ATermConvertible" 
      [ (makeToATerm (name dat),defaultToATerm)
{-      , (makeFromATerm (name dat),defaultFromATerm (name dat))-}
      ] 
      dat 
      $$ (makeFromATermFn dat)

makeToATerm name body
  = let cvs = head (mknss [body] namesupply)
    in text "toATerm att0" <+> -- this first Argument is an ATermTable
       ppCons cvs body <+>
       text "=" $$ nest 4 
       ((if null cvs then text "let lat = []" $$ text "in"
	 else
	 text "let" <+>
	 vcat ((childToATerm "att" cvs (types body))++
	       [text "lat = [" <+>
		hcat (intersperse (text ",") (map addPrime cvs)) <+>  
		text "]" ]) $$
	 text "in") <+> 
	text "addATermSp (AAppl" <+>
	con body <+>
	text " lat)" <+> c_parens body <+> 
	text ("att"++(show (length cvs))))


defaultToATerm
  = empty

childToATerm s vs ts = 
    let (_,vs') = List.mapAccumL childToATerm' (0,ts) vs in vs'
    where childToATerm' (i,t:ts) v = 
	      ((i+1,ts), 
	       attN_v' <+> text "=" <+> text ("toATerm"++str) <+> attO <+> v)
	      where attN_v' = hcat [text "(",text (s++(show (i+1))),
			      text ",", addPrime v, text ")"]
		    attO = text (s++(show i))
		    str = case t of
			  Con "String" -> "Str"
			  otherwise    -> ""
makeFromATermFn dat = 
    block (text "fromATerm att =": 
	   [block (fnstart:(block cases):[whereblock])])
	where 
	fnstart     = text "case" <+> text "aterm" <+> text "of"
        cases       = map (makeFromATerm (name dat)) (body dat)
	whereblock  =
	    text "where" $$
            block [(text "aterm = let" <+> text "aterms" <+> text "=" <+>
		    text "map (getATermSp att) pat_list" <+>
		    text "in" <+> text "findATerm aterms")
		  ,text "pat_list =" <+> 
		   bracketList (map makeFromATermPat (body dat))
		  ] 
		   
makeFromATermPat body = 
    text "(AAppl" <+> con body <+> text "[ ])" <+> c_parens body

makeFromATerm name body
  = let cvs = head (mknss [body] namesupply)
    in text "(AAppl" <+> con body <+>
       text "[" <+> 
       hcat (intersperse (text ",") cvs) <+> 
       text "])" <+>
       c_parens body <+>
       text "->" $$ 
	    block ((text "let"):(kids cvs)++
		   [text "in" <+> ppCons (map addPrime cvs) body])
   where kids cvs = let (_,ks) = (List.mapAccumL 
				     (childFromATerm (text "att")) 
			             (types body)
                                     cvs)
 		 in ks

defaultFromATerm name = empty
{-  = hsep $ texts ["fromATerm", "u", "=", "fromATermError", (doublequote name), "u"] -}
childFromATerm atn (t:ts) v
    = (ts,(addPrime v) <+> text "=" <+> text ("fromATerm"++str) <+> 
       parens (text "getATermByIndexSp1" <+> v <+> atn))
    where str = case t of
		Con "String" -> "Str"
		otherwise    -> ""

con body = let atc       = aterm_constructor body
	       (fc,atc') = case atc of
				    Const c ac -> (c,ac)
				    Args -> error "number of constructors < 1"
	   in text (doublequote fc) <+> con' atc'
    where con' atc = case atc of 
			      Args         -> empty
			      Const s atc' -> text "[" <+>
					      text "(AAppl" <+> 
					      text (doublequote s) <+> 
					      con' atc'

c_parens body = let atc  = aterm_constructor body
		    atc' = case atc of 
				    Const _ ac -> ac
				    Args  -> error "number of constructors < 1"
                in text (p atc')
    where p atc = case atc of
			   Args         -> ""
			   Const _ atc' -> "])" ++ (p atc')

-- end of ATermConvertible derivation
