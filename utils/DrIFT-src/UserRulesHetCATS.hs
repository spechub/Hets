
module UserRulesHetCATS (hetcatsrules) where

import RuleUtils -- gives some examples 

import Pretty
import List 
import Char

hetcatsrules :: [Rule]
hetcatsrules = [("ATermConvertible",atermfn),
		("ShATermConvertible",shatermfn),
		("CATermConvertible",catermfn),
	       	("UpPos",updateposfn)]
	    

catermfn dat = instanceSkeleton "ATermConvertible" 
	       [ (makeToATerm (name dat),defaultToATerm)
	       , (makeFromATerm (name dat),defaultFromATerm (name dat))
	       , (makeToShATerm (name dat),defaultToATerm)
	       ] dat $$ (makeFromShATermFn dat)

-- begin of ATermConvertible derivation 
-- Author: Joost.Visser@cwi.nl

atermfn dat
  = instanceSkeleton "ATermConvertible" 
      [ (makeToATerm (name dat),defaultToATerm)
      , (makeFromATerm (name dat),defaultFromATerm (name dat))
      ] 
      dat

makeToATerm name body
  = let cvs = head (mknss [body] namesupply)
    in text "toATerm" <+> 
       ppCons cvs body <+>
       text "=" <+>
       text "(AAppl" <+>
       doubleQuotes (text (constructor body)) <+>
       text "[" <+> 
       hcat (intersperse (text ",") (map childToATerm cvs)) <+> 
       text "] [])"
defaultToATerm
  = empty
childToATerm v
  = text "toATerm" <+> v

makeFromATerm name body
  = let cvs = head (mknss [body] namesupply)
    in text "fromATerm" <+> 
       text "(AAppl" <+>
       doubleQuotes (text (constructor body)) <+>
       text "[" <+> 
       hcat (intersperse (text ",") cvs) <+> 
       text "] _)" <+>
       text "=" <+> text "let" <+>
       vcat (map childFromATerm cvs) <+>
       text "in" <+>
       ppCons (map addPrime cvs) body
defaultFromATerm name
  = hsep $ texts ["fromATerm", "u", "=", "fromATermError", 
		  ('\"':name++"\""), "u"]
childFromATerm v
  = (addPrime v) <+> text "=" <+> text "fromATerm" <+> v

-- end of ATermConvertible derivation

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

addPrime doc = doc <> char '\''

ppCons cv c = mkpattern (constructor c) (types c) cv

-- begin of PosItem derivation 
-- Author: luettich@tzi.de
updateposfn dat =
    if oneHas_p || oneHas_pl then
       instanceSkeleton "PosItem"
	       [ ((makeUpPosFn "up_pos"   pos   oneHas_p) , empty)
	       , ((makeUpPosFn "up_pos_l" pos_l oneHas_pl), empty)
	       , ((makeGetPosFn "get_pos"   pos   oneHas_p) , empty)
	       , ((makeGetPosFn "get_pos_l" pos_l oneHas_pl), empty)
	       ]
               dat
    else
      empty
    where 
       oneHas tp =  any ((elem tp) . types) (body dat)
       oneHas_p  = oneHas pos
       oneHas_pl = oneHas pos_l	   
       pos   = Con "Pos"
       pos_l = List (Con "Pos")

makeUpPosFn fname tp hasPos body =
    if hasPos then
       let 
           cvs   = head (mknss [body] namesupply)
	   cvs'  = map (appFn tp (text "fn1")) (zip cvs (types body))
{-	   hasTP = trace (show cvs' ++ " : (" 
			  ++ show hasTP' ++ "," 
			  ++ show (types body) ++ ")") $ hasTP' -}
	   hasTP = any (== tp) $ types body
       in hang (text fname <+> 
		(if hasTP then 
		    text "fn1" 
		 else
		    text "_"
		) <+> ppCons cvs body <+> text "=") 
	       4
	       (ppCons cvs' body)
    else
       empty
    where appFn appt fn (var,t) = 
	      if t == appt then 
		 parens (fn <+> var) 
	      else 
	         var

makeGetPosFn fname tp hasPos body =
    if hasPos then
       let 
           cvs  = head (mknss [body] namesupply)
	   (vs,cvs') = mapAccumL (var_or_ tp) [] (zip cvs (types body))
       in hang (text fname <+> ppCons cvs' body <+> text "=") 
	       4
	       (case vs of 
		  []        -> text "Nothing"
		  [v]       -> text "Just" <+> v
		  otherwise -> 
		     error ("*** something strange occured:" ++ fname)
	       )
    else
       empty
    where var_or_ appt accum (var,t) = 
	      if t == appt then 
		 (var:accum,var)
	      else 
	         (accum,text "_")

-- end of PosItem derivation 

-- begin of ATermConvertible derivation 
-- Author: luettich@tzi.de

shatermfn dat
  = instanceSkeleton "ATermConvertible" 
      [ (makeToShATerm (name dat),defaultToATerm)
{-      , (makeFromATerm (name dat),defaultFromATerm (name dat))-}
      ] 
      dat 
      $$ (makeFromShATermFn dat)

makeToShATerm name body
  = let cvs = head (mknss [body] namesupply)
    in text "toShATerm att0" <+> -- this first Argument is an ATermTable
       ppCons cvs body <+>
       text "=" $$ nest 4 
       ((if null cvs then text "let lat = []" $$ text "in"
	 else
	 text "let" <+>
	 vcat ((childToShATerm "att" cvs (types body))++
	       [text "lat = [" <+>
		hcat (intersperse (text ",") (map addPrime cvs)) <+>  
		text "]" ]) $$
	 text "in") <+> 
	text "addATerm (ShAAppl" <+>
	doubleQuotes (text (constructor body)) <+>
	text " lat [])" <+> 
	text ("att"++(show (length cvs))))


childToShATerm s vs ts = 
    let (_,vs') = List.mapAccumL childToATerm' (0,ts) vs in vs'
    where childToATerm' (i,t:ts) v = 
	      ((i+1,ts), 
	       attN_v' <+> text "=" <+> text ("toShATerm") <+> attO <+> v)
	      where attN_v' = hcat [text "(",text (s++(show (i+1))),
			      text ",", addPrime v, text ")"]
		    attO = text (s++(show i))
{-		    str = case t of
			  Con "String" -> "Str"
			  otherwise    -> ""-}


makeFromShATermFn dat = 
    block (text "fromShATerm att =": 
	   [block (fnstart:(block cases):[whereblock])])
	where 
	fnstart     = text "case" <+> text "aterm" <+> text "of"
        cases       = map makeFromShATerm (body dat)++[def_case]
	def_case    = hsep $ texts ["u", "->", "fromShATermError", 
		  ('\"':name dat++"\""), "u"]
	whereblock  =
	    text "where" $$
            block [text "aterm = getATerm att" ]
	choose_att = text (if is_upper_d_const then "att'" else "att")
	is_upper_d_const = and (map isUpper_ (name dat))
	    where isUpper_ x = x == '_' || isUpper x 
	
makeFromShATerm body
  = let cvs = head (mknss [body] namesupply)
    in text "(ShAAppl" <+> doubleQuotes (text (constructor body)) <+>
       text "[" <+> 
       hcat (intersperse (text ",") cvs) <+> 
       text "] _)" <+>
       text "->" $$ nest 4 (
	    (text "let") <+> block ((kids cvs)++
		   [text "in" <+> ppCons (map addPrime cvs) body]))
   where kids cvs = let (_,ks) = (List.mapAccumL 
				     (childFromShATerm (text "att")) 
			             (types body)
                                     cvs)
 		 in ks 

{-defaultFromATerm name = empty-}
{-  = hsep $ texts ["fromATerm", "u", "=", "fromATermError", (doublequote name), "u"] -}
childFromShATerm atn (t:ts) v
    = ( ts
      , (addPrime v) <+> text "=" <+> 
	      (text ("fromShATerm") <+> 
	       parens (text "getATermByIndex1" <+> v <+> atn))
      )


-- end of ATermConvertible derivation
