
module UserRulesHetCATS (hetcatsrules) where

import RuleUtils -- gives some examples 

import Pretty
import List 
import Char

hetcatsrules :: [RuleDef]
hetcatsrules = [("ShATermConvertible",shatermfn, "", "", Nothing),
	       	("UpPos",updateposfn, "", "", Nothing)]

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
      [ (makeToShATerm (name dat), empty)
{-      , (makeFromATerm (name dat),defaultFromATerm (name dat))-}
      ] 
      dat 
      $$ (makeFromShATermFn dat)
      $$ (makeFromToATermErrors dat)

makeToShATerm name body
  = let cvs = head (mknss [body] namesupply)
    in text "toShATerm att0" <+> -- this first Argument is an ATermTable
       ppCons cvs body <+>
       text "=" $$ nest 4 
       ( case childToShATerm "att" cvs (types body) of
	 childs ->
           ( vcat (childs)) $$ 
	    text "addATerm (ShAAppl" <+>
	    doubleQuotes (text (constructor body)) <+>
	    (if null cvs then text "[] [])" 
		else (char '[' <+>
		      hcat (punctuate comma (map addPrime cvs)) <+>  
		      text "] [])")) <+>
	    text ("att"++(show (length cvs))) <+> 
            (if null cvs then empty 
	                 else hcat $ replicate (length childs) (char '}')))


childToShATerm s vs ts = 
    let (_,vs') = List.mapAccumL childToATerm' (0,ts) vs in vs'
    where childToATerm' (i,t:ts) v = 
	      ((i+1,ts), 
	      text "case" <+> text ("toShATerm") <+> attO <+> v 
	       <+> text "of { " <+>  attN_v' <+> text "->")
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

makeFromToATermErrors dat = 
    block ((text "fromATerm _ =" <+> errorFn "fromATerm"): 
	   [text "toATerm _ =" <+> errorFn "toATerm"])
	where 
	errorFn fn_name = text "error \"function " 
			  <> (esc_quotes fn_name) 
			  <> text " not derived (implemented) for data type " 
			  <> (esc_quotes $ name dat)
			  <> text "\""
	esc_quotes str = text "\\\"" <> text str <> text "\\\""

	
makeFromShATerm body
  = let cvs = head (mknss [body] namesupply)
    in text "(ShAAppl" <+> doubleQuotes (text (constructor body)) <+>
       text "[" <+> 
       hcat (intersperse (text ",") cvs) <+> 
       text "] _)" <+>
       text "->" $$ nest 4 (
	    block ((kids cvs)++
		   [ppCons (map addPrime cvs) body <+> 
		    if null cvs then empty
		      else (hcat $ replicate (length cvs) (char '}'))]))
   where kids cvs = let (_,ks) = (List.mapAccumL 
				     (childFromShATerm (text "att")) 
			             (types body)
                                     cvs)
 		 in ks 

{-defaultFromATerm name = empty-}
{-  = hsep $ texts ["fromATerm", "u", "=", "fromATermError", (doublequote name), "u"] -}
childFromShATerm atn (t:ts) v
    = ( ts
      , (text "case fromShATerm" <+> 
	 parens (text "getATermByIndex1" <+> v <+> atn) <+> 
	 text "of { " <+> (addPrime v) <+> text "->")
      )


-- end of ATermConvertible derivation
