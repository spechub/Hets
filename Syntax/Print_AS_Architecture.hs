{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

   Printing the Architechture stuff of HetCASL.
-}
{-
   todo:
     - ATermConversion SML-CATS has now his own module 
       (s. HetCATS/aterm_conv/)
     - LaTeX Pretty Printing
-}

module Syntax.Print_AS_Architecture where

import Common.Lib.Pretty
import Common.PPUtils
import Common.PrettyPrint
import Common.Keywords

import Syntax.AS_Architecture
import Syntax.Print_AS_Structured

instance PrettyPrint ARCH_SPEC where
    printText0 ga (Basic_arch_spec aa ab _) =
	let aa' = fsep $ punctuate semi $ map (printText0 ga) aa
	    ab' = printText0 ga ab
	in (hang (text (unitS ++ sS)) 4 aa') $$ (text resultS <+> ab')
    printText0 ga (Arch_spec_name aa) =
	printText0 ga aa
    printText0 ga (Group_arch_spec aa _) =
	braces $ printText0 ga aa

instance PrettyPrint UNIT_REF where
    printText0 ga (Unit_ref aa ab  _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <> colon <+> ab'

instance PrettyPrint UNIT_DECL_DEFN where
    printText0 ga (Unit_decl aa ab ac _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
            ac' = if null ac then empty
                  else text givenS <+>
                       (fcat $  punctuate (comma <> space) $
                                   map (printText0 ga) ac)
        in hang (aa' <> colon <+> ab') 4  ac'
    printText0 ga (Unit_defn aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in hang (aa' <+> equals) 4 ab'

instance PrettyPrint UNIT_SPEC where
    printText0 ga (Unit_type aa ab _) =
	let aa' = fsep $ punctuate (space<>char '*') $ 
			 map (condBracesGroupSpec printText0 
			                   braces Nothing ga) aa
	    ab' = printText0 ga ab
	in if null aa then ab' else aa' <+> text funS <+> ab'
    printText0 ga (Spec_name aa) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Closed_unit_spec aa _) =
	let aa' = printText0 ga aa
	in hang (text closedS) 4 aa'

instance PrettyPrint REF_SPEC where
    printText0 ga (Unit_spec u) = printText0 ga u
    printText0 ga (Refinement b u m r _) =
       (if b then empty else text behaviourallyS <> space)
       <> text refinedS <+> printText0 ga u <+>
       (if null m then empty else text "via" <+> 
          commaT_text ga m <> space) <> printText0 ga r
    printText0 ga (Arch_unit_spec aa _) =
	let aa' = printText0 ga aa
	in hang (text archS <+> text specS) 4 aa'
    printText0 ga (Compose_ref aa _) =
        listSep_text (space <> text thenS) ga aa
    printText0 ga (Component_ref aa _) =
        braces $ commaT_text ga aa

instance PrettyPrint UNIT_EXPRESSION where
    printText0 ga (Unit_expression aa ab _) =
	let aa' = cat $ punctuate (semi <> space) $ map (printText0 ga) aa
	    ab' = printText0 ga ab
	in if null aa then ab' 
	   else hang (text lambdaS) 4 (hang aa' (-2) (char '.' <+> ab'))

instance PrettyPrint UNIT_BINDING where
    printText0 ga (Unit_binding aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> colon <+> ab'

instance PrettyPrint UNIT_TERM where
    printText0 ga (Unit_reduction aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in fsep [aa', ab']
    printText0 ga (Unit_translation aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in fsep [aa', ab']
    printText0 ga (Amalgamation aa _) =
	listSep_text (space <> text andS) ga aa
    printText0 ga (Local_unit aa ab _) =
	let aa' = fcat $ punctuate (semi<>space) $ map (printText0 ga) aa
	    ab' = printText0 ga ab
	in (hang (text localS) 4 aa') $$ 
	   (hang (text withinS) 4 ab')
    printText0 ga (Unit_appl aa ab _) =
	let aa' = printText0 ga aa
	    ab' = fsep $ map (brackets . (printText0 ga)) ab
	in aa' <+> (if null ab then empty else ab')
    printText0 ga (Group_unit_term aa _) =
	braces $ printText0 ga aa

instance PrettyPrint FIT_ARG_UNIT where
    printText0 ga (Fit_arg_unit aa ab _) =
	printText0 ga aa  <> 
        (if null ab then empty else space <> text fitS <+> 
            printText0 ga ab)
