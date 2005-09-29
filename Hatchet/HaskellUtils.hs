{-| 
Module      :  $Header$
Copyright   :  (c) Sonja Groening, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

-} 

module Hatchet.HaskellUtils where

import Haskell.Hatchet.AnnotatedHsSyn
import Common.AS_Annotation

type AHsDecls = [AHsDecl]
type NamedSentences = [Named AHsDecl]

extractSentences :: AHsModule -> NamedSentences
extractSentences (AHsModule _ _ _ decls) = filterDecls decls

filterDecls :: AHsDecls -> NamedSentences
filterDecls [] = []
filterDecls (decl:decls) =
     (case decl of
       AHsFunBind matches -> 
           [(emptyName decl) { senName = show (1 + length decls) 
                                         ++ funName matches }]
       AHsPatBind _ pat _ _ -> 
           [(emptyName decl) { senName = show (1 + length decls) 
                                         ++ patName pat }]
       _ -> []) ++ filterDecls decls
     where funName ((AHsMatch _ name _ _ _):rest) = show name
           patName pat =
             case pat of
               AHsPVar name -> show name
               AHsPLit lit -> "Literal"
               AHsPNeg p -> "-" ++ patName p
               AHsPInfixApp _ name _ -> show name
               AHsPApp name _ -> show name
               AHsPTuple _ -> "Tuple"
               AHsPList _ -> "List"
               AHsPParen p -> patName p
               AHsPRec name _ -> show name
               AHsPAsPat name _ -> show name
               AHsPWildCard -> "Wildcard"
               AHsPIrrPat p -> "~" ++ patName p
