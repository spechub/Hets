module Haskell.HaskellUtils where

import Haskell.Hatchet.AnnotatedHsSyn
import Common.Named

type AHsDecls = [AHsDecl]
type NamedSentences = [Named AHsDecl]

extractSentences :: AHsModule -> NamedSentences
extractSentences (AHsModule _ _ _ decls) = filterDecls decls

filterDecls :: AHsDecls -> NamedSentences
filterDecls [] = []
filterDecls (decl:decls) =
     case decl of
       (AHsTypeDecl _ _ _ _) -> filterDecls decls
       (AHsDataDecl _ _ _ _ _ _) -> filterDecls decls
       (AHsNewTypeDecl _ _ _ _ _ _) -> filterDecls decls
       (AHsClassDecl _ _ _) -> filterDecls decls
       (AHsInstDecl _ _ _) -> filterDecls decls
       (AHsDefaultDecl _ _) -> filterDecls decls
       (AHsInfixDecl _ _ _ _) -> filterDecls decls
       (AHsTypeSig _ _ _) -> filterDecls decls           -- skip: no sentences
       (AHsFunBind matches) -> ( NamedSen { senName = (show (1+(length decls))) ++ (funName matches), 
                                            sentence = decl } ):(filterDecls decls)
       (AHsPatBind _ pat _ _) -> ( NamedSen { senName =  (show (1+(length decls))) ++ (patName pat), 
                                              sentence = decl } ):(filterDecls decls)
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
