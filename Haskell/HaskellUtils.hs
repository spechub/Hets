module Haskell.HaskellUtils where

import Haskell.Hatchet.AnnotatedHsSyn
import Common.Named

type AHsDecls = [AHsDecl]

type NamedSentences = [Named AHsDecls]

extractSentences :: AHsModule -> NamedSentences
extractSentences (AHsModule _ _ _ decls) = [NamedSen { senName = "",
                                                       sentence = filterDecls decls }]

filterDecls :: AHsDecls -> AHsDecls
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
       (AHsFunBind _) -> decl:(filterDecls decls)
       (AHsPatBind _ _ _ _) -> decl:(filterDecls decls)
