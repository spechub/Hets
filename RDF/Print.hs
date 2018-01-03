{- |
Module      :  ./RDF/Print.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Printer for N-triples

-}

module RDF.Print where

import Common.AS_Annotation
import Common.IRI
import Common.Doc hiding (sepBySemis, sepByCommas)
import Common.DocUtils hiding (ppWithCommas)

import OWL2.AS
import OWL2.Print ()

import RDF.AS
import RDF.Symbols
import RDF.Sign

import qualified Data.Set as Set
import Data.Maybe (isNothing)

sepBySemis :: [Doc] -> Doc
sepBySemis = vcat . punctuate (text " ;")

ppWithSemis :: Pretty a => [a] -> Doc
ppWithSemis = sepBySemis . map pretty

sepByCommas :: [Doc] -> Doc
sepByCommas = vcat . punctuate (text " ,")

ppWithCommas :: Pretty a => [a] -> Doc
ppWithCommas = sepByCommas . map pretty

instance Pretty Predicate where
    pretty = printPredicate

printPredicate :: Predicate -> Doc
printPredicate (Predicate anIRI) = pretty anIRI

instance Pretty RDFLiteral where
    pretty lit = case lit of
        RDFLiteral b lexi ty -> text (if not b
                then '"' : lexi ++ "\""
                else "\"\"\"" ++ lexi ++ "\"\"\"") <> case ty of
            Typed u -> keyword cTypeS <> pretty u
            Untyped tag -> if isNothing tag then empty
                    else let Just tag2 = tag in text "@" <> text tag2
        RDFNumberLit f -> text (show f)

instance Pretty PredicateObjectList where
    pretty = printPredObjList

printPredObjList :: PredicateObjectList -> Doc
printPredObjList (PredicateObjectList p ol) = pretty p <+> ppWithCommas ol

instance Pretty Subject where
    pretty = printSubject

printSubject :: Subject -> Doc
printSubject subj = case subj of
    Subject anIRI -> pretty anIRI
    SubjectList ls -> brackets $ ppWithSemis ls
    SubjectCollection c -> parens $ (hsep . map pretty) c

instance Pretty Object where
    pretty = printObject

printObject :: Object -> Doc
printObject obj = case obj of
    Object s -> pretty s
    ObjectLiteral l -> pretty l

instance Pretty Triples where
    pretty = printTriples

printTriples :: Triples -> Doc
printTriples (Triples s ls) = pretty s <+> ppWithSemis ls <+> dot

instance Pretty Statement where
    pretty = printStatement

printStatement :: Statement -> Doc
printStatement s = case s of
    Statement t -> pretty t
    PrefixStatement (PrefixR p anIRI)
        -> text "@prefix" <+> pretty p <> colon <+> pretty anIRI <+> dot
    BaseStatement (Base anIRI) -> text "@base" <+> pretty anIRI <+> dot

instance Pretty TurtleDocument where
    pretty = printDocument

printDocument :: TurtleDocument -> Doc
printDocument doc = (vcat . map pretty) (statements doc)

printExpandedIRI :: IRI -> Doc
printExpandedIRI anIRI =
 if (not $ hasFullIRI anIRI) || (isBlankNode anIRI) then 
       text $ showIRICase anIRI
  else text "<" <> text (showIRIFull anIRI) <> text ">"

instance Pretty Term where
    pretty = printTerm

printTerm :: Term -> Doc
printTerm t = case t of
    SubjectTerm anIRI -> printExpandedIRI anIRI
    PredicateTerm anIRI -> printExpandedIRI anIRI
    ObjectTerm obj -> case obj of
        Right lit -> pretty lit
        Left anIRI -> printExpandedIRI anIRI

instance Pretty Axiom where
    pretty = printAxiom

printAxiom :: Axiom -> Doc
printAxiom (Axiom sub pre obj) = pretty sub <+> pretty pre <+> pretty obj
                                                                    <+> text "."

printAxioms :: [Axiom] -> Doc
printAxioms = vcat . map pretty

-- | RDF signature printing
printRDFBasicTheory :: (Sign, [Named Axiom]) -> Doc
printRDFBasicTheory (_, l) = vsep (map (pretty . sentence) l)

instance Pretty Sign where
    pretty = printSign

printNodes :: String -> Set.Set Term -> Doc
printNodes s terms = text "#" <+> text s $+$
    vcat (map ((text "#\t\t" <+>) . pretty) (Set.toList terms))

printSign :: Sign -> Doc
printSign s = printNodes "subjects:" (subjects s)
    $+$ printNodes "predicates:" (predicates s)
    $+$ printNodes "objects:" (objects s)

-- | Symbols printing

instance Pretty RDFEntityType where
    pretty ety = text $ show ety

instance Pretty RDFEntity where
    pretty (RDFEntity ty ent) = pretty ty <+> pretty ent

instance Pretty SymbItems where
    pretty (SymbItems m us) = pretty m <+> ppWithCommas us

instance Pretty SymbMapItems where
    pretty (SymbMapItems m us) = pretty m
        <+> sepByCommas
            (map (\ (s, ms) -> sep
                [ pretty s
                , case ms of
                    Nothing -> empty
                    Just t -> mapsto <+> pretty t]) us)

instance Pretty RawSymb where
    pretty rs = case rs of
        ASymbol e -> pretty e
        AnUri u -> pretty u
