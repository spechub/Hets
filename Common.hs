{- |
Module      :  $Header$
Description :  folder description
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This folder contains general purpose libraries and modules to be shared.

All CASL related logics and the structured part share
identifiers and annotations as well as their parsing and printing.

 * "Common.Amalgamate"           amalgamation options

 * "Common.AnalyseAnnos"         analysis of annotations

 * "Common.Anno_Parser"          parsing annotations

 * "Common.AnnoState"            parser state keeping annotations

 * "Common.AS_Annotation"        annotations and named sentences

 * "Common.ConvertGlobalAnnos"   print analysed annotations

 * "Common.ConvertLiteral"
        test and convert applications to literals

 * "Common.ConvertMixfixToken"
        decompose numbers and strings to applications

 * "Common.DefaultMorphism"
        just a source and target signature (no mappings)

 * "Common.Doc"                  new plain text and latex printing documents

 * "Common.DocUtils"             further utilities for pretty documents

 * "Common.DynamicUtils"         only a wrapper for Data.Dynamic.mkTyConApp

 * "Common.Earley"
        the mixfix resolution engine used for CASL and HasCASL

 * "Common.GlobalAnnotations"
        analysed list, number and display annotations

 * "Common.Id"                   simple, mixfix and compound identifiers

 * "Common.Keywords"             string constants for keywords

 * "Common.LaTeX_AS_Annotation"  latex printing of annotations

 * "Common.LaTeX_funs"

 * "Common.LaTeX_maps"

 * "Common.LaTeX_utils"

 * "Common.Lexer"                parsing words, signs and nested comments

 * "Common.OrderedMap"           reordered maps

 * "Common.Partial"              utilities for partial orders

 * "Common.PPUtils"              pretty printing utilities

 * "Common.Prec"                 precedence computations

 * "Common.PrettyPrint"          pretty printing classes and instance

 * "Common.Print_AS_Annotation"  pretty printing of annotations

 * "Common.PrintLaTeX"

 * "Common.ProofUtils"           naming sentences

 * "Common.Result"               a kind of error monad

 * "Common.ResultT"              a generalized result monad

 * "Common.RunParsers"           support for test drivers

 * "Common.SimpPretty"           printing aterms

 * "Common.Taxonomy"             Taxonomy options

 * "Common.Token"                parsing identifiers

 * "Common.ToId"                 identifier translation (i.e. for Kif)

 * "Common.Utils"                some functions for lists

 * "Common.ATerm.AbstractSyntax" shared ATerms

 * "Common.ATerm.ConvInstances"  some aterm conversion instances

 * "Common.ATerm.Conversion"     other aterm conversion instances

 * "Common.ATerm.ReadWrite"      reading and writing aterms

 * "Common.Lib.Map"              see Data.Map

 * "Common.Lib.Pretty"           adapted printer for latex

 * "Common.Lib.Rel"              relations as special graphs

 * "Common.Lib.Set"              see Data.Set

 * "Common.Lib.State"            a portable state monad

-}
module Common where
