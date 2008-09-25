{- |
Module      :  $Id$
Description :  commonly used modules
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
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

 * "Common.Earley"
        the mixfix resolution engine used for CASL and HasCASL

 * "Common.ExtSign"
        a (signature) data type extended with a symbol set

 * "Common.GlobalAnnotations"
        analysed list, number and display annotations

 * "Common.Id"                   simple, mixfix and compound identifiers

 * "Common.InjMap"               one-to-one mappings

 * "Common.Keywords"             string constants for keywords

 * "Common.LaTeX_funs"           latex printing support

 * "Common.LaTeX_maps"           latex string size mapping

 * "Common.Lexer"                parsing words, signs and nested comments

 * "Common.LibName"              library names as keys for development graphs

 * "Common.OrderedMap"           reordered maps

 * "Common.Partial"              utilities for partial orders

 * "Common.Prec"                 precedence computations

 * "Common.PrintLaTeX"           latex rendering

 * "Common.ProofUtils"           naming sentences

 * "Common.Result"               a kind of error monad

 * "Common.ResultT"              a generalized result monad

 * "Common.SExor"                lisp s-expressions as exchange format

 * "Common.SimpPretty"           printing aterms

 * "Common.Taxonomy"             Taxonomy options

 * "Common.Token"                parsing identifiers

 * "Common.ToId"                 identifier translation (i.e. for Kif)

 * "Common.Utils"                some functions for lists

 * "Common.ATerm.AbstractSyntax" shared ATerms

 * "Common.ATerm.ConvInstances"  some aterm conversion instances

 * "Common.ATerm.Conversion"     other aterm conversion instances

 * "Common.ATerm.ReadWrite"      reading and writing aterms

 * "Common.Lib.Pretty"           adapted printer for latex

 * "Common.Lib.Rel"              relations as special graphs

 * "Common.Lib.State"            a portable state monad

-}
module Common where
