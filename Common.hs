{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This folder contains general purpose libraries and modules to be shared.

All CASL related logics and the structured part share
identifiers and annotations as well as their parsing and printing.

 * "Common.AS_Annotation"        annotations and named sentences

 * "Common.Amalgamate"           amalgamation options

 * "Common.AnalyseAnnos"         analysis of annotations

 * "Common.AnnoState"            parser state keeping annotations

 * "Common.Anno_Parser"          parsing annotations

 * "Common.ConvertGlobalAnnos"   print analysed annotations

 * "Common.ConvertLiteral"       
        decompose numbers and strings to applications

 * "Common.DefaultMorphism"      
        just a source and target signature (no mappings) 

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

 * "Common.PPUtils"              pretty printing utilities

 * "Common.PrettyPrint"          pretty printing classes and instance

 * "Common.PrintLaTeX"           

 * "Common.Print_AS_Annotation"  pretty printing of annotations

 * "Common.Result"               a kind of error monad

 * "Common.RunParsers"           a test driver (unused by Main)

 * "Common.SimpPretty"           printing aterms

 * "Common.Taxonomy"             Taxonomy options           

 * "Common.Token"                parsing identifiers

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
