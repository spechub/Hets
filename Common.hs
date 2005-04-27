{- | 

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

 * "Common.DynamicUtils"

 * "Common.Earley"
        the mixfix resolution engine used for CASL and HasCASL

 * "Common.GlobalAnnotations"    
        analysed list, number and display annotations 

 * "Common.GraphUtils"

 * "Common.Id"                   simple, mixfix and compound identifiers 

 * "Common.Keywords"

 * "Common.LaTeX_AS_Annotation"

 * "Common.LaTeX_funs"

 * "Common.LaTeX_maps"

 * "Common.LaTeX_utils"

 * "Common.Lexer"                parsing words, signs and nested comments

 * "Common.PPUtils"              pretty printing utilities

 * "Common.PrettyPrint"

 * "Common.PrintLaTeX"

 * "Common.Print_AS_Annotation"

 * "Common.Result"               a kind of error monad

 * "Common.RunParsers"           a test driver (unused by Main)

 * "Common.SimpPretty"           printing aterms

 * "Common.Taxonomy"             Taxonomy options           

 * "Common.Token"                parsing identifiers

 * "Common.Utils"                some functions for lists 

 * "Common.ATerm.AbstractSyntax"

 * "Common.ATerm.ConvInstances"

 * "Common.ATerm.Conversion"

 * "Common.ATerm.ReadWrite"

 * "Common.Lib.Graph"

 * "Common.Lib.Map"

 * "Common.Lib.Pretty"

 * "Common.Lib.Rel"

 * "Common.Lib.Set"

 * "Common.Lib.SimpleMap"

 * "Common.Lib.State"

-}
module Common where
