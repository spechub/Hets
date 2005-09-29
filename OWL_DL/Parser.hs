{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
 Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.
-}

module OWL_DL.Parser where

import OWL_DL.AS
import Text.XML.HXT.DOM.XmlTree
import Text.XML.HXT.DOM.XmlTreeTypes
import Text.XML.HXT.DOM.Namespace
import Text.XML.HXT.DOM.EditFilters
-- import Text.XML.HXT.DOM.FormatXmlTree
import Text.XML.HXT.Parser.XmlParser
import Common.Result
import Common.Id
import Char
import Monad

type ResXmlTree = XmlTree -> Result XmlTrees
type ResXmlTrees = XmlTrees -> Result XmlTrees

propAndValidateNamespaces :: ResXmlTree
propAndValidateNamespaces t
      = validate $ propagateNamespaces t
        where validate ct = let errs = foldr (++) [] $ Prelude.map validateNamespaces ct
                            in if null errs
                               then Result {diags = [], maybeResult = Just ct}
                               else checkErrs errs 

checkErrs :: ResXmlTrees
checkErrs [] = Result { diags = [], maybeResult = Just []}
checkErrs xt@[(NTree node _)] = 
       case node of
       XError n diag -> 
           let kind = case n of
                             1 -> Warning
                             2 -> Error
                             3 -> Error
                             _ -> Hint
               diagnosis = Diag{ diagKind = kind,
                                 diagString  = diag,
                                 diagPos      = nullPos
                               }
           in  Result{ diags = [diagnosis],
                       maybeResult = if kind == Warning then
                                        Just xt
                                        else Nothing
                     }
       _  -> Result{ diags = [],
                     maybeResult = Just xt
                   }
checkErrs (hd:errs) = let Result d1 _ = checkErrs [hd]
                          Result d2 _ = checkErrs errs
                      in  Result {diags = d1++d2, maybeResult = Nothing}


class (Show a) => XmlTransformer a where
    fromXmlTree  :: XmlTree  -> Result a
    fromXmlTrees :: XmlTrees -> Result [a]
    fromXmlTrees = mapM fromXmlTree


instance XmlTransformer Ontology where
    fromXmlTree tree =  
        let ((Result diagNs maybeNs), subtrees) = analyseNamespace tree
            (properties, subtrees2) = analyseHeader subtrees 
        in  -- wenn keine Annotation in OntologyHeader hat, ... 
            if null properties
               then let directives = []   -- analyseTail subtrees     -- axiom oder fact
                    in  case maybeNs of
                          Just namespaces -> Result{ diags = diagNs,
                                                     maybeResult = Just (Ontology Nothing properties directives namespaces) }
                          Nothing -> Result{ diags = diagNs,
                                                     maybeResult = Just (Ontology Nothing properties directives []) }
               else let directives  = [] -- analyseTail subtrees2    -- analyseOntology subtree2
                    in  case maybeNs of
                            Just namespaces -> Result{ diags = diagNs,
                                                       maybeResult = Just (Ontology Nothing properties directives namespaces) }
                            Nothing -> Result{ diags = diagNs,
                                                       maybeResult = Just (Ontology Nothing properties directives []) }


analyseNamespace :: XmlTree -> (Result [Namespace], XmlTrees)  -- (namespaces, rest)
analyseNamespace (NTree node trees) =
    case node of 
        XTag qname nspaces  -> 
             if (tName qname) == "rdf:RDF" then
                let Result diagNs mResNs = mapM anns nspaces
                in  if null diagNs 
                       then ((Result {diags = diagNs, maybeResult = Nothing}), trees)
                       else 
                          case mResNs of
                               Just resNs ->((Result {diags = [], 
                                                      maybeResult = Just ((NTree (XAttr qname) []):resNs)}), 
                                              trees)
                               Nothing -> ((Result {diags = [], 
                                                    maybeResult = Just [(NTree (XAttr qname) [])]}), 
                                              trees)
                    else analyseNamespace $ head trees
        _  -> analyseNamespace $ head trees   -- nicht sicher, ob alle Namespaces am Anfang
                                              -- der Xml-Datei legen.
        where 
              anns :: XmlTree -> Result Namespace
              anns hts = case hts of 
                              NTree attrib text -> 
                                      Result {diags = [],
                                              maybeResult = Just (NTree (addURI attrib (head text)) []) } 
                              _ -> warning (NTree (XText "") []) "format of namespaces illegal." nullPos
                                  
              addURI :: XNode -> NTree XNode -> XNode
              addURI (XAttr (QN pre local _)) (NTree (XText text) _) = 
                           XAttr QN{ namePrefix = pre, 
                                     localPart = local, 
                                     namespaceUri = text} 
              addURI n _ = n             -- remove warning


-- ist Header immer der erste Knoten in XmlTrees?
analyseHeader :: XmlTrees -> ([Axiom], XmlTrees)
analyseHeader [] = ([], [])
analyseHeader (firstT:trees) = 
     case firstT of 
          NTree (XTag tagName rdfabout) st -> 
              if tName tagName == "owl:Ontology" 
                 then case head rdfabout of 
                          NTree (XAttr ontoProp) _ -> 
                             ((anaheader st), trees) 
                          _ -> ([],[])         -- remove warning
                 else case analyseHeader trees of
                      (res,trees') -> (res, firstT:trees') --(trees ++ [firstT])
          _ -> analyseHeader trees

    where anaheader :: XmlTrees -> [Axiom]
          anaheader [] = []
          anaheader (tr:restT) = 
              case tr of
                 NTree (XTag tagName attr) sub ->
                     let aname = tName tagName
                     in  if (aname == "owl:versionInfo" ||
                             aname == "owl:label" ||
                             aname == "rdfs:comment"  ||
                             aname == "rdfs:seeAlso" ||
                             aname == "rdfs:isDefinedBy")
                            then (AnnotationProperty tagName (buildAnno tagName sub)):(anaheader restT)
                            else (OntologyProperty tagName (buildAnno tagName attr)):(anaheader restT)       -- sub wird hier weggelassen...
                 _ -> anaheader restT
                  
          buildAnno tn text = 
                  if null text 
                     then [DLAnnotation tn (PlainL ("", ""))] 
                     else buildAnnotations tn text

          buildAnnotations tn [] = []
          buildAnnotations tn (text:rest) = 
                  case text of 
                       NTree (XText str) _ -> 
                          if (any isAlphaNum str) then
                             (DLAnnotation tn (PlainL (str, ""))):(buildAnnotations tn rest)
                             else buildAnnotations tn rest
                       NTree (XAttr tn') text' -> (map (\x -> case x of NTree (XText t) _ -> URIAnnotation tn' (mkName t)) text')++(buildAnnotations tn rest)
                       _ ->  (OntAnnotation (mkName "") (mkName "")):(buildAnnotations tn rest)


analyseTail :: XmlTrees -> Result [Directive]
analyseTail trees = mapM analyseTail' trees 

  where 
   analyseTail' :: XmlTree -> Result Directive
   analyseTail' tree = 
     case tree of
          NTree (XTag tagName tagTrees) subTrees -> 
               case tName tagName of
                    "owl:Class"  -> 
                        case owlClass tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)} 
                                                                 
                    "owl:Restriction" -> 
                        case owlRestriction tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)} 
                    "rdf:Property" -> 
                        case rdfProp tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)} 
                    "owl:ObjectProperty" -> 
                        case owlObjProp tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)} 
                    "owl:FunctionalProperty" ->  
                        case owlFuncProp tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)} 
                    "owl:InverseFunctionalProperty" -> 
                        case owlInvFuncProp tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)}
                    "owl:TransitiveProperty" -> 
                        case owlTransProp tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)}
                    "owl:SymmetricProperty" -> 
                        case owlSymmProp tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)}
                    "rdf:Description" -> 
                        case rdfDescription tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)} 
                    "owl:AllDifferent" ->  
                        case owlAllDiff tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just fact -> Just (Fc fact)
                                                      Nothing -> Nothing::(Maybe Directive)}

                    "owl:DatatypeProperty" ->  
                        case owlDtProp tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)}
                    "owl:AnnotatonProperty" -> 
                        case owlAnnoProp tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                      Just axiom -> Just (Ax axiom)
                                                      Nothing -> Nothing::(Maybe Directive)}
                    "owl:Thing"             -> 
                        case owlIndividual tree of
                          Result diagRes maybeRes ->
                              Result {diags = diagRes, 
                                      maybeResult = case maybeRes of
                                                         Just fact -> Just (Fc fact)
                                                         Nothing -> Nothing::(Maybe Directive)}

                    _ -> if not ("owl:" == take 4 (tName tagName) && "rdf:" == take 4 (tName tagName))
                            then
                                 case owlIndividual tree of
                                    Result diagRes maybeRes ->
                                       Result {diags = diagRes, 
                                          maybeResult = case maybeRes of
                                                         Just fact -> Just (Fc fact)
                                                         Nothing -> Nothing::(Maybe Directive)}
                            else fatal_error "Node is unknow." nullPos

          _ -> fatal_error "Error" nullPos

dummyAx:: XmlTree -> Result Axiom
dummyAx tree = Result { diags = [], maybeResult = Nothing::(Maybe Axiom)}

dummyFc:: XmlTree -> Result Fact
dummyFc tree = Result { diags = [], maybeResult = Nothing::(Maybe Fact)}

owlClass:: XmlTree -> Result Axiom
owlClass = dummyAx

owlRestriction:: XmlTree -> Result Axiom
owlRestriction = dummyAx

rdfProp:: XmlTree -> Result Axiom -- Result Directive, keine Ahnung, nicht in abs. Struktur
rdfProp = dummyAx

owlObjProp:: XmlTree -> Result Axiom
owlObjProp = dummyAx

owlFuncProp:: XmlTree -> Result Axiom
owlFuncProp = dummyAx

owlInvFuncProp:: XmlTree -> Result Axiom
owlInvFuncProp = dummyAx

owlTransProp:: XmlTree -> Result Axiom
owlTransProp = dummyAx

owlSymmProp:: XmlTree -> Result Axiom
owlSymmProp = dummyAx

rdfDescription:: XmlTree -> Result Axiom
rdfDescription = dummyAx

owlAllDiff:: XmlTree -> Result Fact
owlAllDiff = dummyFc

owlDtProp:: XmlTree -> Result Axiom
owlDtProp = dummyAx

owlAnnoProp:: XmlTree -> Result Axiom
owlAnnoProp = dummyAx

owlIndividual:: XmlTree -> Result Fact
owlIndividual = dummyFc


owl_parserT :: String -> String -> Result XmlTrees
owl_parserT fname fcont =
     let parsedT@(Result ds mtree) = checkErrs (tryP fname fcont)
     in  case mtree of
               Just mt -> let propAndValidT@(Result ds' mtree') = propAndValidateNamespaces $ head mt
                          in  case mtree' of
                                   Just pvt -> Result {diags = ds ++ ds', 
                                                       maybeResult = Just (canonicalizeAllNodes $ head pvt)}
                                   Nothing  -> propAndValidT
               Nothing -> parsedT

-- for test
tryP :: String -> String -> XmlTrees
tryP loc str = 
        parseXmlFromString (do x <- document; return [x]) loc str

tryO :: String -> IO()
tryO fname = do x <- readFile fname
                let Result diagnos mtrees = owl_parserT "TEST" x
                case mtrees of 
                   Just trees -> putStrLn $ show trees
                   Nothing     -> print $ show diagnos

resTrees :: Result XmlTrees -> XmlTrees
resTrees (Result ds mtree) = case mtree of
                                        Just t -> t
                                        Nothing -> error "ds" -- remve warning
               

{-  warum funktioniert nicht? -}
test1 :: FilePath -> IO ()
test1 fp =
    do x <- readFile fp; 
       let Result d o = fromXmlTree $ head $ resTrees $ owl_parserT "Test" x 
       putStrLn (show d)
       case o of 
          Just (onto::Ontology) -> print $ show onto

