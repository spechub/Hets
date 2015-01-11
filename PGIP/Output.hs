module PGIP.Output
  ( textC
  , xmlC
  , jsonC
  , pdfC
  , dotC
  , svgC
  , htmlC
  , formatProofs
  , ProofResult
  ) where

import Logic.Prover
import Proofs.AbstractState (G_proof_tree)

textC :: String
textC = "text/plain"

xmlC :: String
xmlC = "application/xml"

jsonC :: String
jsonC = "application/json"

pdfC :: String
pdfC = "application/pdf"

dotC :: String
dotC = "text/vnd.graphviz"

svgC :: String
svgC = "image/svg+xml"

htmlC :: String
htmlC = "text/html"

type ProofResult = (String, String, String, Maybe (ProofStatus G_proof_tree))
type ProofFormatter = [(String, [ProofResult])] -> (String, String)
                   -- ^[(dgNodeName, result)]      ^(responseType, response)

formatProofs :: Maybe String -> ProofFormatter
formatProofs format ps = case format of
  Just "json" -> formatAsJSON ps
  _ -> formatAsXML ps
  where
  formatAsJSON :: ProofFormatter
  formatAsJSON proofs = (jsonC, undefined)

  formatAsXML :: ProofFormatter
  formatAsXML proofs = (xmlC, undefined)
