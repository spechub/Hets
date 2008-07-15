{- |
Module      :  $Header$
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach,
  Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Printing abstract syntax of Isabelle Proofs
-}

module Isabelle.IsaProofPrint where

import Common.Doc
import Common.DocUtils
import Isabelle.IsaConsts
import Isabelle.IsaProof

instance Pretty IsaProof where
    pretty = printIsaProof

printIsaProof :: IsaProof -> Doc
printIsaProof (IsaProof p e) = fsep $ map pretty p ++ [pretty e]

instance Pretty ProofCommand where
    pretty = printProofCommand

printProofCommand :: ProofCommand -> Doc
printProofCommand pc =
    case pc of
      Apply pm -> text applyS <+> pretty pm
      Using ls -> text usingS <+> fsep (map text ls)
      Back -> text backS
      Defer x -> text deferS <+> pretty x
      Prefer x -> text preferS <+> pretty x
      Refute -> text refuteS

instance Pretty ProofEnd where
    pretty = printProofEnd

printProofEnd :: ProofEnd -> Doc
printProofEnd pe =
    case pe of
      By pm -> text byS <+> pretty pm
      DotDot -> text dotDot
      Done -> text doneS
      Oops -> text oopsS
      Sorry -> text sorryS

instance Pretty ProofMethod where
    pretty = printProofMethod

printProofMethod :: ProofMethod -> Doc
printProofMethod pm =
    case pm of
      Auto -> text autoS
      Simp -> text simpS
      Induct var -> parens $ (text inductS) <+> doubleQuotes (text var)
      CaseTac t -> text caseTacS <+> doubleQuotes (text t)
      SubgoalTac t -> text subgoalTacS <+> doubleQuotes (text t)
      Insert t -> text insertS <+> text t
      Other s -> parens $ text s
