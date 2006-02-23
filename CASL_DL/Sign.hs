{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

Signatures for DL logics, as extension of CASL signatures.
-}

{- 
  todo:
  - emptySign should be filled with predefined Datatypes bootstrapped 
    from CASL_DL/Datatypes.het (via ATerm reading?)
    and with sort Thing and pred Nothing.
-}

module CASL_DL.Sign where

import qualified Common.Lib.Map as Map
import Common.Id
import Common.Utils
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PrintLaTeX

import CASL.AS_Basic_CASL
import CASL_DL.AS_CASL_DL

import Data.List
import OWL_DL.AS (QName)          
import OWL_DL.ReadWrite ()

data CASL_DLSign = 
    CASL_DLSign { annoProperties  :: Map.Map SIMPLE_ID PropertyType
                , annoPopertySens :: [AnnoAppl]
                } deriving (Show, Eq)

data PropertyType = AnnoProperty
                  | OntoProperty deriving (Show,Eq)

data AnnoAppl = AnnoAppl SIMPLE_ID Id AnnoLiteral 
              deriving (Show,Eq)

data AnnoLiteral = AL_Term (TERM DL_FORMULA)
                 | AL_URI  QName
                 | AL_Id   Id
              deriving (Show,Eq)

emptyCASL_DLSign :: CASL_DLSign
emptyCASL_DLSign = CASL_DLSign Map.empty []

addCASL_DLSign :: CASL_DLSign -> CASL_DLSign -> CASL_DLSign
addCASL_DLSign a b = a
     { annoProperties = 
           Map.unionWithKey (throwAnnoError "CASL_DL.Sign.addCASL_DLSign:") 
                  (annoProperties a) (annoProperties b)
     , annoPopertySens = union (annoPopertySens a) (annoPopertySens b)
     } 

throwAnnoError :: String -> SIMPLE_ID 
               -> PropertyType -> PropertyType -> PropertyType
throwAnnoError s k e1 e2 = 
    if e1 == e2 
       then e1
       else error (s++" Annotation Properties and Ontology Properties \
                          \must have distinct names! ("++show k++")")

diffCASL_DLSign :: CASL_DLSign -> CASL_DLSign -> CASL_DLSign
diffCASL_DLSign a b = a
     { annoProperties = Map.difference (annoProperties a) (annoProperties b)
     , annoPopertySens = (annoPopertySens a) \\ (annoPopertySens b)
     }

isSubCASL_DLSign :: CASL_DLSign -> CASL_DLSign -> Bool
isSubCASL_DLSign a b = 
    Map.isSubmapOf (annoProperties a) (annoProperties b) &&
    (annoPopertySens a `isSublistOf` annoPopertySens b)

instance PrettyPrint CASL_DLSign where
    printText0 _ = text . show

instance PrintLaTeX CASL_DLSign where
    printLatex0 = printText0
