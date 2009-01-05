{- |
Module      :  $Header$
Description : Constants for the translation of processes from CspCASL
              to IsabelleHOL (CspProver)
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Constants for the translation of processes from CspCASL to IsabelleHOL
(CspProver)

-}

module CspCASL.Trans_Consts where

import CASL.AS_Basic_CASL
import CspCASL.AS_CspCASL_Process (PROCESS_NAME)
import Isabelle.IsaConsts
import Isabelle.IsaSign
import Isabelle.Translate(showIsaTypeT)

-- Name for the PreAlphabet
preAlphabetS :: String
preAlphabetS = "PreAlphabet"

-- Type for the PreAlphabet
preAlphabetType :: Typ
preAlphabetType = Type {typeId = preAlphabetS,
                        typeSort = [],
                        typeArgs =[]}

-- Name for the Alphabet
alphabetS :: String
alphabetS = "Alphabet"

-- Type for the Alphabet
alphabetType :: Typ
alphabetType = Type {typeId = alphabetS,
                     typeSort = [],
                     typeArgs =[]}

-- Name for IsabelleHOL quot type
quotS :: String
quotS = "quot"

-- Type for preAlphabet quot
preAlphabetQuotType :: Typ
preAlphabetQuotType = Type {typeId = quotS,
                            typeSort = [],
                            typeArgs =[preAlphabetType]}

-- Name for the datatype of process names
procNameS :: String
procNameS = "ProcName"

-- Type for the datatype of process names
procNameType :: Typ
procNameType = Type {typeId = procNameS,
                     typeSort = [],
                     typeArgs =[]}

-- name for CspProvers ('pn, 'a) proc type
procS :: String
procS = "proc"

-- Type for (ProcName,Alpahbet) proc
cCProverProcType :: Typ
cCProverProcType = Type {typeId = procS,
                         typeSort = [],
                         typeArgs =[procNameType, alphabetType]}

-- Name for the function for mapping process names to real processes
procMapS :: String
procMapS = "ProcMap"

-- Type for the function for mapping process names to real processes
procMapType :: Typ
procMapType = mkFunType procNameType cCProverProcType

barExtS :: String
barExtS = "_Bar"

baseSign :: BaseSig
baseSign = Main_thy

classS :: String
classS = "class"

classOp :: Term -> Term
classOp = termAppl (conDouble classS)

-- Convert a SORT to a string
convertSort2String :: SORT -> String
convertSort2String s = showIsaTypeT s baseSign

convertProcessName2String :: PROCESS_NAME -> String
convertProcessName2String pn = (show pn)
