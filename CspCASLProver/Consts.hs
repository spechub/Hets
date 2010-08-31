{- |
Module      :  $Header$
Description :  Constants and related fucntions for CspCASLProver
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Constants and related fucntions for CspCASLProver.

-}

module CspCASLProver.Consts
    ( alphabetS
    , alphabetType
    , binEq_PreAlphabet
    , classOp
    , classS
    , convertChannelString
    , convertProcessName2String
    , convertSort2String
    , cspFThyS
    , eq_PreAlphabetS
    , eq_PreAlphabetV
    , equivTypeClassS
    , eventS
    , eventType
    , flatS
    , flatOp
    , preAlphabetQuotType
    , preAlphabetS
    , preAlphabetSimS
    , preAlphabetType
    , projFlatS
    , projFlatOp
    , lemmasCCProverDecompositionThmsS
    , lemmasCCProverInjectivityThmsS
    , lemmasEmbInjAxS
    , lemmasIdentityAxS
    , lemmasNotDefBotAxS
    , lemmasTotalityAxS
    , lemmasTransAxS
    , mkChooseFunName
    , mkChooseFunOp
    , mkCompareWithFunName
    , mkPreAlphabetConstructor
    , mkPreAlphabetConstructorOp
    , mkProcNameConstructor
    , mkSortBarAbsString
    , mkSortBarAbsOp
    , mkSortBarRepOp
    , mkSortBarString
    , mkSortBarType
    , mkSortFlatString
    , mkThyNameAlphabet
    , mkThyNameDataEnc
    , mkThyNameIntThms
    , mkThyNamePreAlphabet
    , procMapS
    , procMapType
    , procNameType
    , quotEqualityS
    , quotientThyS
    , reflexivityTheoremS
    , symmetryTheoremS
    , transitivityS
    ) where

import CASL.AS_Basic_CASL (SORT)
import CspCASL.AS_CspCASL_Process (CHANNEL_NAME, PROCESS_NAME)
import Isabelle.IsaConsts (binVNameAppl, conDouble, mkFunType, termAppl)
import Isabelle.IsaSign (BaseSig(..), Term, Typ(..), VName(..))
import Isabelle.Translate(showIsaTypeT, transString)

-- | Name for the CspCASLProver's Alphabet
alphabetS :: String
alphabetS = "Alphabet"

-- | Type for the CspCASLProver's Alphabet
alphabetType :: Typ
alphabetType = Type {typeId = alphabetS,
                     typeSort = [],
                     typeArgs =[]}

-- | String for the name extension of CspCASLProver's bar types
barExtS :: String
barExtS = "_Bar"

-- | Isabelle fucntion to compare eqaulity of two elements of the
--   PreAlphabet.
binEq_PreAlphabet :: Term -> Term -> Term
binEq_PreAlphabet = binVNameAppl eq_PreAlphabetV

-- | Type for (ProcName,Alpahbet) proc
cCProverProcType :: Typ
cCProverProcType = Type {typeId = procS,
                         typeSort = [],
                         typeArgs =[procNameType, eventType]}

-- | Isabelle operation for the class operation
classOp :: Term -> Term
classOp = termAppl (conDouble classS)

-- | String for the class operation
classS :: String
classS = "class"

-- | Function that takes a channel name produces the
--   CspCASLProver's constructor for that channel.
convertChannelString :: CHANNEL_NAME -> String
convertChannelString = show

-- | Convert a SORT to a string
convertSort2String :: SORT -> String
convertSort2String s = transString $ showIsaTypeT s Main_thy

-- | Convert a process name to a string
convertProcessName2String :: PROCESS_NAME -> String
convertProcessName2String = show

-- |  Theory file name for CSP_F of CSP-Prover
cspFThyS :: String
cspFThyS  = "CSP_F"

-- | String of the name of the function to compare eqaulity of two
--   elements of the PreAlphabet.
eq_PreAlphabetS :: String
eq_PreAlphabetS = "eq_PreAlphabet"

-- | VName of the name of the function to compare eqaulity of two
--   elements of the PreAlphabet.
eq_PreAlphabetV :: VName
eq_PreAlphabetV   = VName eq_PreAlphabetS $ Nothing

-- | String for the name of the axiomatic type class of equivalence
--   relations part 2
equivTypeClassS :: String
equivTypeClassS  = "equiv"

-- | String of the name of CspCASLProver's Event datatype.
eventS :: String
eventS = "Event"

-- | Type for the CspCASLProver's Event datatype
eventType :: Typ
eventType = Type {typeId = eventS,
                  typeSort = [],
                  typeArgs =[]}

-- | String of the name of constructor for a plain event without a channel,
--   effectivly this is the channel whos name is Flat. Also used for the names
--   of the flat types.
flatS :: String
flatS = "Flat"

-- | Function that takes a Term and adds a flat around it
flatOp :: Term -> Term
flatOp = termAppl (conDouble flatS)

-- |Name for the lemma which is the collection of our decomposition axioms that
--  we produce.
lemmasCCProverDecompositionThmsS :: String
lemmasCCProverDecompositionThmsS = "ccproverDecompositionAxs"

-- |Name for the lemma which is the collection of our injectivity axioms that we
--  produce.
lemmasCCProverInjectivityThmsS :: String
lemmasCCProverInjectivityThmsS = "ccproverInjectivityThms"

-- | Name for the lemma which is the collection of embedding injectivity axioms.
lemmasEmbInjAxS :: String
lemmasEmbInjAxS = "allGaEmbInjAx"

-- | Name for the lemma which is the collection of identity axioms.
lemmasIdentityAxS :: String
lemmasIdentityAxS = "allGaIdentityAx"

-- | Name for the lemma which is the collection of not defined bottom axioms.
lemmasNotDefBotAxS :: String
lemmasNotDefBotAxS  = "allGaNotDefBotAx"

-- | Name for the lemma which is the collection of totality axioms.
lemmasTotalityAxS :: String
lemmasTotalityAxS = "allGaTotAx"

-- | Name for the lemma which is the collection of transitivity axioms.
lemmasTransAxS :: String
lemmasTransAxS = "allGaTransAx"

-- | Function that takes a sort and outputs the function name for the
--   corresponing choose function
mkChooseFunName :: SORT -> String
mkChooseFunName sort = ("choose_" ++ (mkPreAlphabetConstructor sort))

-- | Function that takes a sort and outputs the Isabelle function for the
--   corresponing choose function
mkChooseFunOp :: SORT -> Term -> Term
mkChooseFunOp s = termAppl (conDouble (mkChooseFunName s))

-- | Function that takes a sort and outputs the function name for the
--   corresponing compare_with function
mkCompareWithFunName :: SORT -> String
mkCompareWithFunName sort = ("compare_with_" ++ (mkPreAlphabetConstructor sort))

-- | Function that returns the constructor of PreAlphabet for a given
--   sort
mkPreAlphabetConstructor :: SORT -> String
mkPreAlphabetConstructor sort = "C_" ++ (convertSort2String sort)

-- | Function that returns the (Isabelle function for the) constructor of
--   PreAlphabet for a given sort
mkPreAlphabetConstructorOp :: SORT -> Term -> Term
mkPreAlphabetConstructorOp s = termAppl (conDouble (mkPreAlphabetConstructor s))

-- | Given a process name this fucntion returns a unique constructor for that
--   process name. This is a helper functin when buildign the process name data
--   type.
mkProcNameConstructor :: PROCESS_NAME -> String
mkProcNameConstructor pn = show pn

-- | Converts a sort in to the corresponding bar sort represented as a
-- string
mkSortBarString :: SORT -> String
mkSortBarString s = convertSort2String s ++ barExtS

-- | Converts a sort in to the corresponding bar sort type
mkSortBarType :: SORT -> Typ
mkSortBarType sort = Type {typeId = (mkSortBarString sort), typeSort = [], typeArgs =[]}

-- | Given a sort this function produces the function name (string) of the built
--   in Isabelle fucntion that corresponds to the abstraction function of the
--   type that sort_bar.
mkSortBarAbsString :: SORT -> String
mkSortBarAbsString s = "Abs_" ++ convertSort2String s ++ barExtS

-- | Given a sort this function produces the a function on the abstract syntax
--   of Isabelle that represents the built in Isabelle fucntion that corresponds
--   to the abstraction function of the type sort_bar.
mkSortBarAbsOp :: SORT -> Term -> Term
mkSortBarAbsOp s = termAppl (conDouble (mkSortBarAbsString s))

-- | Given a sort this function produces the function name (string) of the built
--   in Isabelle fucntion that corresponds to the representation function of the
--   type sort_bar.
mkSortBarRepString :: SORT -> String
mkSortBarRepString s = "Rep_" ++ convertSort2String s ++ barExtS

-- | Given a sort this function produces the a function on the abstract syntax
--   of Isabelle that represents the built in Isabelle fucntion that corresponds
--   to the representation function of the type sort_bar.
mkSortBarRepOp :: SORT -> Term -> Term
mkSortBarRepOp s = termAppl (conDouble (mkSortBarRepString s))

-- | Converts asort in to the corresponding flat type for that sort represented
-- as a string. This is used in the construction of the channels and is linked
-- with the type event.
mkSortFlatString :: SORT -> String
mkSortFlatString s = (convertSort2String s) ++ "_" ++ flatS

-- | Created a name for the theory file which stores the alphabet
--   construction for CspCASLProver.
mkThyNameAlphabet :: String -> String
mkThyNameAlphabet thName = thName ++ "_alphabet"

-- | Created a name for the theory file which stores the data encoding
--   for CspCASLProver.
mkThyNameDataEnc :: String -> String
mkThyNameDataEnc thName = thName ++ "_dataenc"

-- | Created a name for the theory file which stores the Alphabet
--   construction and instances code for CspCASLProver.
mkThyNamePreAlphabet :: String -> String
mkThyNamePreAlphabet thName = thName ++ "_prealphabet"

-- | Created a name for the theory file which stores the Integration
--   Theorems for CspCASLProver.
mkThyNameIntThms :: String -> String
mkThyNameIntThms thName = thName ++ "_integrationThms"

-- | Type for CspCASLProver's preAlphabet quot
preAlphabetQuotType :: Typ
preAlphabetQuotType = Type {typeId = quotS,
                            typeSort = [],
                            typeArgs =[preAlphabetType]}

-- | Name for CspCASLProver's PreAlphabet
preAlphabetS :: String
preAlphabetS = "PreAlphabet"

preAlphabetSimS :: String
preAlphabetSimS = "preAlphabet_sim"

-- | Type for CspCASLProver's PreAlphabet
preAlphabetType :: Typ
preAlphabetType = Type {typeId = preAlphabetS,
                        typeSort = [],
                        typeArgs =[]}

-- | Name for CspCASLProver's function for mapping process names to
--   actual processes
procMapS :: String
procMapS = "ProcMap"

-- | Type for CspCASLProver's function for mapping process names to
--   actual processes
procMapType :: Typ
procMapType = mkFunType procNameType cCProverProcType

-- | Name for CspCASLProver's datatype of process names
procNameS :: String
procNameS = "ProcName"

-- | Type for CspCASLProver's datatype of process names
procNameType :: Typ
procNameType = Type {typeId = procNameS,
                     typeSort = [],
                     typeArgs =[]}

-- | Name for CspProver's ('pn, 'a) proc type
procS :: String
procS = "proc"

-- | Name of CspCASLProver's function for projecting a Flat Event back to the
--   type Alphabet
projFlatS :: String
projFlatS = "projFlat"

-- | Apply the CspCASLProvers projFlat function to an isabelle term
projFlatOp :: Term -> Term
projFlatOp = termAppl (conDouble projFlatS)

-- | Name for IsabelleHOL quot type
quotS :: String
quotS = "quot"

quotEqualityS :: String
quotEqualityS = "quot_equality"

quotientThyS :: String
quotientThyS = "Quotient"

reflexivityTheoremS :: String
reflexivityTheoremS = "eq_refl"

symmetryTheoremS :: String
symmetryTheoremS = "eq_symm"

transitivityS :: String
transitivityS = "eq_trans"
