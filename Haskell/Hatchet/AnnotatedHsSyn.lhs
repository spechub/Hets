\begin{code}
{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 AnnotatedHsSyn

        Description:            Abstract Syntax for Haskell 98 that allows
                                qualified names everywhere. The Annotated
                                Syntax is derived from the Absract Syntax in
                                HsSyn.

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module AnnotatedHsSyn (bogusASrcLoc,
    ASrcLoc(..), AModule(..), AHsName(..), AHsName(..),
    AHsModule(..), AHsExportSpec(..),
    AHsImportDecl(..), AHsImportSpec(..), AHsAssoc(..),
    AHsDecl(..), AHsMatch(..), AHsConDecl(..), AHsBangType(..), AHsRhs(..),
    AHsGuardedRhs(..), AHsQualType(..), AHsType(..), AHsContext, AHsAsst,
    AHsLiteral(..), AHsExp(..), AHsPat(..), AHsPatField(..), AHsStmt(..),
    AHsFieldUpdate(..), AHsAlt(..), AHsGuardedAlts(..), AHsGuardedAlt(..),
    AHsIdentifier(..)
  ) where

\end{code}

\begin{code}

data ASrcLoc = ASrcLoc Int Int -- (Line, Indentation)
  deriving (Eq,Ord,Show)

bogusASrcLoc = ASrcLoc (-1) (-1)

newtype AModule = AModule String
  deriving (Eq,Ord,Show)

-- was HsQName
data AHsName
	= AQual AModule AHsIdentifier 
	| AUnQual AHsIdentifier 
  deriving (Eq,Ord)


instance Show AHsName where
   showsPrec _ (AQual (AModule m) i) = showString m . showString "." . shows i
   showsPrec _ (AUnQual i) = shows i


data AHsIdentifier
     = AHsIdent String
     | AHsSymbol String
     | AHsSpecial String
  -- deriving (Eq,Ord, Show)
  deriving (Eq,Ord)

instance Show AHsIdentifier where
   showsPrec _ (AHsIdent s) = showString s
   showsPrec _ (AHsSymbol s) = showString s
   showsPrec _ (AHsSpecial s) = showString s


data AHsModule = AHsModule AModule (Maybe [AHsExportSpec])
                         [AHsImportDecl] [AHsDecl]
  deriving Show

-- Export/Import Specifications

data AHsExportSpec
	 = AHsEVar AHsName			-- variable
	 | AHsEAbs AHsName			-- T
	 | AHsEThingAll AHsName			-- T(..)
	 | AHsEThingWith AHsName [AHsName]	-- T(C_1,...,C_n)
	 | AHsEModuleContents AModule		-- module M   (not for imports)
  deriving (Eq,Show)

data AHsImportDecl
	 = AHsImportDecl ASrcLoc AModule Bool (Maybe AModule)
	                (Maybe (Bool,[AHsImportSpec]))
  deriving (Eq,Show)

data AHsImportSpec
	 = AHsIVar AHsName			-- variable
	 | AHsIAbs AHsName			-- T
	 | AHsIThingAll AHsName		-- T(..)
	 | AHsIThingWith AHsName [AHsName]	-- T(C_1,...,C_n)
  deriving (Eq,Show)

data AHsAssoc
	 = AHsAssocNone
	 | AHsAssocLeft
	 | AHsAssocRight
  deriving (Eq,Show)

data AHsDecl 
	 = AHsTypeDecl	  ASrcLoc AHsName [AHsName] AHsType
	 | AHsDataDecl	  ASrcLoc AHsContext AHsName [AHsName] [AHsConDecl] [AHsName]
	 | AHsInfixDecl   ASrcLoc AHsAssoc Int [AHsName]
	 | AHsNewTypeDecl ASrcLoc AHsContext AHsName [AHsName] AHsConDecl [AHsName]
	 | AHsClassDecl	  ASrcLoc AHsQualType [AHsDecl]
	 | AHsInstDecl	  ASrcLoc AHsQualType [AHsDecl]
	 | AHsDefaultDecl ASrcLoc AHsType
	 | AHsTypeSig	  ASrcLoc [AHsName] AHsQualType
	 -- | AHsFunBind     ASrcLoc [AHsMatch]
	 | AHsFunBind     [AHsMatch]
	 | AHsPatBind	  ASrcLoc AHsPat AHsRhs {-where-} [AHsDecl]
  deriving (Eq,Show)
  
  -- WARNING: don't get rid of derive show without checking in MultiModuleBasics
  -- whether it's still used (just grep for a "WARNING" there)

data AHsMatch
	 = AHsMatch ASrcLoc AHsName [AHsPat] (AHsRhs) {-where-} [AHsDecl]
  deriving (Eq,Show)

data AHsConDecl
	 = AHsConDecl ASrcLoc AHsName [AHsBangType]
	 | AHsRecDecl ASrcLoc AHsName [([AHsName],AHsBangType)]
  deriving (Eq,Show)

data AHsBangType
	 = AHsBangedTy   AHsType
	 | AHsUnBangedTy AHsType
  deriving (Eq,Show)

data AHsRhs
	 = AHsUnGuardedRhs (AHsExp)
	 | AHsGuardedRhss  [AHsGuardedRhs]
  deriving (Eq,Show)

data AHsGuardedRhs
	 = AHsGuardedRhs ASrcLoc (AHsExp) (AHsExp)
  deriving (Eq,Show)

data AHsQualType
	 = AHsQualType   AHsContext AHsType
	 | AHsUnQualType AHsType
  deriving (Eq,Show)

data AHsType
	 = AHsTyFun   AHsType AHsType
	 | AHsTyTuple [AHsType]
	 | AHsTyApp   AHsType AHsType
	 | AHsTyVar   AHsName
	 | AHsTyCon   AHsName
  deriving (Eq,Show)

type AHsContext = [AHsAsst]
-- type AHsAsst    = (AHsName,[AHsType])	-- for multi-parameter type classes
type AHsAsst    = (AHsName,AHsName)	-- clobber multi-param type classes for the moment 

data AHsLiteral
	= AHsInt		Integer
	| AHsChar	Char
	| AHsString	String
	| AHsFrac	Rational
	-- GHC unboxed literals:
	| AHsCharPrim	Char
	| AHsStringPrim	String
	| AHsIntPrim	Integer
	| AHsFloatPrim	Rational
	| AHsDoublePrim	Rational
	-- GHC extension:
	| AHsLitLit	String
  deriving (Eq, Show)

data AHsExp
	-- = AHsVar AHsName (Maybe ())       -- we might want to annotate occurences of variables
	= AHsVar AHsName 
	| AHsCon AHsName
	| AHsLit AHsLiteral
	| AHsInfixApp (AHsExp) (AHsExp) (AHsExp)
	| AHsApp (AHsExp) (AHsExp)
	| AHsNegApp (AHsExp)
	| AHsLambda ASrcLoc [AHsPat] (AHsExp)               
	| AHsLet [AHsDecl] (AHsExp)                    
	| AHsIf (AHsExp) (AHsExp) (AHsExp)
	| AHsCase (AHsExp) [AHsAlt]
	| AHsDo [AHsStmt]
	| AHsTuple [AHsExp]
	| AHsList [AHsExp]
	| AHsParen (AHsExp)
	| AHsLeftSection (AHsExp) (AHsExp)
	| AHsRightSection (AHsExp) (AHsExp)
	| AHsRecConstr AHsName [AHsFieldUpdate]
	| AHsRecUpdate (AHsExp) [AHsFieldUpdate]
	| AHsEnumFrom (AHsExp)
	| AHsEnumFromTo (AHsExp) (AHsExp)
	| AHsEnumFromThen (AHsExp) (AHsExp)
	| AHsEnumFromThenTo (AHsExp) (AHsExp) (AHsExp)
	| AHsListComp (AHsExp) [AHsStmt]
	| AHsExpTypeSig ASrcLoc (AHsExp) AHsQualType
	| AHsAsPat AHsName (AHsExp)		-- pattern only
	| AHsWildCard			-- ditto
	| AHsIrrPat (AHsExp)		-- ditto
	-- AHsCCall                         (ghc extension)
	-- AHsSCC			   (ghc extension)
 deriving (Eq,Show)

data AHsPat
	= AHsPVar AHsName
	| AHsPLit AHsLiteral
	| AHsPNeg AHsPat
	| AHsPInfixApp AHsPat AHsName AHsPat
	| AHsPApp AHsName [AHsPat]
	| AHsPTuple [AHsPat]
	| AHsPList [AHsPat]
	| AHsPParen AHsPat
	| AHsPRec AHsName [AHsPatField]
	| AHsPAsPat AHsName AHsPat
	| AHsPWildCard
	| AHsPIrrPat AHsPat
 deriving (Eq,Show)

data AHsPatField
	= AHsPFieldPat AHsName AHsPat
 deriving (Eq,Show)

data AHsStmt
	= AHsGenerator ASrcLoc AHsPat (AHsExp)
	| AHsQualifier (AHsExp)
	| AHsLetStmt [AHsDecl]
 deriving (Eq,Show)

data AHsFieldUpdate
	= AHsFieldUpdate AHsName (AHsExp)
  deriving (Eq,Show)

data AHsAlt
	= AHsAlt ASrcLoc AHsPat (AHsGuardedAlts) [AHsDecl]
  deriving (Eq,Show)

data AHsGuardedAlts
	= AHsUnGuardedAlt (AHsExp)
	| AHsGuardedAlts  [AHsGuardedAlt]
  deriving (Eq,Show)

data AHsGuardedAlt
	= AHsGuardedAlt ASrcLoc (AHsExp) (AHsExp)
  deriving (Eq,Show)

-----------------------------------------------------------------------------
\end{code}
