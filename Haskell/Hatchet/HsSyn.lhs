% -----------------------------------------------------------------------------
% $Id$
%
% (c) The GHC Team, 1997-2000
%
% A suite of datatypes describing the abstract syntax of Haskell 98.
%
% -----------------------------------------------------------------------------

\begin{code}
module Haskell.Hatchet.HsSyn (
    SrcLoc(..), Module(..), HsQName(..), HsName(..),
    HsModule(..), HsExportSpec(..),
    HsImportDecl(..), HsImportSpec(..), HsAssoc(..),
    HsDecl(..), HsMatch(..), HsConDecl(..), HsBangType(..), HsRhs(..),
    HsGuardedRhs(..), HsQualType(..), HsType(..), HsContext, HsAsst,
    HsLiteral(..), HsExp(..), HsPat(..), HsPatField(..), HsStmt(..),
    HsFieldUpdate(..), HsAlt(..), HsGuardedAlts(..), HsGuardedAlt(..),
    Binding(..), AxiomBndr(..), Quantifier(..), Formula(..), 

    prelude_mod, main_mod, 
    unit_con_name, tuple_con_name,
    unit_con, tuple_con,
    as_name, qualified_name, hiding_name, minus_name, pling_name,
    unit_tycon_name, fun_tycon_name, list_tycon_name, tuple_tycon_name,
    unit_tycon, fun_tycon, list_tycon, tuple_tycon,
  ) where
\end{code}

\begin{code}
data SrcLoc = SrcLoc Int Int -- (Line, Indentation)
  deriving (Eq,Ord,Show)

newtype Module = Module String
  deriving (Eq,Ord,Show)

data HsQName
	= Qual Module HsName
	| UnQual HsName
  deriving (Eq,Ord)

instance Show HsQName where
   showsPrec _ (Qual (Module m) s) = 
	showString m . showString "." . shows s
   showsPrec _ (UnQual s) = shows s

data HsName
	= HsIdent String
	| HsSymbol String
	| HsSpecial String
  deriving (Eq,Ord)

instance Show HsName where
   showsPrec _ (HsIdent s) = showString s
   showsPrec _ (HsSymbol s) = showString s
   showsPrec _ (HsSpecial s) = showString s

data HsModule = HsModule Module (Maybe [HsExportSpec])
                         [HsImportDecl] [HsDecl]
  deriving Show

-- Export/Import Specifications

data HsExportSpec
	 = HsEVar HsQName			-- variable
	 | HsEAbs HsQName			-- T
	 | HsEThingAll HsQName			-- T(..)
	 | HsEThingWith HsQName [HsQName]	-- T(C_1,...,C_n)
	 | HsEModuleContents Module		-- module M   (not for imports)
  deriving (Eq,Show)

data HsImportDecl
	 = HsImportDecl SrcLoc Module Bool (Maybe Module)
	                (Maybe (Bool,[HsImportSpec]))
  deriving (Eq,Show)

data HsImportSpec
	 = HsIVar HsName			-- variable
	 | HsIAbs HsName			-- T
	 | HsIThingAll HsName		-- T(..)
	 | HsIThingWith HsName [HsName]	-- T(C_1,...,C_n)
  deriving (Eq,Show)

data HsAssoc
	 = HsAssocNone
	 | HsAssocLeft
	 | HsAssocRight
  deriving (Eq,Show)

data HsDecl
	 = HsTypeDecl	 SrcLoc HsName [HsName] HsType
	 | HsDataDecl	 SrcLoc HsContext HsName [HsName] [HsConDecl] [HsQName]
	 | HsInfixDecl   SrcLoc HsAssoc Int [HsName]
	 | HsNewTypeDecl SrcLoc HsContext HsName [HsName] HsConDecl [HsQName]
	 | HsClassDecl	 SrcLoc HsQualType [HsDecl]
	 | HsInstDecl	 SrcLoc HsQualType [HsDecl]
	 | HsDefaultDecl SrcLoc HsType
	 | HsTypeSig	 SrcLoc [HsName] HsQualType
	 -- | HsFunBind     SrcLoc [HsMatch]
	 | HsFunBind     [HsMatch]
	 | HsPatBind	 SrcLoc HsPat HsRhs {-where-} [HsDecl]
         | HsAxiomBind Binding
  deriving (Eq,Show)

data HsMatch 
	 = HsMatch SrcLoc HsQName [HsPat] HsRhs {-where-} [HsDecl]
  deriving (Eq,Show)

data HsConDecl
	 = HsConDecl SrcLoc HsName [HsBangType]
	 | HsRecDecl SrcLoc HsName [([HsName],HsBangType)]
  deriving (Eq,Show)

data HsBangType
	 = HsBangedTy   HsType
	 | HsUnBangedTy HsType
  deriving (Eq,Show)

data HsRhs
	 = HsUnGuardedRhs HsExp
	 | HsGuardedRhss  [HsGuardedRhs]
  deriving (Eq,Show)

data HsGuardedRhs
	 = HsGuardedRhs SrcLoc HsExp HsExp
  deriving (Eq,Show)

data HsQualType
	 = HsQualType   HsContext HsType
	 | HsUnQualType HsType
  deriving (Eq,Show)

data HsType
	 = HsTyFun   HsType HsType
	 | HsTyTuple [HsType]
	 | HsTyApp   HsType HsType
	 | HsTyVar   HsName
	 | HsTyCon   HsQName
  deriving (Eq,Show)

type HsContext = [HsAsst]
type HsAsst    = (HsQName,[HsType])	-- for multi-parameter type classes

data HsLiteral
	= HsInt		Integer
	| HsChar	Char
	| HsString	String
	| HsFrac	Rational
	-- GHC unboxed literals:
	| HsCharPrim	Char
	| HsStringPrim	String
	| HsIntPrim	Integer
	| HsFloatPrim	Rational
	| HsDoublePrim	Rational
	-- GHC extension:
	| HsLitLit	String
  deriving (Eq, Show)

data HsExp
	= HsVar HsQName
	| HsCon HsQName
	| HsLit HsLiteral
	| HsInfixApp HsExp HsExp HsExp
	| HsApp HsExp HsExp
	| HsNegApp HsExp
	| HsLambda SrcLoc [HsPat] HsExp               -- SrcLoc added by Bernie, not in distributed code
	| HsLet [HsDecl] HsExp                        -- above needs patch to HsParser.ly
	| HsIf HsExp HsExp HsExp
	| HsCase HsExp [HsAlt]
	| HsDo [HsStmt]
	| HsTuple [HsExp]
	| HsList [HsExp]
	| HsParen HsExp
	| HsLeftSection HsExp HsExp
	| HsRightSection HsExp HsExp
	| HsRecConstr HsQName [HsFieldUpdate]
	| HsRecUpdate HsExp [HsFieldUpdate]
	| HsEnumFrom HsExp
	| HsEnumFromTo HsExp HsExp
	| HsEnumFromThen HsExp HsExp
	| HsEnumFromThenTo HsExp HsExp HsExp
	| HsListComp HsExp [HsStmt]
	| HsExpTypeSig SrcLoc HsExp HsQualType
	| HsAsPat HsName HsExp		-- pattern only
	| HsWildCard			-- ditto
	| HsIrrPat HsExp		-- ditto
	-- HsCCall                         (ghc extension)
	-- HsSCC			   (ghc extension)
 deriving (Eq,Show)

data HsPat
	= HsPVar HsName
	| HsPLit HsLiteral
	| HsPNeg HsPat
	| HsPInfixApp HsPat HsQName HsPat
	| HsPApp HsQName [HsPat]
	| HsPTuple [HsPat]
	| HsPList [HsPat]
	| HsPParen HsPat
	| HsPRec HsQName [HsPatField]
	| HsPAsPat HsName HsPat
	| HsPWildCard
	| HsPIrrPat HsPat
 deriving (Eq,Show)

data HsPatField
	= HsPFieldPat HsQName HsPat
 deriving (Eq,Show)

data HsStmt
	= HsGenerator SrcLoc HsPat HsExp       -- srcloc added by bernie
	| HsQualifier HsExp
	| HsLetStmt [HsDecl]
 deriving (Eq,Show)

data HsFieldUpdate
	= HsFieldUpdate HsQName HsExp
  deriving (Eq,Show)

data HsAlt
	= HsAlt SrcLoc HsPat HsGuardedAlts [HsDecl]
  deriving (Eq,Show)

data HsGuardedAlts
	= HsUnGuardedAlt HsExp
	| HsGuardedAlts  [HsGuardedAlt]
  deriving (Eq,Show)

data HsGuardedAlt
	= HsGuardedAlt SrcLoc HsExp HsExp
  deriving (Eq,Show)

-----------------------------------------------------------------------------
-- Builtin names.

prelude_mod	      = Module "Prelude"
main_mod	      = Module "Main"

unit_con_name	      = Qual prelude_mod (HsSpecial "()")
tuple_con_name i      = Qual prelude_mod (HsSpecial ("("++replicate i ','++")"))

unit_con	      = HsCon unit_con_name
tuple_con i	      = HsCon (tuple_con_name i)

as_name	              = HsIdent "as"
qualified_name        = HsIdent "qualified"
hiding_name	      = HsIdent "hiding"
minus_name	      = HsSymbol "-"
pling_name	      = HsSymbol "!"

unit_tycon_name       = unit_con_name
fun_tycon_name        = Qual prelude_mod (HsSymbol "->")
list_tycon_name       = Qual prelude_mod (HsIdent "[]")
tuple_tycon_name i    = tuple_con_name i

unit_tycon	      = HsTyCon unit_tycon_name
fun_tycon	      = HsTyCon fun_tycon_name
list_tycon	      = HsTyCon list_tycon_name
tuple_tycon i	      = HsTyCon (tuple_tycon_name i)


type AxiomName = String

data Binding
--  = NullBind
  = AndBindings    Binding Binding
  | AxiomDecl      AxiomName Formula
  deriving (Eq,Show)

data AxiomBndr
 = AxiomBndr HsName
 | AxiomBndrSig HsName HsQualType
  deriving (Eq,Show)

data Quantifier
  = AxForall [AxiomBndr]
   | AxExists [AxiomBndr]
   | AxExistsOne [AxiomBndr]
  deriving (Eq,Show)

data Formula
  = AxQuant   Quantifier Formula
  | AxEq      Formula HsExp SrcLoc
  | AxExp     HsExp
  deriving (Eq,Show)

\end{code}
