{- |
Module      :  $Header$
Description :  abstract syntax of VSE programs and dynamic logic
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

CASL extention to VSE programs and dynamic logic
as described on page 4-7 (Sec 2.3.1, 2.5.2, 2.5.4, 2.6) of
Bruno Langenstein's API description
-}

module VSE.As where

import Data.Char
import qualified Data.Map as Map
import Control.Monad (foldM)

import Common.AS_Annotation
import Common.Id
import Common.Doc
import Common.DocUtils
import Common.Result
import Common.LibName
import Common.Utils (number)

import CASL.AS_Basic_CASL
import CASL.ToDoc

-- | input or output procedure parameter kind
data Paramkind = In | Out deriving (Show, Eq, Ord)

-- | a procedure parameter
data Procparam = Procparam Paramkind SORT deriving (Show, Eq, Ord)

-- | procedure or function declaration
data Profile = Profile [Procparam] (Maybe SORT) deriving (Show, Eq, Ord)

-- | further VSE signature entries
data Sigentry = Procedure Id Profile Range deriving (Show, Eq)

data Procdecls = Procdecls [Annoted Sigentry] Range deriving (Show, Eq)

instance GetRange Procdecls where
  getRange (Procdecls _ r) = r

-- | wrapper for positions
data Ranged a = Ranged { unRanged :: a, range :: Range }
  deriving (Show, Eq, Ord)

-- | attach a nullRange
mkRanged :: a -> Ranged a
mkRanged a = Ranged a nullRange

-- | programs with ranges
type Program = Ranged PlainProgram

-- | programs based on restricted terms and formulas
data PlainProgram =
    Abort
  | Skip
  | Assign VAR (TERM ())
  | Call (FORMULA ()) -- ^ a procedure call as predication
  | Return (TERM ())
  | Block [VAR_DECL] Program
  | Seq Program Program
  | If (FORMULA ()) Program Program
  | While (FORMULA ()) Program
    deriving (Show, Eq, Ord)

-- | alternative variable declaration
data VarDecl = VarDecl VAR SORT (Maybe (TERM ())) Range deriving Show

toVarDecl :: [VAR_DECL] -> [VarDecl]
toVarDecl = concatMap
  (\ (Var_decl vs s r) -> map (\ v -> VarDecl v s Nothing r) vs)

addInits :: [VarDecl] -> Program -> ([VarDecl], Program)
addInits vs p = case vs of
  vd@(VarDecl v s Nothing z) : r -> case unRanged p of
      Seq (Ranged (Assign av t) _) p2 | v == av
          -> let (rs, q) = addInits r p2
             in (VarDecl v s (Just t) z : rs, q)
      _ -> let (rs, q) = addInits r p
           in (vd : rs, q)
  _ -> (vs, p)

-- | extend CASL formulas by box or diamond formulas and defprocs
data VSEforms =
    Dlformula BoxOrDiamond Program Sentence
  | Defprocs [Defproc]
  | RestrictedConstraint [Constraint] (Map.Map SORT Id) Bool
    deriving (Show, Eq, Ord)

type Dlformula = Ranged VSEforms
type Sentence = FORMULA Dlformula

-- | box or diamond indicator
data BoxOrDiamond = Box | Diamond deriving (Show, Eq, Ord)

data ProcKind = Proc | Func deriving (Show, Eq, Ord)

-- | procedure definitions as basic items becoming sentences
data Defproc = Defproc ProcKind Id [VAR] Program Range deriving (Show, Eq, Ord)

data Procs = Procs { procsMap :: Map.Map Id Profile } deriving (Show, Eq, Ord)

emptyProcs :: Procs
emptyProcs = Procs Map.empty

unionProcs :: Procs -> Procs -> Result Procs
unionProcs (Procs m1) (Procs m2) = fmap Procs $
  foldM (\ m (k, v) -> case Map.lookup k m1 of
    Nothing -> return $ Map.insert k v m
    Just w -> if w == v then return m else
      mkError "different union profiles for" k)
  m1 $ Map.toList m2

interProcs :: Procs -> Procs -> Result Procs
interProcs (Procs m1) (Procs m2) = fmap Procs $
  foldM (\ m (k, v) -> case Map.lookup k m1 of
    Nothing -> return m
    Just w -> if w == v then return $ Map.insert k v m else
      mkError "different intersection profiles for" k)
    Map.empty $ Map.toList m2

diffProcs :: Procs -> Procs -> Procs
diffProcs (Procs m1) (Procs m2) = Procs $ Map.difference m1 m2

isSubProcsMap :: Procs -> Procs -> Bool
isSubProcsMap (Procs m1) (Procs m2) = Map.isSubmapOfBy (==) m1 m2

-- * Pretty instances

instance Pretty Profile where
  pretty (Profile ps ores) = fsep
    [ ppWithCommas ps
    , case ores of
        Nothing -> empty
        Just s -> funArrow <+> idDoc s]

instance Pretty Sigentry where
  pretty (Procedure i p _) = fsep [idDoc i, colon <+> pretty p]

instance Pretty Procdecls where
  pretty (Procdecls l _) = if null l then empty else fsep
   [ text $ "PROCEDURE" ++ case l of
        [_] -> ""
        _ -> "S"
   , semiAnnos pretty l ]

instance Pretty Procparam where
  pretty (Procparam m s) = text (map toUpper $ show m) <+> idDoc s

block :: Doc -> Doc
block d = sep [text "BEGIN", d, text "END"]

prettyProcKind :: ProcKind -> Doc
prettyProcKind k = text $ case k of
  Proc -> "PROCEDURE"
  Func -> "FUNCTION"

assign :: Doc
assign = text ":="

instance Pretty Defproc where
  pretty (Defproc pk p ps pr _) = vcat
    [ prettyProcKind pk <+> idDoc p <> parens (ppWithCommas ps)
    , pretty pr ]

instance Pretty a => Pretty (Ranged a) where
  pretty (Ranged a _) = pretty a

instance GetRange (Ranged a) where
  getRange (Ranged _ r) = r

instance FormExtension a => FormExtension (Ranged a) where
  isQuantifierLike (Ranged a _) = isQuantifierLike a

instance Pretty VarDecl where
  pretty (VarDecl v s mt _) =
      sidDoc v <+> colon <+> idDoc s <+> case mt of
      Nothing -> empty
      Just t -> assign <+> pretty t

instance Pretty PlainProgram where
  pretty prg = case prg of
    Abort -> text "ABORT"
    Skip -> text "SKIP"
    Assign v t -> pretty v <+> assign <+> pretty t
    Call f -> pretty f
    Return t -> text "RETURN" <+> pretty t
    Block vs p -> if null vs then block $ pretty p else
      let (vds, q) = addInits (toVarDecl vs) p
      in sep [ text "DECLARE"
             , ppWithCommas vds <> semi
             , pretty q ]
    Seq p1 p2 -> vcat [pretty p1 <> semi, pretty p2]
    If f t e -> sep
      [ text "IF" <+> pretty f
      , text "THEN" <+> pretty t
      , case e of
          Ranged Skip _ -> empty
          _ -> text "ELSE" <+> pretty e
      , text "FI" ]
    While f p -> sep
      [ text "WHILE" <+> pretty f
      , text "DO" <+> pretty p
      , text "OD" ]

instance FormExtension VSEforms

instance GetRange VSEforms

instance Pretty VSEforms where
  pretty v = case v of
    Dlformula b p f -> let d = pretty p in sep
      [ case b of
         Box -> text "[:" <> d <> text ":]"
         Diamond -> text "<:" <> d <> text ":>"
      , pretty f ]
    Defprocs ps -> prettyProcdefs ps
    RestrictedConstraint constrs restr _b ->
       let l = recoverType constrs
       in fsep [ text "true %[generated type"
               , semiAnnos (printRestrTypedecl restr) l
               , text "]%"]

genSortName :: String -> SORT -> Id
genSortName str s@(Id ts cs ps) = case cs of
  [] -> genName $ str ++ show s
  i : r | isQualName s -> Id ts (genSortName str i : r) ps
  _ -> Id [genToken $ str ++ show (Id ts [] ps)] cs ps

{- since such names are generated out of sentences, the qualification
   of the sort may be misleading -}
gnUniformName :: SORT -> Id
gnUniformName = genSortName "uniform_" . unQualName

gnRestrName :: SORT -> Id
gnRestrName = genSortName "restr_"

gnEqName :: SORT -> Id
gnEqName = genSortName "eq_"

genVars :: [SORT] -> [(Token, SORT)]
genVars = map (\ (t, n) -> (genNumVar "x" n, t)) . number

xVar :: Token
xVar = genToken "x"

yVar :: Token
yVar = genToken "y"

printRestrTypedecl :: Map.Map SORT Id -> DATATYPE_DECL -> Doc
printRestrTypedecl restr (Datatype_decl s a r) =
    let pa = printAnnoted printALTERNATIVE in case a of
    [] -> printRestrTypedecl restr
           (Datatype_decl s [emptyAnno $ Subsorts [s] r] r)
    h : t -> sep [idLabelDoc s, colon <> colon <> sep
                      ((equals <+> pa h) :
                       map ((bar <+>) . pa) t), text "restricted by",
                   pretty $ Map.findWithDefault (gnRestrName s) s restr]

prettyProcdefs :: [Defproc] -> Doc
prettyProcdefs ps = vcat
  [ text "DEFPROCS"
  , vsep . punctuate semi $ map pretty ps
  , text "DEFPROCSEND" ]

instance Pretty Procs where
  pretty (Procs m) =
    pretty $ Procdecls
       (map (\ (i, p) -> emptyAnno $ Procedure i p nullRange) $ Map.toList m)
       nullRange
