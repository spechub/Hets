{- |
Module      :  $Header$
Description :  abstract syntax of VSE programs and dynamic logic
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

CASL extention to VSE programs and dynamic logic
as described on page 4-7 (Sec 2.3.1, 2.5.2, 2.5.4, 2.6) of
Bruno Langenstein's API description
-}

module VSE.As where

import Data.Char
import Common.AS_Annotation
import Common.Id
import Common.Doc
import Common.DocUtils
import CASL.AS_Basic_CASL
import CASL.ToDoc (isJunct)

-- | input or output procedure parameter kind
data Paramkind = In | Out deriving (Show, Eq, Ord)

-- | a procedure parameter
data Procparam = Procparam Paramkind SORT deriving (Show, Eq, Ord)

-- | procedure or function declaration
data Profile = Profile [Procparam] (Maybe SORT) deriving (Show, Eq)

-- | further VSE signature entries
data Sigentry = Procedure Id Profile Range deriving (Show, Eq)

data Procdecls = Procdecls [Annoted Sigentry] Range deriving (Show, Eq)

-- | wrapper for positions
data Ranged a = Ranged { unRanged :: a, range :: Range }
  deriving (Show, Eq, Ord)

-- | programs with ranges
type Program = Ranged PlainProgram

-- | programs based on restricted terms and formulas
data PlainProgram =
    Abort
  | Skip
  | Assign VAR (TERM ())
  | Call Id [TERM ()] -- ^ a procedure call
  | Return (TERM ())
  | Block [VAR_DECL] Program
  | Seq Program Program
  | If (FORMULA ()) Program Program
  | While (FORMULA ()) Program
    deriving (Show, Eq, Ord)

-- | fold record
data FoldRec a = FoldRec
  { foldAbort :: Program -> a
  , foldSkip :: Program -> a
  , foldAssign :: Program -> VAR  -> TERM () -> a
  , foldCall :: Program -> Id -> [TERM ()] -> a
  , foldReturn :: Program -> (TERM ()) -> a
  , foldBlock :: Program -> [VAR_DECL] -> a -> a
  , foldSeq :: Program -> a -> a -> a
  , foldIf :: Program -> FORMULA () -> a -> a -> a
  , foldWhile :: Program -> FORMULA () -> a -> a }

-- | fold function
foldProg :: FoldRec a -> Program -> a
foldProg r p = case unRanged p of
  Abort -> foldAbort r p 
  Skip -> foldSkip r p 
  Assign v t-> foldAssign r p v t
  Call i ts -> foldCall r p i ts
  Return t -> foldReturn r p t
  Block vs q -> foldBlock r p vs $ foldProg r q
  Seq p1 p2 -> foldSeq r p (foldProg r p1) $ foldProg r p2
  If f p1 p2 -> foldIf r p f (foldProg r p1) $ foldProg r p2
  While f q -> foldWhile r p f $ foldProg r q

mapRec :: FoldRec Program
mapRec = FoldRec
  { foldAbort = id
  , foldSkip = id
  , foldAssign = \ (Ranged _ r) v t -> Ranged (Assign v t) r
  , foldCall = \ (Ranged _ r) i ts -> Ranged (Call i ts) r
  , foldReturn = \ (Ranged _ r) t -> Ranged (Return t) r
  , foldBlock = \ (Ranged _ r) vs p -> Ranged (Block vs p) r
  , foldSeq = \ (Ranged _ r) p1 p2 -> Ranged (Seq p1 p2) r
  , foldIf = \ (Ranged _ r) c p1 p2 -> Ranged (If c p1 p2) r
  , foldWhile = \ (Ranged _ r) c p -> Ranged (While c p) r }
 
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
    deriving (Show, Eq, Ord)

type Dlformula = Ranged VSEforms
type Sentence = FORMULA Dlformula

-- | box or diamond indicator
data BoxOrDiamond = Box | Diamond deriving (Show, Eq, Ord)

data ProcKind = Proc | Func deriving (Show, Eq, Ord)

-- | procedure definitions as basic items becoming sentences
data Defproc = Defproc ProcKind Id [VAR] Program Range deriving (Show, Eq, Ord)

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
  pretty (Procdecls l _) = fsep
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
    Call p ts -> idDoc p <>
      if null ts then empty else parens $ ppWithCommas ts
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
      , text "ELSE" <+> pretty e
      , text "FI" ]
    While f p -> sep
      [ text "WHILE" <+> pretty f
      , text "DO" <+> pretty p
      , text "OD" ]

instance Pretty VSEforms where
  pretty v = case v of
    Dlformula b p f -> let d = pretty p in
      (case b of
         Box -> text "[:" <> d <> text ":]"
         Diamond -> text "<:" <> d <> text ":>")
      <+> (if isJunct f then parens else id) (pretty f)
    Defprocs ps -> prettyProcdefs ps

prettyProcdefs :: [Defproc] -> Doc
prettyProcdefs ps = vcat
  [ text "DEFPROCS"
  , vsep . punctuate semi $ map pretty ps
  , text "DEFPROCSEND" ]
