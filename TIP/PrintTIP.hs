{-
Copyright (c) 2015, Dan Rosén
Copyright (c) 2016, Nick Smallbone

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the name of the copyright holder nor the names of other
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-}
-- File generated by the BNF Converter (bnfc 2.9.4).

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Pretty-printer for TIP.

module TIP.PrintTIP where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified TIP.AbsTIP

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 False (map ($ "") $ d []) ""
  where
  rend
    :: Int        -- ^ Indentation level.
    -> Bool       -- ^ Pending indentation to be output before next character?
    -> [String]
    -> ShowS
  rend i p = \case
      "["      :ts -> char '[' . rend i False ts
      "("      :ts -> char '(' . rend i False ts
      "{"      :ts -> onNewLine i     p . showChar   '{'  . new (i+1) ts
      "}" : ";":ts -> onNewLine (i-1) p . showString "};" . new (i-1) ts
      "}"      :ts -> onNewLine (i-1) p . showChar   '}'  . new (i-1) ts
      [";"]        -> char ';'
      ";"      :ts -> char ';' . new i ts
      t  : ts@(s:_) | closingOrPunctuation s
                   -> pending . showString t . rend i False ts
      t        :ts -> pending . space t      . rend i False ts
      []           -> id
    where
    -- Output character after pending indentation.
    char :: Char -> ShowS
    char c = pending . showChar c

    -- Output pending indentation.
    pending :: ShowS
    pending = if p then indent i else id

  -- Indentation (spaces) for given indentation level.
  indent :: Int -> ShowS
  indent i = replicateS (2*i) (showChar ' ')

  -- Continue rendering in new line with new indentation.
  new :: Int -> [String] -> ShowS
  new j ts = showChar '\n' . rend j True ts

  -- Make sure we are on a fresh line.
  onNewLine :: Int -> Bool -> ShowS
  onNewLine i p = (if p then id else showChar '\n') . indent i

  -- Separate given string from following text by a space (if needed).
  space :: String -> ShowS
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt i = concatD . map (prt i)

instance Print Char where
  prt _ c = doc (showChar '\'' . mkEsc '\'' c . showChar '\'')

instance Print String where
  prt _ = printString

printString :: String -> Doc
printString s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print TIP.AbsTIP.UnquotedSymbol where
  prt _ (TIP.AbsTIP.UnquotedSymbol (_,i)) = doc $ showString i
instance Print TIP.AbsTIP.QuotedSymbol where
  prt _ (TIP.AbsTIP.QuotedSymbol (_,i)) = doc $ showString i
instance Print TIP.AbsTIP.Keyword where
  prt _ (TIP.AbsTIP.Keyword i) = doc $ showString i
instance Print TIP.AbsTIP.Start where
  prt i = \case
    TIP.AbsTIP.Start decls -> prPrec i 0 (concatD [prt 0 decls])

instance Print [TIP.AbsTIP.Decl] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [doc (showString "("), prt 0 x, doc (showString ")"), prt 0 xs]

instance Print TIP.AbsTIP.Decl where
  prt i = \case
    TIP.AbsTIP.DeclareDatatype attrsymbol datatype -> prPrec i 0 (concatD [doc (showString "declare-datatype"), prt 0 attrsymbol, prt 0 datatype])
    TIP.AbsTIP.DeclareDatatypes datatypenames datatypes -> prPrec i 0 (concatD [doc (showString "declare-datatypes"), doc (showString "("), prt 0 datatypenames, doc (showString ")"), doc (showString "("), prt 0 datatypes, doc (showString ")")])
    TIP.AbsTIP.DeclareSort attrsymbol n -> prPrec i 0 (concatD [doc (showString "declare-sort"), prt 0 attrsymbol, prt 0 n])
    TIP.AbsTIP.DeclareConst attrsymbol consttype -> prPrec i 0 (concatD [doc (showString "declare-const"), prt 0 attrsymbol, prt 0 consttype])
    TIP.AbsTIP.DeclareFun attrsymbol funtype -> prPrec i 0 (concatD [doc (showString "declare-fun"), prt 0 attrsymbol, prt 0 funtype])
    TIP.AbsTIP.DefineFun fundec expr -> prPrec i 0 (concatD [doc (showString "define-fun"), prt 0 fundec, prt 0 expr])
    TIP.AbsTIP.DefineFunRec fundec expr -> prPrec i 0 (concatD [doc (showString "define-fun-rec"), prt 0 fundec, prt 0 expr])
    TIP.AbsTIP.DefineFunsRec bracketedfundecs exprs -> prPrec i 0 (concatD [doc (showString "define-funs-rec"), doc (showString "("), prt 0 bracketedfundecs, doc (showString ")"), doc (showString "("), prt 0 exprs, doc (showString ")")])
    TIP.AbsTIP.Formula assertion attrs expr -> prPrec i 0 (concatD [prt 0 assertion, prt 0 attrs, prt 0 expr])
    TIP.AbsTIP.FormulaPar assertion attrs par expr -> prPrec i 0 (concatD [prt 0 assertion, prt 0 attrs, doc (showString "("), prt 0 par, prt 0 expr, doc (showString ")")])

instance Print TIP.AbsTIP.Assertion where
  prt i = \case
    TIP.AbsTIP.Assert -> prPrec i 0 (concatD [doc (showString "assert")])
    TIP.AbsTIP.Prove -> prPrec i 0 (concatD [doc (showString "prove")])

instance Print TIP.AbsTIP.Par where
  prt i = \case
    TIP.AbsTIP.Par symbols -> prPrec i 0 (concatD [doc (showString "par"), doc (showString "("), prt 0 symbols, doc (showString ")")])

instance Print TIP.AbsTIP.ConstType where
  prt i = \case
    TIP.AbsTIP.ConstTypeMono type_ -> prPrec i 0 (concatD [prt 0 type_])
    TIP.AbsTIP.ConstTypePoly par type_ -> prPrec i 0 (concatD [doc (showString "("), prt 0 par, prt 0 type_, doc (showString ")")])

instance Print TIP.AbsTIP.InnerFunType where
  prt i = \case
    TIP.AbsTIP.InnerFunType types type_ -> prPrec i 0 (concatD [doc (showString "("), prt 0 types, doc (showString ")"), prt 0 type_])

instance Print TIP.AbsTIP.FunType where
  prt i = \case
    TIP.AbsTIP.FunTypeMono innerfuntype -> prPrec i 0 (concatD [prt 0 innerfuntype])
    TIP.AbsTIP.FunTypePoly par innerfuntype -> prPrec i 0 (concatD [doc (showString "("), prt 0 par, doc (showString "("), prt 0 innerfuntype, doc (showString ")"), doc (showString ")")])

instance Print TIP.AbsTIP.InnerFunDec where
  prt i = \case
    TIP.AbsTIP.InnerFunDec bindings type_ -> prPrec i 0 (concatD [doc (showString "("), prt 0 bindings, doc (showString ")"), prt 0 type_])

instance Print TIP.AbsTIP.FunDec where
  prt i = \case
    TIP.AbsTIP.FunDecMono attrsymbol innerfundec -> prPrec i 0 (concatD [prt 0 attrsymbol, prt 0 innerfundec])
    TIP.AbsTIP.FunDecPoly attrsymbol par innerfundec -> prPrec i 0 (concatD [prt 0 attrsymbol, doc (showString "("), prt 0 par, doc (showString "("), prt 0 innerfundec, doc (showString ")"), doc (showString ")")])

instance Print TIP.AbsTIP.BracketedFunDec where
  prt i = \case
    TIP.AbsTIP.BracketedFunDec fundec -> prPrec i 0 (concatD [doc (showString "("), prt 0 fundec, doc (showString ")")])

instance Print TIP.AbsTIP.DatatypeName where
  prt i = \case
    TIP.AbsTIP.DatatypeName attrsymbol n -> prPrec i 0 (concatD [doc (showString "("), prt 0 attrsymbol, prt 0 n, doc (showString ")")])

instance Print TIP.AbsTIP.InnerDatatype where
  prt i = \case
    TIP.AbsTIP.InnerDatatype constructors -> prPrec i 0 (concatD [doc (showString "("), prt 0 constructors, doc (showString ")")])

instance Print TIP.AbsTIP.Datatype where
  prt i = \case
    TIP.AbsTIP.DatatypeMono innerdatatype -> prPrec i 0 (concatD [prt 0 innerdatatype])
    TIP.AbsTIP.DatatypePoly par innerdatatype -> prPrec i 0 (concatD [doc (showString "("), prt 0 par, prt 0 innerdatatype, doc (showString ")")])

instance Print TIP.AbsTIP.Constructor where
  prt i = \case
    TIP.AbsTIP.Constructor attrsymbol bindings -> prPrec i 0 (concatD [doc (showString "("), prt 0 attrsymbol, prt 0 bindings, doc (showString ")")])

instance Print TIP.AbsTIP.Binding where
  prt i = \case
    TIP.AbsTIP.Binding symbol type_ -> prPrec i 0 (concatD [doc (showString "("), prt 0 symbol, prt 0 type_, doc (showString ")")])

instance Print TIP.AbsTIP.LetDecl where
  prt i = \case
    TIP.AbsTIP.LetDecl symbol expr -> prPrec i 0 (concatD [doc (showString "("), prt 0 symbol, prt 0 expr, doc (showString ")")])

instance Print TIP.AbsTIP.Type where
  prt i = \case
    TIP.AbsTIP.TyVar symbol -> prPrec i 0 (concatD [prt 0 symbol])
    TIP.AbsTIP.TyApp symbol types -> prPrec i 0 (concatD [doc (showString "("), prt 0 symbol, prt 0 types, doc (showString ")")])
    TIP.AbsTIP.ArrowTy types -> prPrec i 0 (concatD [doc (showString "("), doc (showString "=>"), prt 0 types, doc (showString ")")])
    TIP.AbsTIP.IntTy -> prPrec i 0 (concatD [doc (showString "Int")])
    TIP.AbsTIP.RealTy -> prPrec i 0 (concatD [doc (showString "Real")])
    TIP.AbsTIP.BoolTy -> prPrec i 0 (concatD [doc (showString "Bool")])

instance Print TIP.AbsTIP.Expr where
  prt i = \case
    TIP.AbsTIP.Var polysymbol -> prPrec i 0 (concatD [prt 0 polysymbol])
    TIP.AbsTIP.App head exprs -> prPrec i 0 (concatD [doc (showString "("), prt 0 head, prt 0 exprs, doc (showString ")")])
    TIP.AbsTIP.Match expr cases -> prPrec i 0 (concatD [doc (showString "("), doc (showString "match"), prt 0 expr, doc (showString "("), prt 0 cases, doc (showString ")"), doc (showString ")")])
    TIP.AbsTIP.Let letdecls expr -> prPrec i 0 (concatD [doc (showString "("), doc (showString "let"), doc (showString "("), prt 0 letdecls, doc (showString ")"), prt 0 expr, doc (showString ")")])
    TIP.AbsTIP.Binder binder bindings expr -> prPrec i 0 (concatD [doc (showString "("), prt 0 binder, doc (showString "("), prt 0 bindings, doc (showString ")"), prt 0 expr, doc (showString ")")])
    TIP.AbsTIP.Lit lit -> prPrec i 0 (concatD [prt 0 lit])

instance Print TIP.AbsTIP.Lit where
  prt i = \case
    TIP.AbsTIP.LitInt n -> prPrec i 0 (concatD [prt 0 n])
    TIP.AbsTIP.LitNegInt n -> prPrec i 0 (concatD [doc (showString "-"), prt 0 n])
    TIP.AbsTIP.LitTrue -> prPrec i 0 (concatD [doc (showString "true")])
    TIP.AbsTIP.LitFalse -> prPrec i 0 (concatD [doc (showString "false")])

instance Print TIP.AbsTIP.Binder where
  prt i = \case
    TIP.AbsTIP.Lambda -> prPrec i 0 (concatD [doc (showString "lambda")])
    TIP.AbsTIP.Forall -> prPrec i 0 (concatD [doc (showString "forall")])
    TIP.AbsTIP.Exists -> prPrec i 0 (concatD [doc (showString "exists")])

instance Print TIP.AbsTIP.Case where
  prt i = \case
    TIP.AbsTIP.Case pattern_ expr -> prPrec i 0 (concatD [doc (showString "("), prt 0 pattern_, prt 0 expr, doc (showString ")")])

instance Print TIP.AbsTIP.Pattern where
  prt i = \case
    TIP.AbsTIP.Default -> prPrec i 0 (concatD [doc (showString "_")])
    TIP.AbsTIP.ConPat symbol symbols -> prPrec i 0 (concatD [doc (showString "("), prt 0 symbol, prt 0 symbols, doc (showString ")")])
    TIP.AbsTIP.SimplePat symbol -> prPrec i 0 (concatD [prt 0 symbol])
    TIP.AbsTIP.LitPat lit -> prPrec i 0 (concatD [prt 0 lit])

instance Print TIP.AbsTIP.Head where
  prt i = \case
    TIP.AbsTIP.Const polysymbol -> prPrec i 0 (concatD [prt 0 polysymbol])
    TIP.AbsTIP.At -> prPrec i 0 (concatD [doc (showString "@")])
    TIP.AbsTIP.IfThenElse -> prPrec i 0 (concatD [doc (showString "ite")])
    TIP.AbsTIP.And -> prPrec i 0 (concatD [doc (showString "and")])
    TIP.AbsTIP.Or -> prPrec i 0 (concatD [doc (showString "or")])
    TIP.AbsTIP.Not -> prPrec i 0 (concatD [doc (showString "not")])
    TIP.AbsTIP.Implies -> prPrec i 0 (concatD [doc (showString "=>")])
    TIP.AbsTIP.Equal -> prPrec i 0 (concatD [doc (showString "=")])
    TIP.AbsTIP.Distinct -> prPrec i 0 (concatD [doc (showString "distinct")])
    TIP.AbsTIP.NumAdd -> prPrec i 0 (concatD [doc (showString "+")])
    TIP.AbsTIP.NumSub -> prPrec i 0 (concatD [doc (showString "-")])
    TIP.AbsTIP.NumMul -> prPrec i 0 (concatD [doc (showString "*")])
    TIP.AbsTIP.NumDiv -> prPrec i 0 (concatD [doc (showString "/")])
    TIP.AbsTIP.IntDiv -> prPrec i 0 (concatD [doc (showString "div")])
    TIP.AbsTIP.IntMod -> prPrec i 0 (concatD [doc (showString "mod")])
    TIP.AbsTIP.NumGt -> prPrec i 0 (concatD [doc (showString ">")])
    TIP.AbsTIP.NumGe -> prPrec i 0 (concatD [doc (showString ">=")])
    TIP.AbsTIP.NumLt -> prPrec i 0 (concatD [doc (showString "<")])
    TIP.AbsTIP.NumLe -> prPrec i 0 (concatD [doc (showString "<=")])
    TIP.AbsTIP.NumWiden -> prPrec i 0 (concatD [doc (showString "to_real")])

instance Print TIP.AbsTIP.PolySymbol where
  prt i = \case
    TIP.AbsTIP.NoAs symbol -> prPrec i 0 (concatD [prt 0 symbol])
    TIP.AbsTIP.As symbol types -> prPrec i 0 (concatD [doc (showString "("), doc (showString "_"), prt 0 symbol, prt 0 types, doc (showString ")")])

instance Print TIP.AbsTIP.AttrSymbol where
  prt i = \case
    TIP.AbsTIP.AttrSymbol symbol attrs -> prPrec i 0 (concatD [prt 0 symbol, prt 0 attrs])

instance Print TIP.AbsTIP.Attr where
  prt i = \case
    TIP.AbsTIP.NoValue keyword -> prPrec i 0 (concatD [prt 0 keyword])
    TIP.AbsTIP.Value keyword symbol -> prPrec i 0 (concatD [prt 0 keyword, prt 0 symbol])

instance Print [TIP.AbsTIP.LetDecl] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.Case] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.Expr] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.Datatype] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.Constructor] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.Binding] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.Symbol] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.Type] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.FunDec] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.BracketedFunDec] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.Attr] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [TIP.AbsTIP.DatatypeName] where
  prt _ [] = concatD []
  prt _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print TIP.AbsTIP.Symbol where
  prt i = \case
    TIP.AbsTIP.Unquoted unquotedsymbol -> prPrec i 0 (concatD [prt 0 unquotedsymbol])
    TIP.AbsTIP.Quoted quotedsymbol -> prPrec i 0 (concatD [prt 0 quotedsymbol])
