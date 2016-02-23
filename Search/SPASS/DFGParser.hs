{- |
Module      :  $Header$
Description :  To be replaced by SoftFOL.DFGParser
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.SPASS.DFGParser where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Prim
import qualified Text.ParserCombinators.Parsec.Token as PT
import Search.SPASS.Sign




-- ----------------------------------------------
-- * SPASS Language Definition
-- ----------------------------------------------

spassDef :: PT.LanguageDef st
spassDef    
 = PT.LanguageDef 
   { PT.commentStart   = ""--"{*"
   , PT.commentEnd     = ""--"*}"
   , PT.commentLine    = "%"
   , PT.nestedComments = False
   , PT.identStart     = letter <|> digit -- digit is not conform to dfg-syntax definition, but needed for mptp.
   , PT.identLetter    = alphaNum <|> oneOf "_'"
   , PT.opStart        = letter -- brauche ich nicht
   , PT.opLetter       = letter --
   , PT.reservedOpNames= []
   , PT.reservedNames  = ["forall", "exists", "equal", "true", "false", "or", "and", "not", "implies", "implied", "equiv", "xor"]
   , PT.caseSensitive  = True
   }

-- helpers ----------------------------------------------------------

lexer :: PT.TokenParser st
lexer = PT.makeTokenParser spassDef

comma = PT.comma lexer
dot = PT.dot lexer
commaSep1 = PT.commaSep1 lexer
parens = PT.parens lexer
squares = PT.squares lexer
symbolT = PT.symbol lexer
natural = PT.natural lexer
whiteSpace = PT.whiteSpace lexer

--parensDot :: Text.ParserCombinators.Parsec.Char.CharParser st a -> Text.ParserCombinators.Parsec.Prim.GenParser Char st a
parensDot p = parens p << dot
squaresDot p = squares p << dot

text = string "{*" >> (manyTill anyChar (try (string "*}")))
{-
*SPASS.Parser> run text "{* mein Kommentar *}"
" mein Kommentar "
-}

identifierT = PT.identifier lexer

list_of sort = string "list_of_" >> string sort
list_of_dot sort = list_of sort >> dot
end_of_list = symbolT "end_of_list."

oneOfTokens ls = choice (map (try . symbolT) ls)
{-
*SPASS.Parser> run (oneOfTokens ["ab","cd"]) "abcd"
"ab"
-}

mapTokensToData ls = choice (map (try . tokenToData) ls)
    where tokenToData (s,t) = symbolT s >> return t

maybeParser p = option Nothing (do {r <- p; return (Just r)})


parseSPASS = whiteSpace >> problem



-- ** SPASS Problem
problem :: Text.ParserCombinators.Parsec.Prim.GenParser Char st Search.SPASS.Sign.SPProblem
problem = do symbolT "begin_problem"
	     i <- parensDot identifierT
	     dl <- description_list
	     lp <- logical_part
	     -- s <- settings -- not yet supported!
	     symbolT "end_problem."
	     return (SPProblem
		     {identifier = i,
                      description = dl,
                      logicalPart = lp,
                      settings = []})

-- ** SPASS Desciptions

{- |
  A description is mandatory for a SPASS problem. It has to specify at least
  a 'name', the name of the 'author', the 'status' (see also 'SPLogState' below),
  and a (verbose) description.
-}
description_list :: Text.ParserCombinators.Parsec.Prim.GenParser Char st Search.SPASS.Sign.SPDescription
description_list = do list_of_dot "descriptions"
		      n <- symbolT "name" >> parensDot text
		      a <- symbolT "author" >> parensDot text
		      v <- maybeParser (symbolT "version" >> parensDot text)
		      l <- maybeParser (symbolT "logic" >> parensDot text)
		      s <- symbolT "status" >> parensDot (mapTokensToData
								[("satisfiable",SPStateSatisfiable),
								 ("unsatisfiable",SPStateUnsatisfiable),
								 ("unknown",SPStateUnknown)])
		      de <- symbolT "description" >> parensDot text
		      da <- maybeParser (symbolT "date" >> parensDot text)
		      end_of_list
		      return (SPDescription
			      {name = n, author = a, version = v, logic = l,
                               status = s, desc = de, date = da})

{-
*SPASS.Parser> run description_list "list_of_descriptions.name({* Pelletier?s Problem No. 57 *}).author({* Christoph Weidenbach *}).status(unsatisfiable).description({* Problem taken in revised form from the Pelletier Collection,      Journal of Automated Reasoning, Vol. 2, No. 2, pages 191-216 *}).end_of_list."
SPDescription {name = " Pelletier?s Problem No. 57 ", author = " Christoph Weidenbach ", version = Nothing, logic = Nothing, status = SPStateUnsatisfiable, desc = " Problem taken in revised form from the Pelletier Collection,      Journal of Automated Reasoning, Vol. 2, No. 2, pages 191-216 ", date = Nothing}
-}

{- |
  The state of a SPASS problem can be satisfiable, unsatisfiable, or unknown.
-}

-- ** SPASS Settings

{- |
  We only support one of the three types mentioned here:
  <http://spass.mpi-sb.mpg.de/webspass/help/options.html>
-}


-- ** SPASS Logical Parts

{- |
  A SPASS logical part consists of a symbol list, a declaration list, and a
  set of formula lists. Support for clause lists and proof lists hasn't
  been implemented yet.
-}
logical_part :: Text.ParserCombinators.Parsec.Prim.GenParser Char st Search.SPASS.Sign.SPLogicalPart
logical_part = do sl <- maybeParser symbol_list
		  --dl <- declaration_list  -- braucht man nicht fuer mptp
		  fs <- many formula_list
		  --cl <- many clause_list  -- braucht man nicht fuer mptp
		  --pl <- many proof_list  -- braucht man nicht fuer mptp
		  return (SPLogicalPart
			  {symbolList = sl,
                           declarationList = [],
                           formulaLists = fs})
--                        clauseLists :: [SPClauseList],
--                        proofLists :: [SPProofList]



-- *** Symbol List

{- |
  SPASS Symbol List
-}
symbol_list :: Text.ParserCombinators.Parsec.Prim.GenParser Char st Search.SPASS.Sign.SPSymbolList
symbol_list = do list_of_dot "symbols"
		 fs <- option [] (signSymFor "functions")
		 ps <- option [] (signSymFor "predicates")
		 ss <- option [] (signSymFor "sorts")
		 end_of_list
		 return (SPSymbolList
			 {functions = fs,
			  predicates = ps,
			  sorts = ss,
			  operators = [],     -- not supported in dfg-syntax version 1.5
			  quantifiers = []})  -- not supported in dfg-syntax version 1.5
{-
*SPASS.Parser> run symbol_list "list_of_symbols.functions[(f,2), (a,0), (b,0), (c,0)].predicates[(F,2)].end_of_list."
SPSymbolList {functions = [SPSignSym {sym = "f", arity = 2},SPSignSym {sym = "a", arity = 0},SPSignSym {sym = "b", arity = 0},SPSignSym {sym = "c", arity = 0}], predicates = [SPSignSym {sym = "F", arity = 2}], sorts = [], operators = [], quantifiers = []}
-}

signSymFor kind = symbolT kind >> squaresDot (commaSep1 $ parens signSym)
signSym = do s <- identifierT
	     a <- maybeParser (comma >> natural) -- option Nothing ((do {comma; n <- natural; return (Just n)}))
	     return (case a
		     of (Just a) -> SPSignSym {sym = s, arity = fromInteger a}
		        Nothing -> SPSimpleSignSym s)

-- *** Declaration List

{- |
  SPASS Declaration List
-}

--declaration_list

-- *** Formula List

{- |
  SPASS Formula List
-}
formula_list :: Text.ParserCombinators.Parsec.Prim.GenParser Char st Search.SPASS.Sign.SPFormulaList
formula_list = do list_of "formulae"
                  ot <- parens (mapTokensToData [("axioms",SPOriginAxioms),
						 ("conjectures",SPOriginConjectures)])
                  dot
		  fs <- many (formula (case ot of {SPOriginAxioms -> True; _ -> False}))
                  end_of_list
                  return (SPFormulaList { originType = ot,
					  formulae = fs })
{-
*SPASS.Parser> run formula_list "list_of_formulae(axioms).formula(all([a,b],R(a,b)),bla).end_of_list."
SPFormulaList {originType = SPOriginAxioms, formulae = [NamedSen {senName = "bla", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPCustomQuantSym "all", variableList = [SPSimpleTerm (SPCustomSymbol "a"),SPSimpleTerm (SPCustomSymbol "b")], qFormula = SPComplexTerm {symbol = SPCustomSymbol "R", arguments = [SPSimpleTerm (SPCustomSymbol "a"),SPSimpleTerm (SPCustomSymbol "b")]}}}]}
*SPASS.Parser> run formula_list "list_of_formulae(axioms).formula(forall([a,b],R(a,b)),bla).end_of_list."
SPFormulaList {originType = SPOriginAxioms, formulae = [NamedSen {senName = "bla", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "a"),SPSimpleTerm (SPCustomSymbol "b")], qFormula = SPComplexTerm {symbol = SPCustomSymbol "R", arguments = [SPSimpleTerm (SPCustomSymbol "a"),SPSimpleTerm (SPCustomSymbol "b")]}}}]}
*SPASS.Parser> run formula_list "list_of_formulae(axioms).formula(forall([a,b],equiv(a,b)),bla).end_of_list."
SPFormulaList {originType = SPOriginAxioms, formulae = [NamedSen {senName = "bla", isAxiom = True, isDef = False, sentence = SPQuantTerm {quantSym = SPForall, variableList = [SPSimpleTerm (SPCustomSymbol "a"),SPSimpleTerm (SPCustomSymbol "b")], qFormula = SPComplexTerm {symbol = SPEquiv, arguments = [SPSimpleTerm (SPCustomSymbol "a"),SPSimpleTerm (SPCustomSymbol "b")]}}}]}
-}
formula :: Bool -> Text.ParserCombinators.Parsec.Prim.GenParser Char st (Search.SPASS.Sign.Named Search.SPASS.Sign.SPTerm)
formula bool = do symbolT "formula"
                  pos <- getPosition
	          parensDot (do sen <- term
			        name <- (option "" (comma >> identifierT))
			        return (NamedSen
					{senName = (show $ sourceLine pos), -- (sourceName pos) ++ " line: " ++ (show $ sourceLine pos) ++ " name:" ++ name,
					 isAxiom = bool, -- propagated from 'origin_type' of 'list_of_formulae'
					 isDef = False, -- this originTpe does not exist
					 sentence = sen}))

-- *** Terms

{- |
  A SPASS Term.
-}

quantification :: Search.SPASS.Sign.SPQuantSym -> Text.ParserCombinators.Parsec.Prim.GenParser Char st Search.SPASS.Sign.SPTerm
quantification s = do (ts',t') <- parens (do ts <- squares (commaSep1 term) -- todo: var binding should allow only simple terms
                                             comma; t <- term
                                             return (ts,t))
                      return (SPQuantTerm
                              {quantSym = s,variableList = ts',qFormula = t'})

application :: Search.SPASS.Sign.SPSymbol -> Text.ParserCombinators.Parsec.Prim.GenParser Char	st Search.SPASS.Sign.SPTerm
application s = do ts <- parens (commaSep1 term)
                   return (SPComplexTerm
			   {symbol = s, arguments = ts})

constant :: (Monad m) => Search.SPASS.Sign.SPSymbol -> m Search.SPASS.Sign.SPTerm
constant c = return (SPSimpleTerm c)

term :: Text.ParserCombinators.Parsec.Prim.GenParser Char st Search.SPASS.Sign.SPTerm
term = do s <- identifierT
          do {try (quantification (SPCustomQuantSym s)) 
	      <|> try (application (SPCustomSymbol s)) 
	      <|> (constant (SPCustomSymbol s))}
       <|>
       do q <- mapTokensToData [("forall",SPForall), ("exists",SPExists)]
	  quantification q
       <|>
       do a <- mapTokensToData [("equal",SPEqual), ("or",SPOr), ("and",SPAnd),("not",SPNot),
                                ("xor",SPXor),
				("implies",SPImplies), ("implied",SPImplied),("equiv",SPEquiv)]
	  application a
       <|>
       do c <- mapTokensToData [("true",SPTrue), ("false",SPFalse)]
	  constant c

{-
For testing
-}

-- ----------------------------------------------
-- * Monad and Functor extensions
-- ----------------------------------------------

bind :: (Monad m) => (a -> b -> c) -> m a -> m b -> m c
bind f p q = do { x <- p; y <- q; return (f x y) }

infixl <<

(<<) :: (Monad m) => m a -> m b -> m a
(<<) = bind const

infixr 5 <:>

(<:>) :: (Monad m) => m a -> m [a] -> m [a]
(<:>) = bind (:)

infixr 5 <++>

(<++>) :: (Monad m) => m [a] -> m [a] -> m [a]
(<++>) = bind (++)




run p input = case (parse p "" input)
              of Left err -> error (show err)
                 Right result  -> return result