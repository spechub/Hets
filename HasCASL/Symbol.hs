{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable

   
   HasCASL symbols for structured specs 
-}

module HasCASL.Symbol where

import Common.Id
import Common.Keywords
import Common.Lexer
import Common.AS_Annotation
import Common.AnnoState
import Common.Lib.Parsec

import HasCASL.HToken
import HasCASL.ParseTerm
import HasCASL.As
import HasCASL.PrintAs

import Common.PrettyPrint
import Common.Lib.Pretty as PP
import Common.PPUtils
import Data.Dynamic


-- * symbol data types
-- | symbols 
data SymbItems = SymbItems SymbKind [Symb] [Annotation] [Pos] 
		  -- pos: kind, commas
		  deriving (Show, Eq, Typeable)

-- | mapped symbols 
data SymbMapItems = SymbMapItems SymbKind [SymbOrMap] [Annotation] [Pos]
		      -- pos: kind commas
		      deriving (Show, Eq, Typeable)

-- | kind of symbols
data SymbKind = Implicit | SK_sort | SK_type | SK_op | SK_pred | SK_class
		 deriving (Show, Eq, Ord)

-- | type annotated symbols
data Symb = Symb Id (Maybe SymbType) [Pos] 
	    -- pos: colon (or empty)
	    deriving (Show, Eq)

-- | type for symbols
data SymbType = SymbType TypeScheme
	    deriving (Show, Eq)

-- | mapped symbol
data SymbOrMap = SymbOrMap Symb (Maybe Symb) [Pos]
		   -- pos: "|->" (or empty)
		   deriving (Show, Eq)


-- * parsers for symbols
-- | parse a (typed) symbol 
symb :: AParser Symb
symb = do i <- uninstOpId
	  do c <- colT 
	     t <- typeScheme
	     return (Symb i (Just $ SymbType t) [tokPos c])
	    <|> 
            do c <- qColonT 
	       t <- parseType 
	       return (Symb i (Just $ SymbType $ simpleTypeScheme $ 
				  LazyType t [tokPos c]) [tokPos c])
             <|> return (Symb i Nothing [])
	       
-- | parse a mapped symbol
symbMap :: AParser SymbOrMap
symbMap =   do s <- symb
	       do   f <- asKey mapsTo
		    t <- symb
		    return (SymbOrMap s (Just t) [tokPos f])
		  <|> return (SymbOrMap s Nothing [])

-- | parse kind of symbols
symbKind :: AParser (SymbKind, Token)
symbKind = try(
        do q <- pluralKeyword opS 
	   return (SK_op, q)
        <|>
        do q <- pluralKeyword functS 
	   return (SK_op, q)
        <|>
        do q <- pluralKeyword predS 
	   return (SK_op, q)
        <|>
        do q <- pluralKeyword typeS 
	   return (SK_type, q)
        <|>
        do q <- pluralKeyword sortS 
	   return (SK_type, q)
        <|>
        do q <- asKey (classS ++ "es") <|> asKey classS
	   return (SK_class, q))
	<?> "kind"


-- | parse symbol items
symbItems :: AParser SymbItems
symbItems = do s <- symb
	       return (SymbItems Implicit [s] [] [])
	    <|> 
	    do (k, p) <- symbKind
               (is, ps) <- symbs
	       return (SymbItems k is [] (map tokPos (p:ps)))

symbs :: AParser ([Symb], [Token])
symbs = do s <- symb 
	   do   c <- anComma `followedWith` symb
	        (is, ps) <- symbs
		return (s:is, c:ps)
	     <|> return ([s], [])

-- | parse symbol mappings
symbMapItems :: AParser SymbMapItems
symbMapItems = 
            do s <- symbMap
	       return (SymbMapItems Implicit [s] [] [])
	    <|> 
	    do (k, p) <- symbKind
               (is, ps) <- symbMaps
	       return (SymbMapItems k is [] (map tokPos (p:ps)))

symbMaps :: AParser ([SymbOrMap], [Token])
symbMaps = 
        do s <- symbMap 
	   do   c <- anComma `followedWith` symb
	        (is, ps) <- symbMaps
		return (s:is, c:ps)
	     <|> return ([s], [])

-- pretty printing

-- | print symbol kind
printSK :: SymbKind -> Doc
printSK k = 
    case k of Implicit -> empty
	      _ -> ptext (drop 3 $ show k) <> PP.space 

instance PrettyPrint Symb where
    printText0 ga (Symb i mt _) =
	printText0 ga i <> (case mt of Nothing -> empty
			               Just (SymbType t) -> 
					  empty <+> colon <+>
					    printText0 ga t)

instance PrettyPrint SymbItems where
    printText0 ga (SymbItems k syms _ _) =
	printSK k <> commaT_text ga syms

instance PrettyPrint SymbOrMap where
    printText0 ga (SymbOrMap s mt _) =
	printText0 ga s <> (case mt of Nothing -> empty
			               Just t -> 
					  empty <+> ptext mapsTo <+>
					    printText0 ga t)

instance PrettyPrint SymbMapItems where
    printText0 ga (SymbMapItems k syms _ _) =
	printSK k <> commaT_text ga syms



	
