{- |
Module      :  ./HPAR/Parse_AS.hs
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  portable

Parser for HPAR
-}

module HPAR.Parse_AS where

import CASL.Formula
import CASL.OpItem
import CASL.SortItem
import qualified CASL.Parse_AS_Basic as CParse
import qualified CASL.Formula as CFormula


import Common.Parsec
import Common.AS_Annotation
import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import Common.GlobalAnnotations
import qualified RigidCASL.AS_Rigid as PAR_AS
import RigidCASL.Parse_AS ()
import Text.ParserCombinators.Parsec

import qualified HPAR.AS_Basic_HPAR as HPAR_AS 

-- | Toplevel parser for basic specs
basicSpec :: PrefixMap -> AParser st HPAR_AS.H_BASIC_SPEC
basicSpec ks = 
  fmap HPAR_AS.Basic_spec (annosParser parseBasicItems) 
                                       -- should be the method for H_BASIC_ITEMS
  <|> (oBraceT >> cBraceT >> return (HPAR_AS.Basic_spec []))


parseBasicItems :: AParser st HPAR_AS.H_BASIC_ITEMS -- TODO: take into account ks
parseBasicItems = 
     parseAxItems -- if this is not first, the parser for basic items consumes more than it should
  <|>
  do (as, ps) <- keyThenList nomP simpleId
     return $ HPAR_AS.Nom_decl $ HPAR_AS.Nom_item as ps
  <|>
  do (as, ps) <- keyThenList modP simpleId
     _c <- colonT
     ni <- getNumber
     let i = read ni :: Int
     return $ HPAR_AS.Mod_decl $ HPAR_AS.Mod_item as i ps
  <|>
  do x <- CParse.basicItems hybrid_keywords
     return $ HPAR_AS.PAR_decl x 


modP :: AParser st Token
modP = asKey modalityS <|> asKey modalitiesS

nomP :: AParser st Token
nomP = asKey nominalS <|> asKey nominalsS

keyThenList :: AParser st Token -> AParser st a ->
           AParser st ([a], Range)
keyThenList k p = do
        c <- k
        (as, cs) <- separatedBy p anComma
        let ps = catRange $ c : cs
        return (as, ps)

-- | Toplevel parser for formulae
aFormula :: AParser st (Annoted HPAR_AS.HFORMULA)
aFormula = allAnnoParser topformula

parseAxItems :: AParser st HPAR_AS.H_BASIC_ITEMS
parseAxItems = do
       d <- dotT
       (fs, ds) <- aFormula `separatedBy` dotT
       (_, an) <- optSemi
       let _ = catRange (d : ds)
           ns = init fs ++ [appendAnno (last fs) an]
       return $ HPAR_AS.Axiom_items ns



parenFormula :: AParser st HPAR_AS.HFORMULA
parenFormula = do
       oParenT << addAnnos
       f <- topformula << addAnnos
       cParenT >> return f

-- | Parser for at 
atKey :: AParser st Token
atKey = asKey asP

-- | Any word to token
propId :: [String] -> GenParser Char st Token
propId k = pToken $ reserved (k ++ hybrid_keywords) scanAnyWords

hFormula :: AParser st HPAR_AS.HFORMULA
hFormula = 
   do 
      c <- atKey
      n <- simpleId
      _ <- colonT
      f <- topformula -- here should be formula without @
      return $ HPAR_AS.AtState n f $ tokPos c
 <|> 
   do
    c <- asKey notS <|> asKey negS <?> "\"not\""
    f <- topformula
    return $ HPAR_AS.Negation f $ tokPos c
   <|>
     do
        c1 <- asKey lessS
        md <- propId [greaterS]
        c2 <- asKey greaterS
        f <- topformula
        return $ HPAR_AS.DiamondFormula md f $ toRange c1 [] c2
 <|>
     do
        c1 <- oBracketT
        md <- propId ["]"]
        c2 <- cBracketT
        f <- topformula
        return $ HPAR_AS.BoxFormula md f $ toRange c1 [] c2
 <|>
     do
       (q, p) <- quant
       parseQFormula (q, p)
 <|>
     do 
        f <- primFormula hybrid_keywords
        return $ HPAR_AS.Base_formula f nullRange    -- this should also catch nominals as terms. We have to make sure during static analysis that this is reverted!
 <|> 
     parenFormula 

parseQFormula :: (HPAR_AS.HQUANT, Token) -> AParser st HPAR_AS.HFORMULA
parseQFormula (q, p) = 
  do -- first try quantification on nominals, or the parser will complain 
     (vs, ps) <- keyThenList nomP simpleId
     d <- dotT
     f <- topformula
     return $ HPAR_AS.QuantNominals q vs f nullRange
    <|> 
  do  
     (vs, ps) <- varDecls []
     d <- dotT
     f <- topformula
     return $ HPAR_AS.QuantRigidVars q vs f $ toRange p ps d

andOrFormula :: AParser st HPAR_AS.HFORMULA
andOrFormula = hFormula >>= optAndOr

optAndOr :: HPAR_AS.HFORMULA -> AParser st HPAR_AS.HFORMULA
optAndOr f = do
      c <- andKey
      (fs, ps) <- hFormula `separatedBy` andKey
      return $ HPAR_AS.Conjunction (f : fs) $ catRange $ c : ps
    <|> do
      c <- orKey
      (fs, ps) <- hFormula `separatedBy` orKey
      return $ HPAR_AS.Disjunction (f : fs) $ catRange $ c : ps
    <|> return f
 
topformula ::  AParser st HPAR_AS.HFORMULA
topformula = andOrFormula >>= optImplForm

optImplForm :: HPAR_AS.HFORMULA -> AParser st HPAR_AS.HFORMULA
optImplForm f = do
      c <- implKey
      (fs, ps) <- andOrFormula `separatedBy` implKey
      return $ makeImpl (f : fs)
    <|> do
      c <- asKey equivS
      g <- andOrFormula
      return $ HPAR_AS.Equivalence f g $ tokPos c
    <|> return f

makeImpl :: [HPAR_AS.HFORMULA] -> HPAR_AS.HFORMULA
makeImpl l = 
 case l of 
  [f1, f2] -> HPAR_AS.Implication f1 f2 nullRange
  f1 : fs  -> HPAR_AS.Implication f1 (makeImpl fs) nullRange
  _ -> error "Illegal argument for makeImpl in parsing of hybrid formulas"

instance TermParser HPAR_AS.HFORMULA where
    termParser = aToTermParser hFormula

quant :: AParser st (HPAR_AS.HQUANT, Token)
quant = choice (map (\ (q, s) -> do
    t <- asKey s
    return (q, t))
  [ (HPAR_AS.HExistential, hExistsS)
  , (HPAR_AS.HUniversal, hForallS) ])
  <?> "quantifier"


