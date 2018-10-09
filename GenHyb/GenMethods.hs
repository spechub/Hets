{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, ExistentialQuantification, DeriveDataTypeable #-}
{- |
Module      :  ./GenHyb/GenMethods
Description :  Instance of class Logic for rigid CASL


Instance of class Logic for rigid logic.
-}

module GenHyb.GenMethods where

import qualified GenHyb.GenTypes as GTypes
import Common.SetColimit
import Logic.Logic
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Graph.Inductive.Graph as Graph
import Common.Lib.Graph
import Common.Id as Id
import Data.List(nub)
import Common.AS_Annotation as AS_Anno
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Formula as CFormula
import Common.Result
import Common.Utils (composeMap)
import Common.Parsec
import Common.AnnoState
import Common.Lexer
import Common.Token
import Common.Keywords
import Common.ExtSign
import Common.GlobalAnnotations
import Control.Monad (foldM)
import qualified Common.Lib.State as CState
import Text.ParserCombinators.Parsec
import Data.Maybe (fromJust)
import Logic.SemConstr

import Debug.Trace

--TODO:
-- sort the methods coming from Static 
-- in Syntax - parse_symb_items, parse_symb_map_items, symb_items_name
-- in Static - stat_symb_items, stat_symb_map_items,
-- intersection, final_union, morphism_union,
-- generated_sign, cogenerated_sign, induced_from_morphism, induced_from_to_morphism, sen_analysis

-- for class Category

idMor :: (Category sig mor) => 
       GTypes.HSign sig -> GTypes.HMorphism sig mor
idMor hsig = GTypes.HMorphism hsig hsig (ide $ GTypes.baseSig hsig) Map.empty Map.empty

isHIncl :: (Category sig mor) => 
           GTypes.HMorphism sig mor -> Bool
isHIncl hmor = isInclusion (GTypes.baseMor hmor) && 
               Map.null (GTypes.nomMap hmor) && 
               Map.null (GTypes.modMap hmor)

compHMor :: (Category sig mor) => 
            GTypes.HMorphism sig mor -> GTypes.HMorphism sig mor -> Result (GTypes.HMorphism sig mor)
compHMor mor1 mor2 = 
 if GTypes.target mor1 == GTypes.source mor2 then do
  bmor <- composeMorphisms (GTypes.baseMor mor1) (GTypes.baseMor mor2)
  return $ GTypes.HMorphism (GTypes.source mor1) (GTypes.target mor2) 
                            bmor 
                            (composeMap (Map.fromSet id $ GTypes.noms $ GTypes.source mor1)(GTypes.nomMap mor1)(GTypes.nomMap mor2)) 
                            (composeMap (GTypes.mods $ GTypes.source mor1)(GTypes.modMap mor1)(GTypes.modMap mor2))
 else fail $ "cannot compose HMorphisms: signatures don't match" 

{- will write the following instance:
instance 
  Category (GTypes.HSign sig) (GTypes.HMorphism sig mor)
 where
    dom = GTypes.source
    cod = GTypes.target
    ide = GMethods.idMor
    isInclusion = GMethods.isHIncl
    composeMorphisms = GMethods.compHMor
-}

-- for class Syntax

parseHBasicSpecEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      =>           Bool -- admits quantification on nominals 
                -> Bool -- admits quantification on symbols of base logic
                -> lid -- lid for base logic
                -> PrefixMap ->  AParser st (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
parseHBasicSpecEng hasQNominals kVars baseLid _ks =
  fmap GTypes.Basic_spec (annosParser (parseBasicItemsEng hasQNominals kVars baseLid))  -- TODO: pass baseLid, it's easier to call functions from WriteFile
  <|> (oBraceT >> cBraceT >> return (GTypes.Basic_spec []))

parseHBasicSpec :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      =>           Bool -- admits quantification on nominals 
                -> Bool -- admits quantification on symbols of base logic
                -> lid -- lid for base logic
                -> PrefixMap ->  AParser st (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
parseHBasicSpec hasQNominals kVars baseLid _ks =
  fmap GTypes.Basic_spec (annosParser (parseBasicItems hasQNominals kVars baseLid))  -- TODO: pass baseLid, it's easier to call functions from WriteFile
  <|> (oBraceT >> cBraceT >> return (GTypes.Basic_spec []))
  {- where 
    fparser = case parse_prim_formula baseLid of
                Nothing -> error $ "no prim formula parser for logic " ++ show baseLid
                Just f -> f
    symParser = case parse_symb_items baseLid of
                  Nothing -> error $ "no symbol parser for logic " ++ show baseLid
                  Just f -> f
  -} 

parseBasicItems :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.H_BASIC_ITEMS sen symb_items raw_sym) -- TODO: take into account ks
parseBasicItems hasQNominals kVars baseLid = 
     parseAxItems hasQNominals kVars baseLid -- if this is not first, the parser for basic items consumes more than it should
  <|>
  do (as, ps) <- keyThenList nomP simpleId
     return $ GTypes.Nom_decl $ GTypes.Nom_item as ps
  <|>
  do (as, ps) <- keyThenList modP simpleId
     _c <- colonT
     ni <- getNumber
     let i = read ni :: Int
     return $ GTypes.Mod_decl $ GTypes.Mod_item as i ps

parseBasicItemsEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.H_BASIC_ITEMS sen symb_items raw_sym) -- TODO: take into account ks
parseBasicItemsEng hasQNominals kVars baseLid = 
     parseAxItemsEng hasQNominals kVars baseLid -- if this is not first, the parser for basic items consumes more than it should
  <|>
  do (as, ps) <- keyThenList nomPEng simpleId
     return $ GTypes.Nom_decl $ GTypes.Nom_item as ps
  <|>
  do (as, ps) <- keyThenList modPEng simpleId
     _c <- colonT
     ni <- getNumber
     let i = read ni :: Int
     return $ GTypes.Mod_decl $ GTypes.Mod_item as i ps

modP :: AParser st Token
modP = asKey modalityS <|> asKey modalitiesS

modPEng :: AParser st Token
modPEng = asKey "event" <|> asKey "events"

nomP :: AParser st Token
nomP = asKey nominalS <|> asKey nominalsS

nomPEng :: AParser st Token
nomPEng = asKey "state" <|> asKey "states"

keyThenList :: AParser st Token -> AParser st a ->
           AParser st ([a], Range)
keyThenList k p = do
        c <- k
        (as, cs) <- separatedBy p anComma
        let ps = catRange $ c : cs
        return (as, ps)

parseAxItems :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.H_BASIC_ITEMS sen symb_items raw_sym)
parseAxItems hasQNominals kVars baseLid = do
       d <- dotT
       (fs, ds) <- (aFormula hasQNominals kVars baseLid) `separatedBy` dotT
       (_, an) <- optSemi
       let _ = catRange (d : ds)
           ns = init fs ++ [appendAnno (last fs) an]
       return $ GTypes.Axiom_items ns

parseAxItemsEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.H_BASIC_ITEMS sen symb_items raw_sym)
parseAxItemsEng hasQNominals kVars baseLid = do
       d <- dotT
       (fs, ds) <- (aFormulaEng hasQNominals kVars baseLid) `separatedBy` dotT
       (_, an) <- optSemi
       let _ = catRange (d : ds)
           ns = init fs ++ [appendAnno (last fs) an]
       -- trace ("fs:" ++ show fs) $ 
       return $ GTypes.Axiom_items ns

-- | parser for annoted formulae
aFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (Annoted (GTypes.HFORMULA sen symb_items raw_sym))
aFormula hasQNominals kVars baseLid = allAnnoParser (topformula hasQNominals kVars baseLid)

aFormulaEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (Annoted (GTypes.HFORMULA sen symb_items raw_sym))
aFormulaEng hasQNominals kVars baseLid = allAnnoParser (topformulaEng hasQNominals kVars baseLid)


-- | toplevel formula parser
topformula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
topformula hasQNominals kVars baseLid = (andOrFormula hasQNominals kVars baseLid) >>= (optImplForm hasQNominals kVars baseLid)

topformulaEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
topformulaEng hasQNominals kVars baseLid = (andOrFormulaEng hasQNominals kVars baseLid) >>= (optImplFormEng hasQNominals kVars baseLid)

andOrFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
andOrFormula hasQNominals kVars baseLid = (hFormula hasQNominals kVars baseLid) >>= (optAndOr hasQNominals kVars baseLid)

andOrFormulaEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
andOrFormulaEng hasQNominals kVars baseLid = (hFormulaEng hasQNominals kVars baseLid) >>= (optAndOrEng hasQNominals kVars baseLid)

optImplForm :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> GTypes.HFORMULA sen symb_items raw_sym -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
optImplForm hasQNominals kVars baseLid f = do
      _c <- CFormula.implKey
      (fs, _ps) <- (andOrFormula hasQNominals kVars baseLid) `separatedBy` CFormula.implKey --TODO: range?
      return $ makeImpl (f : fs)
    <|> do
      c <- asKey equivS
      g <- andOrFormula hasQNominals kVars baseLid
      return $ GTypes.Equivalence f g $ tokPos c
    <|> return f

optImplFormEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> GTypes.HFORMULA sen symb_items raw_sym -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
optImplFormEng hasQNominals kVars baseLid f = do
      _c <- CFormula.implKey
      (fs, _ps) <- (andOrFormulaEng hasQNominals kVars baseLid) `separatedBy` CFormula.implKey --TODO: range?
      return $ makeImpl (f : fs)
    <|> do
      c <- asKey equivS
      g <- andOrFormulaEng hasQNominals kVars baseLid
      return $ GTypes.Equivalence f g $ tokPos c
    <|> return f

makeImpl :: [GTypes.HFORMULA sen symb_items raw_sym] -> GTypes.HFORMULA sen symb_items raw_sym
makeImpl l = 
 case l of 
  [f1, f2] -> GTypes.Implication f1 f2 nullRange
  f1 : fs  -> GTypes.Implication f1 (makeImpl fs) nullRange
  _ -> error "Illegal argument for makeImpl in parsing of hybrid formulas"


optAndOr :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> GTypes.HFORMULA sen symb_items raw_sym -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
optAndOr hasQNominals kVars baseLid f = do
      c <- CFormula.andKey
      (fs, ps) <- (hFormula hasQNominals kVars baseLid) `separatedBy` CFormula.andKey
      return $ GTypes.Conjunction (f : fs) $ catRange $ c : ps
    <|> do
      c <- CFormula.orKey
      (fs, ps) <- (hFormula hasQNominals kVars baseLid) `separatedBy` CFormula.orKey
      return $ GTypes.Disjunction (f : fs) $ catRange $ c : ps
    <|> return f

optAndOrEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> GTypes.HFORMULA sen symb_items raw_sym -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
optAndOrEng hasQNominals kVars baseLid f = do
      c <- CFormula.andKey
      (fs, ps) <- (hFormulaEng hasQNominals kVars baseLid) `separatedBy` CFormula.andKey
      return $ GTypes.Conjunction (f : fs) $ catRange $ c : ps
    <|> do
      c <- CFormula.orKey
      (fs, ps) <- (hFormulaEng hasQNominals kVars baseLid) `separatedBy` CFormula.orKey
      return $ GTypes.Disjunction (f : fs) $ catRange $ c : ps
    <|> return f

hFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
hFormula hasQNominals kVars baseLid = 
   do 
      c <- atKey
      n <- simpleId
      _ <- colonT
      f <- topformula hasQNominals kVars baseLid -- here should be formula without @?
      return $ GTypes.AtState n f $ tokPos c
 <|> 
   do
    c <- asKey notS <|> asKey negS <?> "\"not\""
    f <- hFormula hasQNominals kVars baseLid --topformula
    return $ GTypes.Negation f $ tokPos c
   <|>
     do
        c1 <- asKey lessS
        md <- propId [greaterS]
        c2 <- asKey greaterS
        f <- topformula hasQNominals kVars baseLid
        return $ GTypes.DiamondFormula md f $ toRange c1 [] c2
 <|>
     do
        c1 <- oBracketT
        md <- propId ["]"]
        c2 <- cBracketT
        f <- topformula hasQNominals kVars baseLid
        return $ GTypes.BoxFormula md f $ toRange c1 [] c2
 <|> 
     parenFormula hasQNominals kVars baseLid
 <|>
     do
       (q, p) <- quant
       parseQFormula hasQNominals kVars baseLid (q, p)
 <|>
     do 
        let fparser = case parse_prim_formula baseLid of
                Nothing -> error $ "no prim formula parser for logic " ++ show baseLid
                Just f -> f
        f <- fparser 
        return $ GTypes.Base_formula f nullRange    
        -- this should also catch nominals as terms. 
        -- We have to make sure during static analysis that this is reverted!
 <|> do -- qualified symbols are nominals
       nom <- simpleId
       _ <- asKey "::"
       qual <- simpleId
       return $ GTypes.Nominal (show qual) False nom nullRange -- TODO: always False here, no qualifications for variables

hFormulaEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
hFormulaEng hasQNominals kVars baseLid = 
   do 
      c <- atKeyEng
      n <- simpleId
      _ <- colonT
      f <- topformulaEng hasQNominals kVars baseLid -- here should be formula without @?
      return $ GTypes.AtState n f $ tokPos c
 <|> 
   do
    c <- asKey notS <|> asKey negS <?> "\"not\""
    f <- hFormulaEng hasQNominals kVars baseLid --topformula
    return $ GTypes.Negation f $ tokPos c
   <|>
     do
        c1 <- asKey "Through" --lessS
        md <- propId ["sometimes", "always"]
        _ <- commaT
        sen <- do
                 c2 <- asKey "sometimes" 
                 f <- topformulaEng hasQNominals kVars baseLid
                 return $ GTypes.DiamondFormula md f $ toRange c1 [] c2
               <|> do
                 c2 <- asKey "always" 
                 f <- topformulaEng hasQNominals kVars baseLid
                 return $ GTypes.BoxFormula md f $ toRange c1 [] c2
        return sen
 <|> 
     parenFormulaEng hasQNominals kVars baseLid
 <|>
     do
       (q, p) <- quant
       parseQFormulaEng hasQNominals kVars baseLid (q, p)
 <|>
     do 
        let fparser = case parse_prim_formula baseLid of
                Nothing -> error $ "no prim formula parser for logic " ++ show baseLid
                Just f -> f
        f <- fparser 
        return $ GTypes.Base_formula f nullRange    
        -- this should also catch nominals as terms. 
        -- We have to make sure during static analysis that this is reverted!
 <|> do -- qualified symbols are nominals
       nom <- simpleId
       _ <- asKey "::"
       qual <- simpleId
       return $ GTypes.Nominal (show qual) False nom nullRange -- TODO: always False here, no qualifications for variables


parenFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
parenFormula hasQNominals kVars baseLid = do
       oParenT << addAnnos
       f <- topformula hasQNominals kVars baseLid << addAnnos
       cParenT >> return f

parenFormulaEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
parenFormulaEng hasQNominals kVars baseLid = do
       oParenT << addAnnos
       f <- topformulaEng hasQNominals kVars baseLid << addAnnos
       cParenT >> return f

quant :: AParser st (GTypes.HQUANT, Token)
quant = choice (map (\ (q, s) -> do
    t <- asKey s
    str <- do 
     _ <- asKey "::"
     qual <- simpleId
     return $ show qual
     <|> do
     return ""
    return (q str, t))
  [ (GTypes.HExistential, hExistsS)
  , (GTypes.HUniversal,   hForallS) ])
  <?> "quantifier" 

parseQFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> (GTypes.HQUANT, Token) -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
parseQFormula hasQNominals kVars baseLid (q, p) = 
  do -- first try quantification on nominals, or the parser will complain 
     (vs, _ps) <- keyThenList nomP simpleId
     _d <- dotT -- TODO: range
     f <- topformula hasQNominals kVars baseLid
     if hasQNominals then 
      return $ GTypes.QuantNominals q vs f nullRange
     else error $ "the logic does not admit quantification on nominals"
    <|> 
  do 
     let symParser = case parse_symb_items baseLid of
                  Nothing -> error $ "no symbol parser for logic " ++ show baseLid
                  Just f -> f
     (sitems, ps) <- symParser `separatedBy` commaT
     d <- dotT
     f <- topformula hasQNominals kVars baseLid
     if kVars then 
      return $ GTypes.QuantVarsParse q sitems f $ toRange p ps d
     else error $ "the logic does not admit quantification on base symbols"

parseQFormulaEng :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> lid -> (GTypes.HQUANT, Token) -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
parseQFormulaEng hasQNominals kVars baseLid (q, p) = 
  do -- first try quantification on nominals, or the parser will complain 
     (vs, _ps) <- keyThenList nomPEng simpleId
     _d <- dotT -- TODO: range
     f <- topformulaEng hasQNominals kVars baseLid
     if hasQNominals then 
      return $ GTypes.QuantNominals q vs f nullRange
     else error $ "the logic does not admit quantification on nominals"
    <|> 
  do 
     let symParser = case parse_symb_items baseLid of
                  Nothing -> error $ "no symbol parser for logic " ++ show baseLid
                  Just f -> f
     (sitems, ps) <- symParser `separatedBy` commaT
     d <- dotT
     f <- topformulaEng hasQNominals kVars baseLid
     if kVars then 
      return $ GTypes.QuantVarsParse q sitems f $ toRange p ps d
     else error $ "the logic does not admit quantification on base symbols"


-- | Any word to token
propId :: [String] -> GenParser Char st Token
propId k = pToken $ reserved (k ++ hybrid_keywords) scanAnyWords

-- | Parser for at 
atKey :: AParser st Token
atKey = asKey asP

-- | Parser for at, eng
atKeyEng :: AParser st Token
atKeyEng = asKey "At state"


{-
will write the following instance:

instance Syntax lid (H_BASIC_SPEC sen) (HSymbol sym) (H_SYMB_ITEMS kind sym) symb_map_items
 where 
  parse_basic_spec lid  = case (parse_formula baseLid, parse_symb_items baseLid) of 
                             (Just f, Just g) -> Just $ parseHBasicSpec f g
                             _ -> Nothing
  parse_symb_items lid = error "parse symb items nyi" -- Just $ symbItems [rigidS]
  parse_symb_map_items lid = error "parse symb map items nyi" -- Just $ symbMapItems hybrid_reserved_words
-}

-- for class Sentences

mapSentence :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
            => lid -> 
               GTypes.HMorphism sig mor -> GTypes.HFORMULA sen symb_items raw_sym -> Result (GTypes.HFORMULA sen symb_items raw_sym)
mapSentence baseLid hmor hsen =
 case hsen of
  GTypes.Base_formula sen _ -> do
    sen' <- map_sen baseLid (GTypes.baseMor hmor) sen
    return $ GTypes.Base_formula sen' nullRange
  GTypes.Negation hsen' _ -> do
    hsen'' <- mapSentence baseLid hmor hsen'
    return $ GTypes.Negation hsen'' nullRange
  GTypes.Conjunction hsens _ -> do
    hsens' <- mapM (mapSentence baseLid hmor) hsens
    return $ GTypes.Conjunction hsens' nullRange
  GTypes.Disjunction hsens _ -> do
    hsens' <- mapM (mapSentence baseLid hmor) hsens
    return $ GTypes.Disjunction hsens' nullRange
  GTypes.Implication hsen1 hsen2 _ -> do
    tsen1 <- mapSentence baseLid hmor hsen1
    tsen2 <- mapSentence baseLid hmor hsen2
    return $ GTypes.Implication tsen1 tsen2 nullRange
  GTypes.Equivalence hsen1 hsen2 _ -> do
    tsen1 <- mapSentence baseLid hmor hsen1
    tsen2 <- mapSentence baseLid hmor hsen2
    return $ GTypes.Equivalence tsen1 tsen2 nullRange
  GTypes.Nominal s b n _ -> 
     if b then return hsen
     else let n0 = simpleIdToId n
              n' = Map.findWithDefault n0 n0 $ GTypes.nomMap hmor
          in return $ GTypes.Nominal s b (idToSimpleId n') nullRange
  GTypes.AtState n hsen' _ -> do
    tsen' <- mapSentence baseLid hmor hsen'
    let n0 = simpleIdToId n
        n' = idToSimpleId $ Map.findWithDefault n0 n0 $ GTypes.nomMap hmor
    return $ GTypes.AtState n' tsen' nullRange
  GTypes.BoxFormula m hsen' _ -> do 
    tsen' <- mapSentence baseLid hmor hsen'
    let m0 = simpleIdToId m
        m' = idToSimpleId $ Map.findWithDefault m0 m0 $ GTypes.modMap hmor
    return $ GTypes.BoxFormula m' tsen' nullRange
  GTypes.DiamondFormula m hsen' _ -> do 
    tsen' <- mapSentence baseLid hmor hsen'
    let m0 = simpleIdToId m
        m' = idToSimpleId $ Map.findWithDefault m0 m0 $ GTypes.modMap hmor
    return $ GTypes.DiamondFormula m' tsen' nullRange
  GTypes.QuantNominals hq noms hsen' _ -> do
    tsen' <- mapSentence baseLid hmor hsen'
    return $ GTypes.QuantNominals hq noms tsen' nullRange
  GTypes.QuantVarsParse _ _ _ _ -> error "cannot translate a sentence before it was analyzed"
  GTypes.QuantVars hq rsyms hsen' _ -> do
    {-
               hincl (generated by rsyms)
       ssig  .......> ssig'
        |               |
        | hmor          | hmor'
        |               |
        V               V
       tsig ........> csig

       Then Sen(hmor) (forall rsyms.e) =
            forall (rsyms') hmor'(e)
       where rsyms' are the symbols of csig \ tsig  
  
    -}
    let mSyms = convertRawSyms baseLid rsyms
    case mSyms of
     Nothing -> error $ "could not convert symbols in quantification when translating sentence"
     Just syms -> do
      let ssig = GTypes.source hmor
          tsig = GTypes.target hmor
      ssig' <- foldM (addSymbToHSign baseLid) ssig $ 
               map GTypes.BaseSymb syms
      hincl <- subsigInclusion baseLid ssig ssig'
      let spanGr = Graph.mkGraph [(0, ssig), (1, ssig'), (2, tsig)] [(0, 1, (0, hincl)), (0, 2, (1, hmor))]
      (csig, cmors) <- signatureColimit baseLid spanGr
      let hmor'  = Map.findWithDefault (error "cmor  missing") 1 cmors
          -- cincl = Map.findWithDefault (error "cincl missing") 2 cmors
      dsig <- signatureDifference baseLid csig tsig
      let rsyms' = map (symbol_to_raw baseLid) $ mostSymsOf baseLid $ GTypes.baseSig dsig
                                               -- only base symbols, so we don't lose anything here
      tsen' <- mapSentence baseLid hmor' hsen'
      return $ GTypes.QuantVars hq rsyms' tsen' nullRange

mostSymsOfDiff :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
    => lid -> GTypes.HSign sig -> [GTypes.HSymbol sym]
mostSymsOfDiff baseLid hsig = let 
  bsyms = map GTypes.BaseSymb $ mostSymsOf baseLid $ GTypes.baseSig hsig
  nsyms = map (\n -> GTypes.HSymb n GTypes.Nom) $ Set.toList $ GTypes.noms hsig
  msyms = map (\(m,i) -> GTypes.HSymb m (GTypes.Mod i)) $ Map.toList $ GTypes.mods hsig
 in bsyms ++ nsyms ++ msyms

signatureDifference :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
    => lid -> GTypes.HSign sig -> GTypes.HSign sig -> Result (GTypes.HSign sig)
signatureDifference baseLid hsig1 hsig2 = do 
 bDiff <- signatureDiff baseLid (GTypes.baseSig hsig1) $ GTypes.baseSig hsig2
 return $ GTypes.HSign bDiff 
                       (Set.difference (GTypes.noms hsig1) $ GTypes.noms hsig2) 
                       (Map.difference (GTypes.mods hsig1) $ GTypes.mods hsig2)

subsigInclusion :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
    => lid -> GTypes.HSign sig -> GTypes.HSign sig -> Result (GTypes.HMorphism sig mor)
subsigInclusion baseLid ssig ssig' = do 
   bmor <- subsig_inclusion baseLid (GTypes.baseSig ssig) $ GTypes.baseSig ssig'
   return $ GTypes.HMorphism ssig ssig' bmor Map.empty Map.empty

addSymbToHSign :: Logic lid sublogics basic_spec sen
                   symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
      => lid -> GTypes.HSign sig -> GTypes.HSymbol sym -> Result (GTypes.HSign sig)
addSymbToHSign baseLid hsig s =
 case s of 
  GTypes.BaseSymb bs -> do 
    bsig <- add_symb_to_sign baseLid (GTypes.baseSig hsig) bs 
    return $ hsig {GTypes.baseSig = bsig}
  GTypes.HSymb i k -> 
   case k of
    GTypes.Nom -> addNomToSig hsig i
    GTypes.Mod a -> addModToSig hsig i a

signatureColimit :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
  => lid -> Gr (GTypes.HSign sig) (Int, GTypes.HMorphism sig mor) -> 
            Result (GTypes.HSign sig, Map.Map Int (GTypes.HMorphism sig mor))
signatureColimit baseLid hgr = do
 let bgr = emap (\(i, m) -> (i, GTypes.baseMor m)) $ nmap GTypes.baseSig hgr
 (cbsig, cbmors) <- signature_colimit baseLid bgr
 let ngr = emap (\(i, m) -> (i, GTypes.nomMap m)) $ nmap GTypes.noms hgr
     (nomSet0, nomFuns0) = computeColimitSet ngr
     (nomSet, nomFuns) = addIntToSymbols (nomSet0, nomFuns0)
     csig = GTypes.HSign cbsig nomSet Map.empty
     cmors = Map.fromList $ map (\(n, hsig) -> (n, GTypes.HMorphism
                                                 hsig csig 
                                                 (Map.findWithDefault (error "missing morphism") n cbmors) 
                                                 (Map.findWithDefault Map.empty n nomFuns) 
                                                 Map.empty
                                           )
                            ) 
             $ labNodes hgr
    -- TODO: colimit on modalities!
 return (csig, cmors)

hNegation :: GTypes.HFORMULA sen symb_items raw_sym -> Maybe (GTypes.HFORMULA sen symb_items raw_sym)
hNegation hsen = Just $ GTypes.Negation hsen nullRange

hSymOf :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
   => lid -> GTypes.HSign sig -> [Set.Set (GTypes.HSymbol sym)]
hSymOf baseLid hsig = 
 let bSyms = sym_of baseLid $ GTypes.baseSig hsig
     nSyms = GTypes.noms hsig
     mSyms = GTypes.mods hsig
 in [Set.map (\x -> GTypes.HSymb x GTypes.Nom) nSyms] ++
    [Set.fromList $ map (\(m,i) -> GTypes.HSymb m (GTypes.Mod i)) $ Map.toList mSyms] ++
    map (\ss -> Set.map (\s -> GTypes.BaseSymb s) ss) bSyms

hSymMapOf :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => lid -> GTypes.HMorphism sig mor -> EndoMap (GTypes.HSymbol sym)
hSymMapOf baseLid hmor = 
 let mkBSymMap f = Map.mapKeys (\x -> GTypes.BaseSymb x) $ Map.map (\x -> GTypes.BaseSymb x) f
     bMap = mkBSymMap $ symmap_of baseLid $ GTypes.baseMor hmor
     nMap = Map.mapKeys (\x -> GTypes.HSymb x GTypes.Nom) $ Map.map (\x -> GTypes.HSymb x GTypes.Nom) $ GTypes.nomMap hmor
     mMap = Map.mapKeys (\x -> let i = Map.findWithDefault (error $ "unknown modality: " ++ show x) x $ GTypes.mods $ GTypes.source hmor
                               in GTypes.HSymb x (GTypes.Mod i)) $ 
            Map.map     (\x -> let i = Map.findWithDefault (error $ "unknown modality: " ++ show x) x $ GTypes.mods $ GTypes.target hmor
                               in GTypes.HSymb x (GTypes.Mod i)) $ GTypes.modMap hmor
 in Map.union bMap $ Map.union nMap mMap    

hSymName :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => lid -> GTypes.HSymbol sym -> Id
hSymName baseLid (GTypes.BaseSymb x) = sym_name baseLid x
hSymName _ (GTypes.HSymb x _) = x

symKindH :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => lid -> GTypes.HSymbol sym -> String
symKindH baseLid s = 
 case s of 
  GTypes.BaseSymb x -> symKind baseLid x
  GTypes.HSymb _ (GTypes.Nom) -> "nominal"
  GTypes.HSymb _ (GTypes.Mod _) -> "modality"

extSymKindH :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => lid -> GTypes.HSymbol sym -> String -- TODO: add to logic instance
extSymKindH baseLid s = 
 case s of 
  GTypes.BaseSymb x -> extSymKind baseLid x
  GTypes.HSymb _ (GTypes.Nom) -> "nominal"
  GTypes.HSymb _ (GTypes.Mod _) -> "modality"

symsOfHSen :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => 
              lid -> 
              GTypes.HSign sig -> GTypes.HFORMULA sen symb_items raw_sym -> [GTypes.HSymbol sym]
symsOfHSen baseLid hsig hsen = 
 case hsen of 
   GTypes.Base_formula sen _ -> let bSyms = symsOfSen baseLid (GTypes.baseSig hsig) sen 
                                in map (\s -> GTypes.BaseSymb s) bSyms
   GTypes.Negation hsen' _ -> symsOfHSen baseLid hsig hsen'
   GTypes.Conjunction hsens _ -> nub $ concatMap (symsOfHSen baseLid hsig) hsens
   GTypes.Disjunction hsens _ -> nub $ concatMap (symsOfHSen baseLid hsig) hsens
   GTypes.Implication hsen1 hsen2 _ -> nub $ (symsOfHSen baseLid hsig hsen1) ++ (symsOfHSen baseLid hsig hsen2)
   GTypes.Equivalence hsen1 hsen2 _ -> nub $ (symsOfHSen baseLid hsig hsen1) ++ (symsOfHSen baseLid hsig hsen2)
   GTypes.Nominal _ b n _ -> if b then [] else [GTypes.HSymb (simpleIdToId n) GTypes.Nom] -- TODO: ok to have empty list of syms for variables?
   GTypes.AtState n hsen' _ -> let syms = symsOfHSen baseLid hsig hsen' in (GTypes.HSymb (simpleIdToId n) GTypes.Nom):syms  
   GTypes.BoxFormula m hsen' _ -> let syms = symsOfHSen baseLid hsig hsen' 
                                      k = GTypes.Mod (2::Int)
                                  in (GTypes.HSymb (simpleIdToId m) k):syms
   GTypes.DiamondFormula m hsen' _ -> let syms = symsOfHSen baseLid hsig hsen' 
                                          k = GTypes.Mod (2::Int)
                                      in (GTypes.HSymb (simpleIdToId m) k):syms
   GTypes.QuantNominals _hq _noms hsen' _ -> symsOfHSen baseLid hsig hsen' -- TODO:vars?
   GTypes.QuantVars _hq _vars hsen' _ -> symsOfHSen baseLid hsig hsen' -- TODO:vars?
   GTypes.QuantVarsParse _hq _vars _hsen' _ -> error $ "unparsed sentence"

rawToSymbol :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => 
              lid -> GTypes.HRawSymbol sym raw_sym -> Maybe (GTypes.HSymbol sym)
rawToSymbol baseLid rsym =
 case rsym of
  GTypes.BaseRawSymbol brsym -> 
   let msym = raw_to_symbol baseLid brsym
   in case msym of
       Nothing -> Nothing
       Just sym -> Just $ GTypes.BaseSymb sym
  GTypes.ASymbol x -> Just x
  GTypes.AKindedSymb gk i -> 
    case gk of
     GTypes.Implicit -> Nothing 
     GTypes.HKindAsG hk -> Just $ GTypes.HSymb i hk

idToRaw :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => 
              lid -> Id -> GTypes.HRawSymbol sym raw_sym
idToRaw baseLid anId = 
  let baseRawSym = id_to_raw baseLid anId
  in GTypes.BaseRawSymbol baseRawSym

emptyHSign :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => 
              lid -> GTypes.HSign sig
emptyHSign baseLid = 
 let emptyBSign = empty_signature baseLid
 in GTypes.HSign emptyBSign Set.empty Map.empty

sigUnion :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => 
              lid -> GTypes.HSign sig -> GTypes.HSign sig -> Result (GTypes.HSign sig)
sigUnion baseLid hsig1 hsig2 = do
 bsig <- signature_union baseLid (GTypes.baseSig hsig1) $ GTypes.baseSig hsig2
 let uNoms = Set.union (GTypes.noms hsig1) $ GTypes.noms hsig2
     uMods = Map.union (GTypes.mods hsig1) $ GTypes.mods hsig2 -- TODO: fail if a modality appears in both sigs with different arities?
 return $ GTypes.HSign bsig uNoms uMods 

isSubsig :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => 
              lid -> GTypes.HSign sig -> GTypes.HSign sig -> Bool
isSubsig baseLid sig1 sig2 = 
  (is_subsig baseLid (GTypes.baseSig sig1) $ GTypes.baseSig sig1) &&
  (Set.isSubsetOf (GTypes.noms sig1) $ GTypes.noms sig2) &&
  (Map.isSubmapOf (GTypes.mods sig1) $ GTypes.mods sig2)
-- for StaticAnalysis

data HTheoryAna sig sen symb_items raw_sym sym = HTheoryAna {
                   hSign :: GTypes.HSign sig,
                   declSyms :: Set.Set (GTypes.HSymbol sym),
                   hSens :: [Named (GTypes.HFORMULA sen symb_items raw_sym)],
                   hVars :: [GTypes.HRawSymbol sym raw_sym],
                   globAnnos :: GlobalAnnos,
                   anaDiags :: [Diagnosis]
                   }
      deriving Show

basicHAnalysis :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> -- flag: has quantification on nominals? 
         [String] -> -- kinds allowed in quantification on base symbols, empty for none
         lid -> -- lid of the base logic, to call methods in Logic class
         Maybe sublogics -> -- if we make the hybridization of a sublogic, check that the case theory lives in that sublogic
         (GTypes.H_BASIC_SPEC sen symb_items raw_sym, GTypes.HSign sig, GlobalAnnos) ->
         Result (GTypes.H_BASIC_SPEC sen symb_items raw_sym, ExtSign (GTypes.HSign sig) (GTypes.HSymbol sym), [Named (GTypes.HFORMULA sen symb_items raw_sym)])
basicHAnalysis hasQNominals kVars baseLid mSubl (bs, inSig, ga) = let
  hth = HTheoryAna inSig Set.empty [] [] ga []
  (newBs, accTh) = CState.runState (anaBasicHSpec hasQNominals kVars baseLid bs) hth
  ds = reverse $ anaDiags accTh
  outSig = hSign accTh
  sents = hSens accTh
  (baseSig, baseSens) = (GTypes.baseSig outSig, concatMap (\s -> case sentence s of
                                                                 GTypes.Base_formula f _ -> [f]
                                                                 _ -> []) sents)
 in case mSubl of 
     Nothing -> -- trace ("sents:" ++ show sents) $ 
                Result ds $ Just (newBs, ExtSign outSig $ declSyms accTh, sents)
     Just aSub -> -- trace ("aSub:" ++ show aSub ++ " " ++ "sents:" ++ show sents) $ 
                  do 
       let tSub = sublogicOfTheo baseLid (baseSig, baseSens)
       if isSubElem tSub aSub then -- trace ("tSub:" ++ show tSub ++ " baseSens:" ++ show baseSens) $ 
                                   Result ds $ Just (newBs, ExtSign outSig $ declSyms accTh, sents)
                              else fail $ "The sublogic of the analyzed theory should be " ++ show aSub ++ "but it is " ++ show tSub

anaBasicHSpec :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
      =>  Bool -> [String] -> lid
       -> GTypes.H_BASIC_SPEC sen symb_items raw_sym
       -> CState.State (HTheoryAna sig sen symb_items raw_sym sym) (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
anaBasicHSpec hasQNominals kVars baseLid (GTypes.Basic_spec al) = fmap GTypes.Basic_spec $
      mapAnM (anaBasicHItems hasQNominals kVars baseLid) al

anaBasicHItems :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
      => Bool -> [String] -> lid
      -> GTypes.H_BASIC_ITEMS sen symb_items raw_sym
      -> CState.State (HTheoryAna sig sen symb_items raw_sym sym) (GTypes.H_BASIC_ITEMS sen symb_items raw_sym) 
anaBasicHItems hasQNominals kVars baseLid bi = 
 case bi of
  GTypes.Nom_decl (GTypes.Nom_item noms _) -> do 
    hth <- CState.get
    let hsign = hSign hth
    let Result ds mhsign' = foldM (\s n -> addNomToSig s $ mkId [n]) hsign noms
    case mhsign' of 
     Nothing -> error $ "cannot add nominals" ++ show ds
     Just hsign' -> do
      CState.put $ hth {hSign = hsign', anaDiags = ds ++ anaDiags hth}
      return bi
  GTypes.Mod_decl (GTypes.Mod_item mods i _) -> do
    hth <- CState.get
    let hsign = hSign hth 
    let Result ds mhsign' = foldM (\s m -> addModToSig s (mkId [m]) i) hsign mods 
    case mhsign' of
      Nothing -> error $ "cannot add modalities" ++ show ds
      Just hsign' -> do  
       CState.put $ hth { hSign = hsign', anaDiags = ds ++ anaDiags hth } 
       return bi
  GTypes.Axiom_items annofs -> do
    hth <- CState.get
    let (hth', annofs') = foldl (\(h, l) f -> let (f', h') = trace ("f:" ++ show (item f)) $ CState.runState 
                                                              (anaHFORMULA hasQNominals kVars
                                                               baseLid f) h
                                              in (h', f':l)) (hth, []) annofs 
    let replfs = reverse annofs'
        nfs = map (makeNamedSen.snd) replfs
    CState.put $ hth' {hSens = nfs ++ hSens hth'}
    return $ GTypes.Axiom_items $ map fst replfs

-- | Adds a nominal to the signature
addNomToSig :: GTypes.HSign sig -> Id -> Result (GTypes.HSign sig)
addNomToSig sig nom = 
 let 
  snoms = GTypes.noms sig
 in if Set.member nom snoms then 
      Result [mkDiag Warning "redeclaring nominal" nom] $ Just sig
    else return sig {GTypes.noms = Set.insert nom snoms}

-- | Adds a modality to the signature
addModToSig :: GTypes.HSign sig -> Id -> Int -> Result (GTypes.HSign sig)
addModToSig sig md ar = 
 let
  smods = GTypes.mods sig
 in if Map.member md smods then 
       Result [mkDiag Warning "redeclaring modality" md] $ Just sig  
     else return sig {GTypes.mods = Map.insert md ar smods}

-- | sentence simplification

simplifyHSen :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
   => lid ->  GTypes.HSign sig -> GTypes.HFORMULA sen symb_items raw_sym -> GTypes.HFORMULA sen symb_items raw_sym
simplifyHSen baseLid hsig hsen = 
 case hsen of 
  GTypes.Base_formula pfrm r -> 
    let pfrm' = simplify_sen baseLid (GTypes.baseSig hsig) pfrm
    in GTypes.Base_formula pfrm' r  
  GTypes.Nominal _ _ _ _ -> 
    hsen
  GTypes.AtState nom frm r -> 
    GTypes.AtState nom (simplifyHSen baseLid hsig frm) r
  GTypes.BoxFormula md frm r -> 
    GTypes.BoxFormula md (simplifyHSen baseLid hsig frm) r
  GTypes.DiamondFormula md frm r -> 
    GTypes.DiamondFormula md (simplifyHSen baseLid hsig frm) r
  GTypes.Negation frm r -> 
    GTypes.Negation (simplifyHSen baseLid hsig frm) r
  GTypes.Conjunction xs r -> 
    GTypes.Conjunction (map (simplifyHSen baseLid hsig) xs) r
  GTypes.Disjunction xs r -> 
    GTypes.Disjunction (map (simplifyHSen baseLid hsig) xs) r
  GTypes.Implication x y r -> 
    GTypes.Implication (simplifyHSen baseLid hsig x) (simplifyHSen baseLid hsig y) r
  GTypes.Equivalence x y r -> 
    GTypes.Equivalence (simplifyHSen baseLid hsig x) (simplifyHSen baseLid hsig y) r
  GTypes.QuantVarsParse _ _ _ _ -> error "GenHyb.GenMethods.simplifyHSen: sentence not analyzed"
  GTypes.QuantVars q vdecls frm r ->  
   let Result ds msig = foldM (add_symb_to_sign baseLid) (GTypes.baseSig hsig) $ 
                        map (\x -> fromJust $ raw_to_symbol baseLid x) vdecls
   in case msig of 
       Nothing -> error $ "GenHyb.GenMethods.simplifyHSen:" ++ show ds
       Just bsig -> GTypes.QuantVars q vdecls (simplifyHSen baseLid hsig{GTypes.baseSig = bsig} frm) r
  GTypes.QuantNominals q noms frm r -> 
    GTypes.QuantNominals q noms (simplifyHSen baseLid hsig frm) r

anaHFORMULA :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
      => Bool -> [String] -> lid ->
         Annoted (GTypes.HFORMULA sen symb_items raw_sym) -> 
         CState.State (HTheoryAna sig sen symb_items raw_sym sym) 
                       (Annoted (GTypes.HFORMULA sen symb_items raw_sym), 
                        Annoted (GTypes.HFORMULA sen symb_items raw_sym)
                      )
anaHFORMULA hasQNominals kVars baseLid hf = case item hf of
 GTypes.Base_formula bsen r -> do 
   hth <- CState.get
   let (isNom, mNomName) = is_nominal_sen baseLid (GTypes.noms $ hSign hth) bsen -- isNominalSen baseLid (hSign hth) bsen
   if not isNom then do
     let senAnaBase = case sen_analysis baseLid of
                       Nothing -> error $ "sentence analysis not implemented for logic " ++ show baseLid
                       Just f -> f
         emptyBasicSpec = case convertTheory baseLid of
                            Nothing -> error $ "can't convert theory in logic " ++ show baseLid
                            Just f -> f $ (empty_signature baseLid, [])
         baseVars = concatMap (\s -> case s of 
                                      GTypes.BaseRawSymbol rs -> [rs]
                                      _ -> [] ) $ hVars hth
         baseVarsSyms = fromJust $ convertRawSyms baseLid baseVars
     let Result dadd mAnaSig = foldM (add_symb_to_sign baseLid) (GTypes.baseSig $ hSign hth) baseVarsSyms
     case mAnaSig of 
      Nothing -> do
       CState.put $ hth {anaDiags = dadd ++ anaDiags hth}
       return (hf, hf)
      Just anaSig -> do
       let Result ds mf = senAnaBase 
                           (emptyBasicSpec,
                            anaSig,
                            bsen)
       case mf of
         Nothing -> do
           CState.put $ hth {anaDiags = ds ++ anaDiags hth}
           return (hf, hf)
         Just (f1, f2) -> do
           let hf1 = hf {item = GTypes.Base_formula f1 r}
               hf2 = hf {item = GTypes.Base_formula f2 r}
           CState.put $ hth {anaDiags = ds ++ anaDiags hth}
           return (hf1, hf2) 
    else case mNomName of
          Nothing -> error "Can't have nominal formula without nominal name" -- should never happen!
          Just i -> -- trace ("i:" ++ show i) $ 
            let iNom = GTypes.ASymbol $ GTypes.HSymb i GTypes.Nom
            in if iNom `elem` hVars hth then 
                  let hf' = hf { item = GTypes.Nominal "" True (idToSimpleId i) nullRange } -- should be the top logic!
                  in return (hf', hf')
                 else if i `elem` (GTypes.noms $ hSign hth) then 
                         let hf' = hf { item = GTypes.Nominal "" False (idToSimpleId i) nullRange } -- should be the top logic
                         in return (hf', hf')
                       else do -- TODO: undeclared nominals are not identified as nominals in isNominalSen!
                          CState.put $ hth {anaDiags = (mkDiag Error "undeclared nominal" i) : (anaDiags hth) }
                          return (hf, hf)  
 GTypes.Negation f r -> do
   (af1, af2) <- anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f
   let hf'= hf { item = GTypes.Negation (item af2) r}
   return (hf{item = GTypes.Negation (item af1) r}, hf')
 GTypes.Conjunction fs r -> do 
   afs' <- mapM (anaHFORMULA hasQNominals kVars baseLid) $ map emptyAnno fs 
   return $ (hf { item = GTypes.Conjunction (map (item.fst) afs') r}, 
             hf { item = GTypes.Conjunction (map (item.snd) afs') r})
 GTypes.Disjunction fs r -> do 
   afs' <- mapM (anaHFORMULA hasQNominals kVars baseLid) $ map emptyAnno fs 
   return $ (hf { item = GTypes.Disjunction (map (item.fst) afs') r}, 
             hf { item = GTypes.Disjunction (map (item.snd) afs') r})
 GTypes.Implication f1 f2 r -> do
   f1' <- anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f1
   f2' <- anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f2
   return $ (hf {item = GTypes.Implication (item $ fst f1') (item $ fst f2') r}, 
             hf {item = GTypes.Implication (item $ snd f1') (item $ snd f2') r})
 GTypes.Equivalence f1 f2 r -> do
   f1' <- anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f1
   f2' <- anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f2
   return $ (hf {item = GTypes.Equivalence (item $ fst f1') (item $ fst f2') r}, 
             hf {item = GTypes.Equivalence (item $ snd f1') (item $ snd f2') r})
 GTypes.Nominal _s _b i _r -> do
  hth <- CState.get --TODO: check that if b holds, i must be a variable?
  if ( Set.member (simpleIdToId i) (GTypes.noms $ hSign hth) ) || 
      ( (GTypes.ASymbol $ GTypes.HSymb (simpleIdToId i) GTypes.Nom) `elem` (hVars hth))
           then return (hf, hf)
           else do 
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared nominal" i) : (anaDiags hth)}
    return (hf,hf)
 GTypes.AtState i f r -> do
   hth <- CState.get
   if ( Set.member (simpleIdToId i) (GTypes.noms $ hSign hth) ) || 
      ( (GTypes.ASymbol $ GTypes.HSymb (simpleIdToId i) GTypes.Nom) `elem` (hVars hth))
           then do
    f' <- anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f 
    return $ (hf { item = GTypes.AtState i (item $ fst f') r}, 
              hf { item = GTypes.AtState i (item $ snd f') r})
           else do 
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared nominal" i) : (anaDiags hth)}
    return (hf,hf)
 GTypes.BoxFormula i f r -> do 
  hth <- CState.get
  if (simpleIdToId i) `elem` (Map.keys $ GTypes.mods $ hSign hth)
           then do
   f' <- anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f
   return $ (hf { item = GTypes.BoxFormula i (item $ fst f') r}, 
             hf { item = GTypes.BoxFormula i (item $ snd f') r})
  else do
   CState.put $ hth {anaDiags = (mkDiag Error "undeclared modality" i) : (anaDiags hth)}
   return (hf,hf)
 GTypes.DiamondFormula i f r -> do 
  hth <- CState.get
  if (simpleIdToId i) `elem` (Map.keys $ GTypes.mods $ hSign hth)
           then do
   f' <- anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f
   return $ (hf { item = GTypes.DiamondFormula i (item $ fst f') r}, 
             hf { item = GTypes.DiamondFormula i (item $ snd f') r})  
  else do
   CState.put $ hth {anaDiags = (mkDiag Error "undeclared modality" i) : (anaDiags hth)}
   return (hf,hf)
 GTypes.QuantVarsParse q vs f r -> do 
   hth <- CState.get
   if null kVars then do
     CState.put $ hth {anaDiags = (mkDiag Error "quantification on base symbols not allowed:" (show hf)): (anaDiags hth)}
     return (hf, hf)
   else do
    let Result dsyms mrsyms = stat_symb_items baseLid (GTypes.baseSig $ hSign hth) vs -- the variables don't appear in hSign hth, that's why we get Nothing!
    case mrsyms of
     Nothing -> do
       CState.put $ hth {anaDiags = dsyms ++ anaDiags hth}
       return (hf, hf)
     Just rsyms -> -- trace ("rsyms:" ++ concatMap (\x -> show x ++ " ~ ") rsyms) $ 
                   do
      let msyms = convertRawSyms baseLid rsyms -- TODO: this should be a Result, not a Maybe, so we know which symbols failed
      case msyms of
       Nothing -> do
        CState.put $ hth {anaDiags = (mkDiag Error "could not convert all raw symbols to symbols" (show rsyms)) : anaDiags hth}
        return (hf, hf)
       Just syms -> do
        let symsKinds = filter (\x -> not (x `elem` kVars)) $ map (extSymKind baseLid) syms
        case symsKinds of 
         [] -> do  
           let (f', _) = CState.runState (anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f) $ 
                         hth {hVars = hVars hth ++ map GTypes.BaseRawSymbol rsyms }
           trace ("f' : " ++ show f' ) $ 
            return $ (hf{item = GTypes.QuantVars q rsyms (item $ fst f') r}, 
                    hf{item = GTypes.QuantVars q rsyms (item $ snd f') r})
         _ -> do -- TODO: better error message!
           let diagKinds = map (\k -> mkDiag Error ("quantification not allowed on symbols of kind " ++ k) (show hf) ) symsKinds
           CState.put $ hth {anaDiags = diagKinds ++ (anaDiags hth)}
           return (hf, hf)
 GTypes.QuantVars _ _ _ _ -> error $ "Already analyzed sentence:" ++ show hf
 GTypes.QuantNominals q ns f r -> 
  if hasQNominals then do
   hth <- CState.get
   let (f',_) = CState.runState  (anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f) $ 
                 hth {hVars = hVars hth ++  
                              map (\i -> GTypes.ASymbol $ GTypes.HSymb (simpleIdToId i) GTypes.Nom) ns}
   return $ (hf { item = GTypes.QuantNominals q ns (item $ fst f') r}, 
             hf { item = GTypes.QuantNominals q ns (item $ snd f') r})
  else error "the logic does not allow quantification on nominals"

convertRawSyms :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
                => lid -> [raw_sym] -> Maybe [sym]
convertRawSyms baseLid rawSymList = -- trace ("rawSymList:" ++ show rawSymList) $ 
           let mSymList = map (raw_to_symbol baseLid) rawSymList
           in if Nothing `elem` mSymList then 
                  -- trace (show mSymList) $ 
                 Nothing 
               else -- trace "convertRawSyms2" $ 
                    Just $ map fromJust mSymList 

{-
isNominalSen :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
                => lid -> GTypes.HSign sig -> sen -> (Bool, Maybe Id)
isNominalSen lid hsig sen = trace ("sen in isNominalSen:" ++ show sen) $ 
 let
  -- first add the nominals, or they will not be in the base signature
  -- and symsOfSen will not return them as symbols!
  Result ds mbsig = add_noms_to_sign lid (GTypes.baseSig hsig) $ GTypes.noms hsig
 in 
  case mbsig of 
   Nothing -> error $ show ds
   Just bsig -> let
     sSyms = -- symsOfHSen lid hsig (GTypes.Base_formula sen nullRange)  
             trace ("bsig:" ++ show bsig) $ symsOfSen lid bsig sen
    in trace ("sSyms:" ++ show sSyms) $ 
       case sSyms of
        [x] -> let i = sym_name lid x
                     -- hSymName lid x
             in (i `elem` (GTypes.noms hsig), Just i)
        _ -> (False, Nothing)
-}

-- translate constraints to CASL sentences
-- for some this can be done independent of the underlying logic
-- for others, this requires logic-dependent analysis

constrToSens :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
             => lid -> GTypes.HSign sig -> SemanticConstraint -> Result ([Named CBasic.CASLFORMULA])
constrToSens lid hsign c = trace ("c:"++ show c) $ 
 let binMods = map fst $
               filter (\(_, y) -> y == 2) $ 
               Map.toList $ GTypes.mods hsign
     st = genName "ST"
 in case c of 
     ReflexiveMod -> -- forall w : st . m(w,w)
      return $
      map (\m -> makeNamed ("ga_reflexive_" ++ show m) $ 
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w") st] $ 
                  CBasic.mkPredication 
                    (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w") st nullRange, CBasic.Qual_var (genToken "w") st nullRange]
          ) 
       binMods
     SymmetricMod -> -- forall w1, w2 : st . m(w1,w2) => m(w2, w1)
       return $
       map (\m -> makeNamed ("ga_symmetric_" ++ show m) $ 
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st, 
                                  CBasic.mkVarDecl (genToken "w2") st] $
                  CBasic.mkImpl
                  (CBasic.mkPredication 
                    (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w2") st nullRange])
                  (CBasic.mkPredication 
                    (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w2") st nullRange, CBasic.Qual_var (genToken "w1") st nullRange])
          )
       binMods
     TransitiveMod -> -- forall w1, w2,w3 : st . m(w1,w2) /\ m(w2, w3) => m(w1, w3)
      return $
      map (\m -> makeNamed ("ga_transitive_" ++ show m) $ 
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st, 
                                  CBasic.mkVarDecl (genToken "w2") st,
                                  CBasic.mkVarDecl (genToken "w3") st] $
                  CBasic.mkImpl
                  (CBasic.conjunct 
                   [ CBasic.mkPredication 
                      (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w2") st nullRange],
                     CBasic.mkPredication 
                      (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w2") st nullRange, CBasic.Qual_var (genToken "w3") st nullRange]
                   ]
                  )
                  (CBasic.mkPredication 
                    (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w3") st nullRange])
          )
       binMods
     SerialMod -> -- forall w1 : st . exists w2 : st . m(w1, w2)
      return $
      map (\m -> makeNamed ("ga_serial_" ++ show m) $ 
                 CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st] $
                  CBasic.mkExist [CBasic.mkVarDecl (genToken "w2") st] $ 
                   CBasic.mkPredication 
                    (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w2") st nullRange]
          ) 
       binMods
     EuclideanMod -> -- forall w1, w2,w3 : st . m(w1,w2) /\ m(w1, w3) => m(w2, w3)
      return $
      map (\m -> makeNamed ("ga_Euclidean_" ++ show m) $ 
                 CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st, 
                                  CBasic.mkVarDecl (genToken "w2") st,
                                  CBasic.mkVarDecl (genToken "w3") st] $
                  CBasic.mkImpl
                  (CBasic.conjunct 
                   [ CBasic.mkPredication 
                      (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w2") st nullRange],
                     CBasic.mkPredication 
                      (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w3") st nullRange]
                   ]
                  )
                  (CBasic.mkPredication 
                    (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w2") st nullRange, CBasic.Qual_var (genToken "w3") st nullRange])
          )
       binMods
     FunctionalMod -> -- forall w1 : st . exists! w2 : st . m(w1, w2)
      return $
      map (\m -> makeNamed ("ga_functional_" ++ show m) $ 
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st] $
                  CBasic.Quantification
                   CBasic.Unique_existential 
                   [CBasic.mkVarDecl (genToken "w2") st]
                   (CBasic.mkPredication 
                    (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w2") st nullRange]
                   )
                   nullRange
          ) 
       binMods
     LinearMod -> -- forall w1, w2,w3 : st . m(w1,w2) /\ m(w1, w3) => (m(w2, w3) \/ m(w3, w2) \/ w3 = w2)
      return $
      map (\m -> makeNamed ("ga_linear_" ++ show m) $ 
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st, 
                                  CBasic.mkVarDecl (genToken "w2") st,
                                  CBasic.mkVarDecl (genToken "w3") st] $
                  CBasic.mkImpl
                  (CBasic.conjunct 
                   [ CBasic.mkPredication 
                      (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w2") st nullRange],
                     CBasic.mkPredication 
                      (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w3") st nullRange]
                   ]
                  )
                  (CBasic.disjunct
                    [CBasic.mkPredication 
                      (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w2") st nullRange, CBasic.Qual_var (genToken "w3") st nullRange],
                     CBasic.mkPredication 
                      (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w3") st nullRange, CBasic.Qual_var (genToken "w2") st nullRange],
                     CBasic.mkStEq (CBasic.mkVarTerm (genToken "w2") st) 
                                   (CBasic.mkVarTerm (genToken "w3") st)
                   ]
                  )
          )
       binMods
     TotalMod -> -- forall w1, w2 : st . m(w1,w2) \/ m(w2, w1)
      return $
      map (\m -> makeNamed ("ga_total_" ++ show m) $ 
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st, 
                                  CBasic.mkVarDecl (genToken "w2") st] $
                  CBasic.disjunct
                  [CBasic.mkPredication 
                    (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange, CBasic.Qual_var (genToken "w2") st nullRange],
                   CBasic.mkPredication 
                    (CBasic.mkQualPred m $ CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w2") st nullRange, CBasic.Qual_var (genToken "w1") st nullRange]
                  ]
          )
       binMods
     _ -> constr_to_sens lid (GTypes.baseSig hsign) c -- should be GTypes.baseSig hsign
  
 

