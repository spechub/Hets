{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, ExistentialQuantification, DeriveDataTypeable #-}
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

--TODO:
-- sort the methods coming from Static 
-- in Syntax - parse_symb_items, parse_symb_map_items, symb_items_name
-- in Sentences - simplify_sen
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

parseHBasicSpec :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      =>           Bool -- admits quantification on nominals 
                -> Bool -- admits quantification on symbols of base logic
                -> lid -- lid for base logic
                -> PrefixMap ->  AParser st (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
parseHBasicSpec hasQNominals kVars baseLid _ks =
  fmap GTypes.Basic_spec (annosParser (parseBasicItems hasQNominals kVars fparser symParser)) 
  <|> (oBraceT >> cBraceT >> return (GTypes.Basic_spec []))
   where 
    fparser = case parse_formula baseLid of
                Nothing -> error $ "no formula parser for logic " ++ show baseLid
                Just f -> f
    symParser = case parse_symb_items baseLid of
                  Nothing -> error $ "no symbol parser for logic " ++ show baseLid
                  Just f -> f
 

parseBasicItems :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> AParser st (GTypes.H_BASIC_ITEMS sen symb_items raw_sym) -- TODO: take into account ks
parseBasicItems hasQNominals kVars fparser symParser = 
     parseAxItems hasQNominals kVars fparser symParser -- if this is not first, the parser for basic items consumes more than it should
  <|>
  do (as, ps) <- keyThenList nomP simpleId
     return $ GTypes.Nom_decl $ GTypes.Nom_item as ps
  <|>
  do (as, ps) <- keyThenList modP simpleId
     _c <- colonT
     ni <- getNumber
     let i = read ni :: Int
     return $ GTypes.Mod_decl $ GTypes.Mod_item as i ps

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

parseAxItems :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> AParser st (GTypes.H_BASIC_ITEMS sen symb_items raw_sym)
parseAxItems hasQNominals kVars fparser symParser = do
       d <- dotT
       (fs, ds) <- (aFormula hasQNominals kVars fparser symParser) `separatedBy` dotT
       (_, an) <- optSemi
       let _ = catRange (d : ds)
           ns = init fs ++ [appendAnno (last fs) an]
       return $ GTypes.Axiom_items ns

-- | parser for annoted formulae
aFormula :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> AParser st (Annoted (GTypes.HFORMULA sen symb_items raw_sym))
aFormula hasQNominals kVars fparser symParser = allAnnoParser (topformula hasQNominals kVars fparser symParser)

-- | toplevel formula parser
topformula :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
topformula hasQNominals kVars fparser symParser = (andOrFormula hasQNominals kVars fparser symParser) >>= (optImplForm hasQNominals kVars fparser symParser)

andOrFormula :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
andOrFormula hasQNominals kVars fparser symParser = (hFormula hasQNominals kVars fparser symParser) >>= (optAndOr hasQNominals kVars fparser symParser)

optImplForm :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> GTypes.HFORMULA sen symb_items raw_sym -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
optImplForm hasQNominals kVars fparser symParser f = do
      _c <- CFormula.implKey
      (fs, _ps) <- (andOrFormula hasQNominals kVars fparser symParser) `separatedBy` CFormula.implKey --TODO: range?
      return $ makeImpl (f : fs)
    <|> do
      c <- asKey equivS
      g <- andOrFormula hasQNominals kVars fparser symParser
      return $ GTypes.Equivalence f g $ tokPos c
    <|> return f

makeImpl :: [GTypes.HFORMULA sen symb_items raw_sym] -> GTypes.HFORMULA sen symb_items raw_sym
makeImpl l = 
 case l of 
  [f1, f2] -> GTypes.Implication f1 f2 nullRange
  f1 : fs  -> GTypes.Implication f1 (makeImpl fs) nullRange
  _ -> error "Illegal argument for makeImpl in parsing of hybrid formulas"


optAndOr :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> GTypes.HFORMULA sen symb_items raw_sym -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
optAndOr hasQNominals kVars fparser symParser f = do
      c <- CFormula.andKey
      (fs, ps) <- (hFormula hasQNominals kVars fparser symParser) `separatedBy` CFormula.andKey
      return $ GTypes.Conjunction (f : fs) $ catRange $ c : ps
    <|> do
      c <- CFormula.orKey
      (fs, ps) <- (hFormula hasQNominals kVars fparser symParser) `separatedBy` CFormula.orKey
      return $ GTypes.Disjunction (f : fs) $ catRange $ c : ps
    <|> return f

hFormula :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
hFormula hasQNominals kVars fparser symParser = 
   do 
      c <- atKey
      n <- simpleId
      _ <- colonT
      f <- topformula hasQNominals kVars fparser symParser -- here should be formula without @?
      return $ GTypes.AtState n f $ tokPos c
 <|> 
   do
    c <- asKey notS <|> asKey negS <?> "\"not\""
    f <- hFormula hasQNominals kVars fparser symParser --topformula
    return $ GTypes.Negation f $ tokPos c
   <|>
     do
        c1 <- asKey lessS
        md <- propId [greaterS]
        c2 <- asKey greaterS
        f <- topformula hasQNominals kVars fparser symParser
        return $ GTypes.DiamondFormula md f $ toRange c1 [] c2
 <|>
     do
        c1 <- oBracketT
        md <- propId ["]"]
        c2 <- cBracketT
        f <- topformula hasQNominals kVars fparser symParser
        return $ GTypes.BoxFormula md f $ toRange c1 [] c2
 <|> 
     parenFormula hasQNominals kVars fparser symParser
 <|>
     do
       (q, p) <- quant
       parseQFormula hasQNominals kVars fparser symParser (q, p)
 <|>
     do 
        f <- fparser 
        return $ GTypes.Base_formula f nullRange    
        -- this should also catch nominals as terms. 
        -- We have to make sure during static analysis that this is reverted!

parenFormula :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
parenFormula hasQNominals kVars fparser symParser = do
       oParenT << addAnnos
       f <- topformula hasQNominals kVars fparser symParser << addAnnos
       cParenT >> return f

quant :: AParser st (GTypes.HQUANT, Token)
quant = choice (map (\ (q, s) -> do
    t <- asKey s
    return (q, t))
  [ (GTypes.HExistential, hExistsS)
  , (GTypes.HUniversal, hForallS) ])
  <?> "quantifier" 

parseQFormula :: Bool -> Bool -> AParser st sen -> AParser st symb_items -> (GTypes.HQUANT, Token) -> AParser st (GTypes.HFORMULA sen symb_items raw_sym)
parseQFormula hasQNominals kVars fparser symParser (q, p) = 
  do -- first try quantification on nominals, or the parser will complain 
     (vs, _ps) <- keyThenList nomP simpleId
     _d <- dotT -- TODO: range
     f <- topformula hasQNominals kVars fparser symParser
     if hasQNominals then 
      return $ GTypes.QuantNominals q vs f nullRange
     else error $ "the logic does not admit quantification on nominals"
    <|> 
  do  
     (sitems, ps) <- symParser `separatedBy` commaT
     d <- dotT
     f <- topformula hasQNominals kVars fparser symParser
     if kVars then 
      return $ GTypes.QuantVarsParse q sitems f $ toRange p ps d
     else error $ "the logic does not admit quantification on base symbols"

-- | Any word to token
propId :: [String] -> GenParser Char st Token
propId k = pToken $ reserved (k ++ hybrid_keywords) scanAnyWords

-- | Parser for at 
atKey :: AParser st Token
atKey = asKey asP


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
  GTypes.Nominal b n _ -> 
     if b then return hsen
     else let n0 = simpleIdToId n
              n' = Map.findWithDefault n0 n0 $ GTypes.nomMap hmor
          in return $ GTypes.Nominal b (idToSimpleId n') nullRange
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
   GTypes.Nominal b n _ -> if b then [] else [GTypes.HSymb (simpleIdToId n) GTypes.Nom] -- TODO: ok to have empty list of syms for variables?
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
         (GTypes.H_BASIC_SPEC sen symb_items raw_sym, GTypes.HSign sig, GlobalAnnos) ->
         Result (GTypes.H_BASIC_SPEC sen symb_items raw_sym, ExtSign (GTypes.HSign sig) (GTypes.HSymbol sym), [Named (GTypes.HFORMULA sen symb_items raw_sym)])
basicHAnalysis hasQNominals kVars baseLid (bs, inSig, ga) = let
  hth = HTheoryAna inSig Set.empty [] [] ga []
  (newBs, accTh) = CState.runState (anaBasicHSpec hasQNominals kVars baseLid bs) hth
  ds = reverse $ anaDiags accTh
  outSig = hSign accTh
  sents = hSens accTh
 in Result ds $ Just (newBs, ExtSign outSig $ declSyms accTh, sents)

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
    let (hth', annofs') = foldl (\(h, l) f -> let (f', h') = CState.runState 
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
   let (isNom, mNomName) = isNominalSen baseLid (hSign hth) bsen
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
         Just (f1, f2) ->
           let hf1 = hf {item = GTypes.Base_formula f1 r}
               hf2 = hf {item = GTypes.Base_formula f2 r}
           in return (hf1, hf2) 
    else case mNomName of
          Nothing -> error "Can't have nominal formula without nominal name" -- should never happen!
          Just i -> 
            let iNom = GTypes.ASymbol $ GTypes.HSymb i GTypes.Nom
            in if iNom `elem` hVars hth then 
                  let hf' = hf { item = GTypes.Nominal True (idToSimpleId i) nullRange }
                  in return (hf', hf')
                 else if i `elem` (GTypes.noms $ hSign hth) then 
                         let hf' = hf { item = GTypes.Nominal False (idToSimpleId i) nullRange }
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
 GTypes.Nominal _b i _r -> do
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
    let Result dsyms mrsyms = stat_symb_items baseLid (GTypes.baseSig $ hSign hth) vs
    case mrsyms of
     Nothing -> do
       CState.put $ hth {anaDiags = dsyms ++ anaDiags hth}
       return (hf, hf)
     Just rsyms -> do
      let msyms = convertRawSyms baseLid rsyms -- TODO: this should be a Result, not a Maybe, so we know which symbols failed
      case msyms of 
       Nothing -> do
        CState.put $ hth {anaDiags = (mkDiag Error "could not convert all raw symbols to symbols" (show rsyms)) : anaDiags hth}
        return (hf, hf)
       Just syms -> do
        let symsKinds = filter (\x -> not (x `elem` kVars)) $ map (symKind baseLid) syms
        case symsKinds of 
         [] -> do  
           let (f', _) = CState.runState (anaHFORMULA hasQNominals kVars baseLid $ emptyAnno f) $ 
                         hth {hVars = hVars hth ++ map GTypes.BaseRawSymbol rsyms }
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
convertRawSyms baseLid rawSymList = 
           let mSymList = map (raw_to_symbol baseLid) rawSymList
           in if Nothing `elem` mSymList then Nothing else Just $ map fromJust mSymList 

isNominalSen :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
                => lid -> GTypes.HSign sig -> sen -> (Bool, Maybe Id)
isNominalSen lid hsig sen =
 let
  sSyms = symsOfSen lid (GTypes.baseSig hsig) sen
 in case sSyms of
      [x] -> let i = sym_name lid x
             in (i `elem` (GTypes.noms hsig), Just i)
      _ -> (False, Nothing)
{-

basicHAnalysis ::  Bool -> -- flag: has quantification on nominals? 
                   Bool -> -- flag: has quantification on base symbols?
                  ((basic_spec, sig, sen) -> Result sen) 
                  -> (GTypes.H_BASIC_SPEC sen symb_items raw_sym, GTypes.HSign sig, GlobalAnnos)
                  -> Result (GTypes.H_BASIC_SPEC sen symb_items raw_sym, ExtSign (GTypes.HSign sig) (GTypes.HSymbol sym), [Named (GTypes.HFORMULA sen symb_items raw_sym)])
basicHAnalysis hasQNominals kVars basicAnalysisSenBase (bs, inSig, ga) =
 let 
    hth = HTheoryAna inSig Set.empty [] Map.empty ga []
    (newBs, accTh) = CState.runState (anaBasicHSpec hasQNominals kVars basicAnalysisSenBase bs) hth
    ds = reverse $ anaDiags accTh
    outSig = hSign accTh
    sents = hSens accTh
 in Result ds $ Just (newBs, ExtSign outSig $ declSyms accTh, sents)

anaBasicHSpec :: Bool -> Bool ->
              ((basic_spec, sig, sen) -> Result sen)
              -> GTypes.H_BASIC_SPEC sen symb_items raw_sym -> CState.State (HTheoryAna sig sen symb_items raw_sym sym) (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
anaBasicHSpec hasQNominals kVars basicAnalysisSenBase (GTypes.Basic_spec al)= fmap GTypes.Basic_spec $
      mapAnM (anaBasicHItems hasQNominals kVars basicAnalysisSenBase) al

anaBasicHItems :: Bool -> Bool -> 
              ((basic_spec, sig, sen) -> Result sen)
              -> GTypes.H_BASIC_ITEMS sen symb_items raw_sym
              -> CState.State (HTheoryAna sig sen symb_items raw_sym sym) (GTypes.H_BASIC_ITEMS sen symb_items raw_sym) 
anaBasicHItems hasQNominals kVars basicAnalysisSenBase bi =
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
    let (hth', annofs') = foldl (\(h, l) f -> let (f', h') = CState.runState 
                                                              (anaHFORMULA hasQNominals kVars
                                                               basicAnalysisSenBase f) h
                                              in (h', f':l)) (hth, []) annofs 
    let replfs = reverse annofs'
        nfs = map (makeNamedSen.snd) replfs
    CState.put $ hth' {hSens = nfs ++ hSens hth'}
    return $ GTypes.Axiom_items $ map fst replfs

anaHFORMULA :: Bool -> Bool -> 
              ((basic_spec, sig, sen) -> Result sen)
              -> 
               Annoted (GTypes.HFORMULA sen symb_items raw_sym) -> 
               CState.State (HTheoryAna sig sen symb_items raw_sym sym) 
                            (Annoted (GTypes.HFORMULA sen symb_items raw_sym), 
                             Annoted (GTypes.HFORMULA sen symb_items raw_sym))
anaHFORMULA hasQNominals kVars basicAnalysisSenBase hf = case item hf of
 GTypes.Base_formula _bsen _r -> error "nyi" {- case bsen of
  Mixfix_formula (Mixfix_token i) -> do
   hth <- get
   let (d, hf') = if i `elem` (Map.keys $ hVars hth) then 
                          (Nothing, hf { item = HBasic.Nominal True i r})
                   else if Set.member (simpleIdToId i) (HSign.noms $ hSign hth)
                         then (Nothing, hf { item = HBasic.Nominal False i r})
                         else (Just $ mkDiag Error "undeclared nominal" i, hf)                                    
             -- here we check whether the nominal is a variable or not!
   case d of 
    Nothing -> return (hf', hf')
    Just x -> do 
      put $ hth {anaDiags = x : (anaDiags hth) }
      return (hf, hf)            
  f -> do
   hth <- get
   let bsig = HSign.baseSig $ hSign hth
       Result ds1 msig = CSign.addSymbToSign (RSign.caslSign bsig) $
                           CSign.Symbol (genName "ST") CSign.SortAsItemType
   case msig of 
        Nothing -> do 
                    put $ hth {anaDiags = ds1 ++ anaDiags hth} 
                    return (hf, hf)
        Just bsig0 -> do
         let allIds = CAna.getAllIds (Basic_spec []) emptyMix bsig0
             mix = emptyMix { mixRules = makeRules (CSign.globAnnos bsig0) allIds }
             Result ds3 mf = CAna.anaForm (const return) mix 
                                    bsig0{CSign.varMap = Map.union (CSign.varMap bsig0) $ 
                                                          hVars hth}
                                    f
         case mf of 
          Nothing -> do 
           put $ hth {anaDiags = ds3 ++ anaDiags hth}
           return (hf, hf)
          Just (f1, f2) -> let hf1 = hf {item = HBasic.Base_formula f1 r}
                               hf2 = hf {item = HBasic.Base_formula f2 r}
                           in return (hf1, hf2) -} 

 {-
   IDEA: 
  
   add a method 
   
    isNominal :: lid -> sig -> sen -> Bool

   that returns true if the formula is a nominal

   or  a formula is a nominal if it has only one symbol whose name is in the list of names of all nominals. 
  
 
   GENERIC CODE FOR FORMULAS:
   
  do
 hth <- CState.get
 Result ds mf = basicAnalysisSenBase 
                 (emptyBasicSpec, -- don't have it
                  GTypes.baseSig $ hSign hth, -- but the variables will be missing!
                  bsen)
 case mf of
  Nothing -> do
    CState.put $ hth {anaDiags = ds ++ anaDiags hth}
    return (hf, hf)
  Just (f1, f2) -> -- BUT: sen_analysis only gives a formula not both! It seems that it could give both!
                   let hf1 = hf {item = GTypes.Base_formula f1 r}
                       hf2 = hf {item = GTypes.Base_formula f2 r}
                   in return (hf1, hf2) 

  -}

 GTypes.Negation f r -> do
   (af1, af2) <- anaHFORMULA hasQNominals kVars basicAnalysisSenBase $ emptyAnno f
   let hf'= hf { item = GTypes.Negation (item af2) r}
   return (hf{item = GTypes.Negation (item af1) r}, hf')
 GTypes.Conjunction fs r -> do 
   afs' <- mapM (anaHFORMULA hasQNominals kVars basicAnalysisSenBase) $ map emptyAnno fs 
   return $ (hf { item = GTypes.Conjunction (map (item.fst) afs') r}, 
             hf { item = GTypes.Conjunction (map (item.snd) afs') r})
 GTypes.Disjunction fs r -> do 
   afs' <- mapM (anaHFORMULA hasQNominals kVars basicAnalysisSenBase) $ map emptyAnno fs 
   return $ (hf { item = GTypes.Disjunction (map (item.fst) afs') r}, 
             hf { item = GTypes.Disjunction (map (item.snd) afs') r})
 GTypes.Implication f1 f2 r -> do
   f1' <- anaHFORMULA hasQNominals kVars basicAnalysisSenBase $ emptyAnno f1
   f2' <- anaHFORMULA hasQNominals kVars basicAnalysisSenBase $ emptyAnno f2
   return $ (hf {item = GTypes.Implication (item $ fst f1') (item $ fst f2') r}, 
             hf {item = GTypes.Implication (item $ snd f1') (item $ snd f2') r}) 
 GTypes.Equivalence f1 f2 r -> do
   f1' <- anaHFORMULA hasQNominals kVars basicAnalysisSenBase $ emptyAnno f1
   f2' <- anaHFORMULA hasQNominals kVars basicAnalysisSenBase $ emptyAnno f2
   return $ (hf {item = GTypes.Equivalence (item $ fst f1') (item $ fst f2') r}, 
             hf {item = GTypes.Equivalence (item $ snd f1') (item $ snd f2') r})
 GTypes.Nominal _b i _r -> do
  hth <- CState.get
  if ( Set.member (simpleIdToId i) (GTypes.noms $ hSign hth) ) || 
      ( (i, genName "ST") `elem` (Map.toList $ hVars hth))
           then return (hf, hf)
           else do 
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared nominal" i) : (anaDiags hth)}
    return (hf,hf)
 GTypes.AtState i f r -> do
   hth <- CState.get
   if ( Set.member (simpleIdToId i) (GTypes.noms $ hSign hth) ) || 
      ( (i, genName "ST") `elem` (Map.toList $ hVars hth))
           then do
    f' <- anaHFORMULA hasQNominals kVars basicAnalysisSenBase $ emptyAnno f 
    return $ (hf { item = GTypes.AtState i (item $ fst f') r}, 
              hf { item = GTypes.AtState i (item $ snd f') r})
           else do 
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared nominal" i) : (anaDiags hth)}
    return (hf,hf)
 GTypes.BoxFormula i f r -> do 
  hth <- CState.get
  if (simpleIdToId i) `elem` (Map.keys $ GTypes.mods $ hSign hth)
           then do
   f' <- anaHFORMULA hasQNominals kVars basicAnalysisSenBase $ emptyAnno f
   return $ (hf { item = GTypes.BoxFormula i (item $ fst f') r}, 
             hf { item = GTypes.BoxFormula i (item $ snd f') r})
  else do
   CState.put $ hth {anaDiags = (mkDiag Error "undeclared modality" i) : (anaDiags hth)}
   return (hf,hf)
 GTypes.DiamondFormula i f r -> do 
  hth <- CState.get
  if (simpleIdToId i) `elem` (Map.keys $ GTypes.mods $ hSign hth)
           then do
   f' <- anaHFORMULA hasQNominals kVars basicAnalysisSenBase $ emptyAnno f
   return $ (hf { item = GTypes.DiamondFormula i (item $ fst f') r}, 
             hf { item = GTypes.DiamondFormula i (item $ snd f') r})  
  else do
   CState.put $ hth {anaDiags = (mkDiag Error "undeclared modality" i) : (anaDiags hth)}
   return (hf,hf)
 GTypes.QuantVarsParse q vs f r -> do 
   hth <- CState.get
   let Result dsyms mrsyms = basicAnaRawSym (GTypes.baseSig $ hSign hth) vs
   case mrsyms of
    Nothing -> do
      CState.put $ hth {anaDiags = dsyms : anaDiags hth}
      return (hf, hf)
    Just rsyms -> do
     let Result dconv msyms = convertRawSyms rsyms
     case msyms of 
      Nothing -> do
       CState.put $ hth {anaDiags = dconv : anaDiags hth}
       return (hf, hf)
      Just syms -> do
       -- TODO: check that the kinds of all symbols appearing in syms are allowed!
       let (f', _) = CState.runState (anaHFORMULA basicAnalysisSenBase basicAnaRawSym $ emptyAnno f) $ 
                     hth {hVars = hVars hth ++ map GTypes.ASymbol syms }
       return $ (hf{item = GTypes.QuantVars q rsyms (item $ fst f') r}, 
                 hf{item = GTypes.QuantVars q rsyms (item $ snd f') r})
 GTypes.QuantVars _ _ _ _ -> error $ "Already analyzed sentence" -- ++ show hf
 GTypes.QuantNominals q ns f r -> 
  if hasQNominals then do
   hth <- CState.get
   let (f',_) = CState.runState  (anaHFORMULA hasQNominals kVars basicAnalysisSenBase $ emptyAnno f) $ 
                 hth {hVars = Map.union (hVars hth) $ 
                              Map.fromList $ map (\i -> (i, genName "ST") ) ns}
   return $ (hf { item = GTypes.QuantNominals q ns (item $ fst f') r}, 
             hf { item = GTypes.QuantNominals q ns (item $ snd f') r})
  else error "the logic does not allow quantification on nominals"

isNominalSen :: (sig -> sen -> [sym]) ->
                (sym -> Id) ->
                GTypes.HSign sig -> sen -> Bool
isNominalSen senSyms sName hsig sen = 
 let
  sSyms = senSyms (GTypes.baseSig hsig) sen
 in case sSyms of
      [x] -> (sName x) `elem` (GTypes.noms hsig)
      _ -> False

{- 

basic_analysis :: lid
           -> Maybe ((basic_spec, sign, GlobalAnnos)
             -> Result (basic_spec, ExtSign sign symbol, [Named sentence]))
sen_analysis :: lid
           -> Maybe ((basic_spec, sign, sentence) -> Result sentence)
stat_symb_map_items :: lid -> sign -> Maybe sign -> [symb_map_items]
             -> Result (EndoMap raw_symbol)
stat_symb_items :: lid -> sign -> [symb_items] -> Result [raw_symbol]

the other methods will be implemented later
-}

-}


