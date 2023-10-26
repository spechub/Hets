{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
    TypeSynonymInstances, FlexibleInstances, FlexibleContexts,
    ExistentialQuantification, DeriveDataTypeable #-}
{- |
Module      :  ./GenHyb/GenMethods
Copyright   :  (c) R. Diaconescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Generic methods for the Loigc class and its subclasses.
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

--TODO:
-- sort the methods coming from Static
-- in Static
-- final_union, TODO: where is this needed at all?
-- morphism_union, TODO: can wait
-- TODO: we need is_nominal_sen, DONE
-- convertTheory, DONE
-- convertRawSyms, TODO:  check that it does what it should
-- extSymKind TODO: need to distinguish base and top nominals and modalities?

-- for class Category

idMor :: (Category sig mor) =>
       GTypes.HSign sig -> GTypes.HMorphism sig mor
idMor hsig = GTypes.HMorphism hsig hsig
               (ide $ GTypes.baseSig hsig) Map.empty Map.empty

isHIncl :: (Category sig mor) =>
           GTypes.HMorphism sig mor -> Bool
isHIncl hmor = isInclusion (GTypes.baseMor hmor) &&
               Map.null (GTypes.nomMap hmor) &&
               Map.null (GTypes.modMap hmor)

compHMor :: (Category sig mor) =>
            GTypes.HMorphism sig mor -> GTypes.HMorphism sig mor ->
            Result (GTypes.HMorphism sig mor)
compHMor mor1 mor2 =
 if GTypes.target mor1 == GTypes.source mor2 then do
  bmor <- composeMorphisms (GTypes.baseMor mor1) (GTypes.baseMor mor2)
  return $ GTypes.HMorphism (GTypes.source mor1) (GTypes.target mor2)
                            bmor
                            (composeMap
                              (Map.fromSet id $ GTypes.noms $
                                           GTypes.source mor1)
                              (GTypes.nomMap mor1)
                              (GTypes.nomMap mor2))
                            (composeMap
                              (GTypes.mods $ GTypes.source mor1)
                              (GTypes.modMap mor1)
                              (GTypes.modMap mor2))
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

parseSymbItems :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => lid -> Maybe (PrefixMap -> AParser st (GTypes.H_SYMB_ITEMS sym symb_items))
parseSymbItems baseLid = Just $ \pm -> do
      _ <- nomP False -- TODO: add a flag for the two notations!!!
      _s <- optQual
      aNom <- simpleId
      return $ GTypes.HSymbItems GTypes.NomKind
                [GTypes.HSymb (simpleIdToId aNom) GTypes.Nom] nullRange
    <|> do
     _ <- modP False -- TODO: add a flag for the two notations!!!
     _s <- optQual
     aMod <- simpleId
     return $ GTypes.HSymbItems GTypes.ModKind
                [GTypes.HSymb (simpleIdToId aMod) $ GTypes.Mod 2] nullRange
     -- Note: only binary modalitiesies for now
    <|> do
      let bParser = case parse_symb_items baseLid of
                     Just f -> f
                     Nothing -> error $
                                 "parser for symbol items not available"
                                 ++ " for base logic " ++ show baseLid
      x <- bParser pm
      return $ GTypes.BaseSymbItems x


parseSymbMapItems :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => lid -> Maybe (PrefixMap -> AParser st (GTypes.H_SYMB_MAP_ITEMS symb_map_items))
parseSymbMapItems baseLid = Just $ \pm -> do
      _ <- nomP False <|> modP False
      -- TODO: add a flag for the two notations!!!
      _s <- optQual
      anId <- simpleId
      do f <- pToken $ toKey mapsTo
         anId' <- simpleId
         return (GTypes.HSymbMapItems
                   [GTypes.HMapItem (simpleIdToId anId)
                                    (simpleIdToId anId') $ tokPos f]
                   nullRange)
        <|> return (GTypes.HSymbMapItems
                     [GTypes.HSymbItem $ simpleIdToId anId]
                     nullRange)
 <|> do
  let bParser = case parse_symb_map_items baseLid of
                     Just f -> f
                     Nothing ->
                       error $ "parser for symbol items not available"
                               ++ " for base logic " ++ show baseLid
  x <- bParser pm
  return $ GTypes.BaseSymbMapItems x


hSymbItemsName :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => lid -> GTypes.H_SYMB_ITEMS sym symb_items -> [String]
hSymbItemsName lid (GTypes.BaseSymbItems sitems) =
  symb_items_name lid sitems
hSymbItemsName lid (GTypes.HSymbItems _ hs _) =
  map (show . (hSymName lid)) hs

parseHBasicSpec :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      =>           Bool -- True for eng. notation, False for math. notation
                -> Bool -- admits quantification on nominals
                -> Bool -- admits quantification on symbols of base logic
                -> lid -- lid for base logic
                -> PrefixMap
                -> AParser st (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
parseHBasicSpec eng hasQNominals kVars baseLid pm =
  fmap GTypes.Basic_spec
       (annosParser (parseBasicItems eng hasQNominals kVars baseLid pm))
  <|> (oBraceT >> cBraceT >> return (GTypes.Basic_spec []))

parseBasicItems :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> Bool -> lid -> PrefixMap -> 
         AParser st (GTypes.H_BASIC_ITEMS sen symb_items raw_sym)
         -- TODO: take into account ks
parseBasicItems eng hasQNominals kVars baseLid pm =
     parseAxItems eng hasQNominals kVars baseLid pm
 -- if this is not first,
 -- the parser for basic items consumes more than it should
  <|>
  do (as, ps) <- keyThenList (nomP eng) simpleId
     return $ GTypes.Nom_decl $ GTypes.Nom_item as ps
  <|>
  do (as, ps) <- keyThenList (modP eng) simpleId
     _c <- colonT
     ni <- getNumber
     let i = read ni :: Int
     return $ GTypes.Mod_decl $ GTypes.Mod_item as i ps

modP :: Bool -> AParser st Token
modP eng =
  if eng
    then asKey "event" <|> asKey "events"
    else asKey modalityS <|> asKey modalitiesS

nomP :: Bool -> AParser st Token
nomP eng =
  if eng
   then asKey "state" <|> asKey "states"
   else asKey nominalS <|> asKey nominalsS

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
      => Bool -> Bool -> Bool -> lid -> PrefixMap -> 
         AParser st (GTypes.H_BASIC_ITEMS sen symb_items raw_sym)
parseAxItems eng hasQNominals kVars baseLid pm = do
       d <- dotT
       (fs, ds) <- (aFormula eng hasQNominals kVars baseLid pm)
                   `separatedBy` dotT
       (_, an) <- optSemi
       let _ = catRange (d : ds)
           ns = init fs ++ [appendAnno (last fs) an]
       return $ GTypes.Axiom_items ns

-- | parser for annoted formulae
aFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> Bool -> lid -> PrefixMap -> 
         AParser st (Annoted (GTypes.HFORMULA sen symb_items raw_sym))
aFormula eng hasQNominals kVars baseLid pm =
  allAnnoParser (topformula eng hasQNominals kVars baseLid pm)

-- | toplevel formula parser
topformula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> Bool -> lid -> PrefixMap -> 
         AParser st (GTypes.HFORMULA sen symb_items raw_sym)
topformula eng hasQNominals kVars baseLid pm =
  (andOrFormula eng hasQNominals kVars baseLid pm)
  >>= (optImplForm eng hasQNominals kVars baseLid pm)

andOrFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> Bool -> lid -> PrefixMap -> 
         AParser st (GTypes.HFORMULA sen symb_items raw_sym)
andOrFormula eng hasQNominals kVars baseLid pm =
 (hFormula eng hasQNominals kVars baseLid pm)
 >>= (optAndOr eng hasQNominals kVars baseLid pm)

optImplForm :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> Bool -> lid -> PrefixMap -> 
         GTypes.HFORMULA sen symb_items raw_sym -> 
         AParser st (GTypes.HFORMULA sen symb_items raw_sym)
optImplForm eng hasQNominals kVars baseLid pm f = do
      _c <- CFormula.implKey
      (fs, _ps) <- (andOrFormula eng hasQNominals kVars baseLid pm)
                   `separatedBy` CFormula.implKey
      return $ makeImpl (f : fs)
    <|> do
      c <- asKey equivS
      g <- andOrFormula eng hasQNominals kVars baseLid pm
      return $ GTypes.Equivalence f g $ tokPos c
    <|> return f

makeImpl :: [GTypes.HFORMULA sen symb_items raw_sym] ->
            GTypes.HFORMULA sen symb_items raw_sym
makeImpl l =
 case l of
  [f1, f2] -> GTypes.Implication f1 f2 nullRange
  f1 : fs  -> GTypes.Implication f1 (makeImpl fs) nullRange
  _ -> error "Illegal argument for makeImpl in parsing of hybrid formulas"


optAndOr :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> Bool -> lid -> PrefixMap -> 
         GTypes.HFORMULA sen symb_items raw_sym ->
         AParser st (GTypes.HFORMULA sen symb_items raw_sym)
optAndOr eng hasQNominals kVars baseLid pm f = do
      c <- CFormula.andKey
      (fs, ps) <- (hFormula eng hasQNominals kVars baseLid pm)
                  `separatedBy` CFormula.andKey
      return $ GTypes.Conjunction (f : fs) $ catRange $ c : ps
    <|> do
      c <- CFormula.orKey
      (fs, ps) <- (hFormula eng hasQNominals kVars baseLid pm)
                  `separatedBy` CFormula.orKey
      return $ GTypes.Disjunction (f : fs) $ catRange $ c : ps
    <|> return f

hFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> Bool -> lid -> PrefixMap -> 
         AParser st (GTypes.HFORMULA sen symb_items raw_sym)
hFormula eng hasQNominals kVars baseLid pm =
 if eng
 then
   do
      c <- asKey "At state"
      n <- simpleId
      s <- optQual
      _ <- colonT
      f <- topformula eng hasQNominals kVars baseLid pm
      -- here should be formula without @?
      return $ GTypes.AtState s n f $ tokPos c
 <|>
   do
    c <- asKey notS <|> asKey negS <?> "\"not\""
    f <- hFormula eng hasQNominals kVars baseLid pm --topformula
    return $ GTypes.Negation f $ tokPos c
   <|>
     do
        c1 <- asKey "Through" --lessS
        md <- propId ["sometimes", "always"]
        s <- optQual
        _ <- commaT
        sen <- do
                 c2 <- asKey "sometimes"
                 f <- topformula eng hasQNominals kVars baseLid pm
                 return $ GTypes.DiamondFormula s md f $ toRange c1 [] c2
               <|> do
                 c2 <- asKey "always"
                 f <- topformula eng hasQNominals kVars baseLid pm
                 return $ GTypes.BoxFormula s md f $ toRange c1 [] c2
        return sen
 <|>
     parenFormula eng hasQNominals kVars baseLid pm
 <|>
     do
       (q, p) <- quant
       parseQFormula baseLid eng hasQNominals kVars(q, p) pm
 <|>
     do
        let fparser = case parse_prim_formula baseLid of
                Nothing ->
                 error $ "no prim formula parser for logic " ++ show baseLid
                Just f -> f
        f <- fparser pm
        return $ GTypes.Base_formula f nullRange
        -- this should also catch nominals as terms.
        -- We have to make sure during static analysis that this is reverted!
 <|> do -- qualified symbols are nominals
       nom <- simpleId
       _ <- asKey "::"
       qual <- simpleId
       return $ GTypes.Nominal (show qual) False nom nullRange

 else
   do
      c <- asKey asP
      n <- simpleId
      s <- optQual
      _ <- colonT
      f <- topformula eng hasQNominals kVars baseLid pm
      return $ GTypes.AtState s n f $ tokPos c
 <|>
   do
    c <- asKey notS <|> asKey negS <?> "\"not\""
    f <- hFormula eng hasQNominals kVars baseLid pm
    return $ GTypes.Negation f $ tokPos c
   <|>
     do
        c1 <- asKey lessS
        md <- propId [greaterS]
        s <- optQual
        c2 <- asKey greaterS
        f <- topformula eng hasQNominals kVars baseLid pm
        return $ GTypes.DiamondFormula s md f $ toRange c1 [] c2
 <|>
     do
        c1 <- oBracketT
        md <- propId ["]"]
        s <- optQual
        c2 <- cBracketT
        f <- topformula eng hasQNominals kVars baseLid pm
        return $ GTypes.BoxFormula s md f $ toRange c1 [] c2
 <|>
     parenFormula eng hasQNominals kVars baseLid pm
 <|>
     do
       (q, p) <- quant
       parseQFormula baseLid eng hasQNominals kVars (q, p) pm
 <|>
     do
        let fparser = case parse_prim_formula baseLid of
                Nothing -> error $
                            "no prim formula parser for logic "
                            ++ show baseLid
                Just f -> f
        f <- fparser pm
        return $ GTypes.Base_formula f nullRange
        -- this should also catch nominals as terms.
        -- We have to make sure during static analysis that this is reverted!
 <|> do -- qualified symbols are nominals
       nom <- simpleId
       _ <- asKey "::"
       qual <- simpleId
       return $ GTypes.Nominal (show qual) False nom nullRange
   -- Note: always False here, no qualifications for variables

parenFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => Bool -> Bool -> Bool -> lid -> PrefixMap -> 
         AParser st (GTypes.HFORMULA sen symb_items raw_sym)
parenFormula eng hasQNominals kVars baseLid pm = do
       oParenT << addAnnos
       f <- topformula eng hasQNominals kVars baseLid pm << addAnnos
       cParenT >> return f

quant :: AParser st (GTypes.HQUANT, Token)
quant = choice (map (\ (q, s) -> do
    t <- asKey s
    str <- optQual
    return (q str, t))
  [ (GTypes.HExistential, hExistsS)
  , (GTypes.HUniversal,   hForallS) ])
  <?> "quantifier"

optQual :: AParser st String
optQual = do
     _ <- asKey "::"
     qual <- simpleId
     return $ show qual
     <|> do
     return ""

parseQFormula :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
      => lid -> Bool -> Bool -> Bool -> (GTypes.HQUANT, Token) -> PrefixMap ->
         AParser st (GTypes.HFORMULA sen symb_items raw_sym)
parseQFormula baseLid eng hasQNominals kVars (q, p) pm =
  do -- first try quantification on nominals, or the parser will complain
     (vs, _ps) <- keyThenList (nomP eng) simpleId
     _d <- dotT
     f <- topformula eng hasQNominals kVars baseLid pm
     if hasQNominals then
      return $ GTypes.QuantNominals q vs f nullRange
     else error $ "the logic does not admit quantification on nominals"
    <|>
  do
     let symParser = case parse_symb_items baseLid of
                  Nothing ->
                    error $ "no symbol parser for logic "
                            ++ show baseLid
                  Just f -> f
     (sitems, ps) <- (symParser pm) `separatedBy` commaT
     d <- dotT
     f <- topformula eng hasQNominals kVars baseLid pm
     if kVars then
      return $ GTypes.QuantVarsParse q sitems f $ toRange p ps d
     else error $ "the logic does not admit quantification on base symbols"

-- | Any word to token
propId :: [String] -> GenParser Char st Token
propId k = pToken $ reserved (k ++ hybrid_keywords) scanAnyWords

-- for class Sentences

mapSentence :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
            => lid ->
               GTypes.HMorphism sig mor ->
               GTypes.HFORMULA sen symb_items raw_sym ->
               Result (GTypes.HFORMULA sen symb_items raw_sym)
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
  GTypes.AtState s n hsen' _ -> do
    tsen' <- mapSentence baseLid hmor hsen'
    let n0 = simpleIdToId n
        n' = idToSimpleId $ Map.findWithDefault n0 n0 $ GTypes.nomMap hmor
    return $ GTypes.AtState s n' tsen' nullRange
  GTypes.BoxFormula s m hsen' _ -> do
    tsen' <- mapSentence baseLid hmor hsen'
    let m0 = simpleIdToId m
        m' = idToSimpleId $ Map.findWithDefault m0 m0 $ GTypes.modMap hmor
    return $ GTypes.BoxFormula s m' tsen' nullRange
  GTypes.DiamondFormula s m hsen' _ -> do
    tsen' <- mapSentence baseLid hmor hsen'
    let m0 = simpleIdToId m
        m' = idToSimpleId $ Map.findWithDefault m0 m0 $ GTypes.modMap hmor
    return $ GTypes.DiamondFormula s m' tsen' nullRange
  GTypes.QuantNominals hq noms hsen' _ -> do
    tsen' <- mapSentence baseLid hmor hsen'
    return $ GTypes.QuantNominals hq noms tsen' nullRange
  GTypes.QuantVarsParse _ _ _ _ ->
    error "cannot translate a sentence before it was analyzed"
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
     Nothing ->
      error $ "could not convert symbols in quantification"
              ++" when translating sentence"
     Just syms -> do
      let ssig = GTypes.source hmor
          tsig = GTypes.target hmor
      ssig' <- foldM (addSymbToHSign baseLid) ssig $
               map GTypes.BaseSymb syms
      hincl <- --trace ("ssig:" ++ show ssig ++ "ssig':" ++ show ssig') $
               subsigInclusion baseLid ssig ssig'
      let spanGr = Graph.mkGraph [(0, ssig), (1, ssig'), (2, tsig)]
                                 [(0, 1, (0, hincl)), (0, 2, (1, hmor))]
      (csig, cmors) <- signatureColimit baseLid spanGr
      let hmor'  = Map.findWithDefault (error "cmor  missing") 1 cmors
      dsig <- signatureDifference baseLid csig tsig
      let rsyms' = map (symbol_to_raw baseLid) $
       -- this is an ugly hack,
       -- cause signature colimits don't preserve inclusions
                       mostSymsOf baseLid $ GTypes.baseSig dsig
       -- only base symbols, so we don't lose anything here
      tsen' <- mapSentence baseLid hmor' hsen'
      let transSen = GTypes.QuantVars hq rsyms' tsen' nullRange
      return transSen

mostSymsOfDiff :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
    => lid -> GTypes.HSign sig -> [GTypes.HSymbol sym]
mostSymsOfDiff baseLid hsig = let
  bsyms = map GTypes.BaseSymb $
               mostSymsOf baseLid $ GTypes.baseSig hsig
  nsyms = map (\n -> GTypes.HSymb n GTypes.Nom) $
              Set.toList $ GTypes.noms hsig
  msyms = map (\(m,i) -> GTypes.HSymb m (GTypes.Mod i)) $
              Map.toList $ GTypes.mods hsig
 in bsyms ++ nsyms ++ msyms

signatureDifference :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
    => lid -> GTypes.HSign sig -> GTypes.HSign sig ->
       Result (GTypes.HSign sig)
signatureDifference baseLid hsig1 hsig2 = do
 bDiff <- signatureDiff baseLid (GTypes.baseSig hsig1) $
                                GTypes.baseSig hsig2
 return $
  GTypes.HSign bDiff
   (Set.difference (GTypes.noms hsig1) $ GTypes.noms hsig2)
   (Map.difference (GTypes.mods hsig1) $ GTypes.mods hsig2)

subsigInclusion :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
    => lid -> GTypes.HSign sig -> GTypes.HSign sig ->
       Result (GTypes.HMorphism sig mor)
subsigInclusion baseLid ssig ssig' = do
   bmor <- subsig_inclusion baseLid (GTypes.baseSig ssig) $
                                     GTypes.baseSig ssig'
   return $ GTypes.HMorphism ssig ssig' bmor Map.empty Map.empty

addSymbToHSign :: Logic lid sublogics basic_spec sen
                   symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
      => lid -> GTypes.HSign sig -> GTypes.HSymbol sym ->
         Result (GTypes.HSign sig)
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
     mgr = emap (\(i, m) -> (i, GTypes.modMap m)) $
           nmap (\ s -> Set.fromList $ Map.keys $ GTypes.mods s) hgr
     (modSet0, modFuns0) = computeColimitSet mgr
     (modSet, modFuns) = addIntToSymbols (modSet0, modFuns0)
     csig = GTypes.HSign cbsig nomSet $
             Map.fromList $ map (\m -> (m, 2)) $ Set.toList modSet
     cmors = Map.fromList $ map (\(n, hsig) ->
                                  (n, GTypes.HMorphism
                                       hsig csig
                                       (Map.findWithDefault
                                          (error "missing morphism")
                                          n cbmors)
                                       (Map.findWithDefault
                                         Map.empty n nomFuns)
                                       (Map.findWithDefault
                                         Map.empty n modFuns)
                                  )
                                )
             $ labNodes hgr
 return (csig, cmors)

hNegation :: GTypes.HFORMULA sen symb_items raw_sym ->
             Maybe (GTypes.HFORMULA sen symb_items raw_sym)
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
    [Set.fromList $ map (\(m,i) -> GTypes.HSymb m (GTypes.Mod i)) $
     Map.toList mSyms] ++
    map (\ss -> Set.map (\s -> GTypes.BaseSymb s) ss) bSyms

hSymMapOf :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          => lid -> GTypes.HMorphism sig mor -> EndoMap (GTypes.HSymbol sym)
hSymMapOf baseLid hmor =
 let mkBSymMap f = Map.mapKeys (\x -> GTypes.BaseSymb x) $
                               Map.map (\x -> GTypes.BaseSymb x) f
     bMap = mkBSymMap $ symmap_of baseLid $ GTypes.baseMor hmor
     nMap = Map.mapKeys (\x -> GTypes.HSymb x GTypes.Nom) $
             Map.map (\x -> GTypes.HSymb x GTypes.Nom) $ GTypes.nomMap hmor
     mMap = Map.mapKeys (\x ->
             let i = Map.findWithDefault
                         (error $ "unknown modality: " ++ show x)
                         x $ GTypes.mods $ GTypes.source hmor
             in GTypes.HSymb x (GTypes.Mod i)) $
            Map.map (\x ->
             let i = Map.findWithDefault
                         (error $ "unknown modality: " ++ show x)
                         x $ GTypes.mods $ GTypes.target hmor
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
          => lid -> GTypes.HSymbol sym -> String
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
              GTypes.HSign sig ->
              GTypes.HFORMULA sen symb_items raw_sym ->
              [GTypes.HSymbol sym]
symsOfHSen baseLid hsig hsen =
 case hsen of
   GTypes.Base_formula sen _ ->
    let bSyms = symsOfSen baseLid (GTypes.baseSig hsig) sen
    in map (\s -> GTypes.BaseSymb s) bSyms
   GTypes.Negation hsen' _ ->
     symsOfHSen baseLid hsig hsen'
   GTypes.Conjunction hsens _ ->
     nub $ concatMap (symsOfHSen baseLid hsig) hsens
   GTypes.Disjunction hsens _ ->
     nub $ concatMap (symsOfHSen baseLid hsig) hsens
   GTypes.Implication hsen1 hsen2 _ ->
     nub $ (symsOfHSen baseLid hsig hsen1) ++ (symsOfHSen baseLid hsig hsen2)
   GTypes.Equivalence hsen1 hsen2 _ ->
     nub $ (symsOfHSen baseLid hsig hsen1) ++ (symsOfHSen baseLid hsig hsen2)
   GTypes.Nominal _ b n _ ->
     if b then []
     else [GTypes.HSymb (simpleIdToId n) GTypes.Nom]
     -- TODO: ok to have empty list of syms for variables?
   GTypes.AtState _ n hsen' _ ->
     let syms = symsOfHSen baseLid hsig hsen'
     in (GTypes.HSymb (simpleIdToId n) GTypes.Nom):syms
   GTypes.BoxFormula _ m hsen' _ ->
     let syms = symsOfHSen baseLid hsig hsen'
         k = GTypes.Mod (2::Int)
     in (GTypes.HSymb (simpleIdToId m) k):syms
   GTypes.DiamondFormula _ m hsen' _ ->
      let syms = symsOfHSen baseLid hsig hsen'
          k = GTypes.Mod (2::Int)
      in (GTypes.HSymb (simpleIdToId m) k):syms
   GTypes.QuantNominals _hq _noms hsen' _ ->
      symsOfHSen baseLid hsig hsen' -- TODO:vars?
   GTypes.QuantVars _hq _vars hsen' _ ->
      symsOfHSen baseLid hsig hsen' -- TODO:vars?
   GTypes.QuantVarsParse _hq _vars _hsen' _ ->
      error $ "unparsed sentence"

rawToSymbol :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          =>
              lid -> GTypes.HRawSymbol sym raw_sym ->
              Maybe (GTypes.HSymbol sym)
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

sigIntersection :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          =>
              lid -> GTypes.HSign sig -> GTypes.HSign sig ->
              Result (GTypes.HSign sig)
sigIntersection baseLid hsig1 hsig2 = do
 bsig <- intersection baseLid (GTypes.baseSig hsig1) $
                               GTypes.baseSig hsig2
 let uNoms = Set.intersection (GTypes.noms hsig1) $
                               GTypes.noms hsig2
     uMods = Map.intersection (GTypes.mods hsig1) $
                               GTypes.mods hsig2
-- TODO: fail if a modality appears in both sigs with different arities?
 return $ GTypes.HSign bsig uNoms uMods

sigUnion :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          =>
              lid -> GTypes.HSign sig -> GTypes.HSign sig ->
              Result (GTypes.HSign sig)
sigUnion baseLid hsig1 hsig2 = do
 bsig <- signature_union baseLid (GTypes.baseSig hsig1) $
                                  GTypes.baseSig hsig2
 let uNoms = Set.union (GTypes.noms hsig1) $ GTypes.noms hsig2
     uMods = Map.union (GTypes.mods hsig1) $ GTypes.mods hsig2
-- TODO: fail if a modality appears in both sigs with different arities?
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

hGeneratedSign :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          =>
              lid -> Set.Set (GTypes.HSymbol sym) -> GTypes.HSign sig ->
              Result (GTypes.HMorphism sig mor)
hGeneratedSign baseLid kSyms hSig = do
 let hSyms = Set.unions $ hSymOf baseLid hSig
 if not $ Set.isSubsetOf kSyms hSyms then do
    let diff = kSyms Set.\\ hSyms
    error $ "Revealing: The following symbols "
                     ++ show diff ++ " are not in the signature"
  else do
   let (bSyms, nSyms, mSyms) =
         foldl (\(bs, ns, ms) s ->
                  case s of
                   GTypes.BaseSymb x ->
                    (Set.insert x bs, ns, ms)
                   GTypes.HSymb i GTypes.Nom ->
                    (bs, Set.insert i ns, ms)
                   GTypes.HSymb i (GTypes.Mod a) ->
                    (bs, ns, Set.insert (i, a) ms)
               ) (Set.empty, Set.empty, Set.empty) kSyms
   bIncl <- generated_sign baseLid bSyms $ GTypes.baseSig hSig
   let bSig = dom bIncl
       bhSig = GTypes.HSign bSig nSyms $ Map.fromList $ Set.toList mSyms
       iMor = GTypes.HMorphism bhSig hSig bIncl Map.empty Map.empty
   return iMor

hCoGeneratedSign :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          =>
              lid -> Set.Set (GTypes.HSymbol sym) -> GTypes.HSign sig ->
              Result (GTypes.HMorphism sig mor)
hCoGeneratedSign baseLid kSyms hSig = do
 let hSyms = Set.unions $ hSymOf baseLid hSig
 if not $ Set.isSubsetOf kSyms hSyms then do
    let diff = kSyms Set.\\ hSyms
    error $ "Hiding: The following symbols "
                     ++ show diff ++ " are not in the signature"
  else do
   let (bSyms, nSyms, mSyms) =
         foldl (\(bs, ns, ms) s ->
                  case s of
                   GTypes.BaseSymb x ->
                    (Set.insert x bs, ns, ms)
                   GTypes.HSymb i GTypes.Nom ->
                    (bs, Set.insert i ns, ms)
                   GTypes.HSymb i (GTypes.Mod a) ->
                    (bs, ns, Set.insert (i, a) ms)
               ) (Set.empty, Set.empty, Set.empty) kSyms
   bIncl <- generated_sign baseLid bSyms $ GTypes.baseSig hSig
   let bSig = dom bIncl
       bhSig = GTypes.HSign bSig ((GTypes.noms hSig) Set.\\ nSyms) $
               Map.difference (GTypes.mods hSig) $
               Map.fromList $ Set.toList mSyms
       iMor = GTypes.HMorphism bhSig hSig bIncl Map.empty Map.empty
   return iMor

hStatSymbItems :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                  mor sym raw_sym proof_tree
          =>
              lid -> GTypes.HSign sig ->
              [GTypes.H_SYMB_ITEMS sym symb_items] ->
              Result [GTypes.HRawSymbol sym raw_sym]
hStatSymbItems baseLid hsig sitems = do
 rsyms <- foldM (\rsl sitem ->
           case sitem of
             GTypes.BaseSymbItems bsitems -> do
               brSyms <- stat_symb_items baseLid
                           (GTypes.baseSig hsig) [bsitems]
               return $ rsl ++ map GTypes.BaseRawSymbol brSyms
             GTypes.HSymbItems _hk hsyms _ ->
               return $ rsl ++ map GTypes.ASymbol hsyms
               --TODO: would it be better to use AKindedSymb?
                )
   [] sitems
 return $ reverse rsyms

-- for StaticAnalysis

convertHTheory :: Logic lid sublogics basic_spec sen
                    symb_items symb_map_items sig
                    mor sym raw_sym proof_tree
          => lid ->
             Maybe ((GTypes.HSign sig,
                     [Named (GTypes.HFORMULA sen symb_items raw_sym)]) ->
             GTypes.H_BASIC_SPEC sen symb_items raw_sym)
convertHTheory baseLid = Just $
 \(s, nsens) -> if (s == emptyHSign baseLid) && (null nsens)
                  then GTypes.Basic_spec []
                  else error $ "convertHTheory nyi"

statSymbMapItems :: Logic lid sublogics basic_spec sen
                    symb_items symb_map_items sig
                    mor sym raw_sym proof_tree
          =>  lid -> GTypes.HSign sig -> Maybe (GTypes.HSign sig)
             -> [GTypes.H_SYMB_MAP_ITEMS symb_map_items]
             -> Result (EndoMap (GTypes.HRawSymbol sym raw_sym))
statSymbMapItems baseLid sig1 msig2 sitems = do
 let (bm, hm) = foldl (\(b, h) x -> case x of
                         GTypes.BaseSymbMapItems si -> (b ++ [si], h)
                         _ -> (b, h ++ [x])
                      ) ([],[]) sitems
 bmap <- stat_symb_map_items baseLid (GTypes.baseSig sig1)
            (case msig2 of
               Nothing -> Nothing
               Just sig2 -> Just $ GTypes.baseSig sig2)
            bm
 let bmap' = Map.fromList $
             map (\(x,y) ->
                   (GTypes.BaseRawSymbol x, GTypes.BaseRawSymbol y)) $
             Map.toList bmap
     getIdKind i sig = if Set.member i $ GTypes.noms sig
                        then GTypes.ASymbol $ GTypes.HSymb i GTypes.Nom
                        else if i `elem` (Map.keys $ GTypes.mods sig)
                              then GTypes.ASymbol $ GTypes.HSymb i $
                                                    GTypes.Mod 2
                              else error $
                                     "unknown symbol " ++ show i
                                     -- TODO: improve
     statSymbMapItem sf si =
       case si of
         GTypes.HSymbMapItems smis _ ->
           foldl (\f x -> case x of
                            GTypes.HSymbItem i ->
                              let rsym = getIdKind i sig1
                              in Map.insert rsym rsym f
                            GTypes.HMapItem i j _ ->
                              let rsym1 = getIdKind i sig1
                                  rsym2 = case msig2 of
                                   Nothing -> case rsym1 of
                                    GTypes.ASymbol (GTypes.HSymb _ k) ->
                                     GTypes.ASymbol $ GTypes.HSymb j k
                                    _ -> error "should never happen"
                                    -- TODO: improve
                                   Just sig2 -> getIdKind j sig2
                              in Map.insert rsym1 rsym2 f)
                              -- TODO: improve, kinds should match
                 sf smis
         _ -> error "should not happen" -- TODO: better error message
     bmap'' = foldl statSymbMapItem Map.empty hm
 return $ Map.union bmap' bmap''

inducedFromMorphism :: Logic lid sublogics basic_spec sen
                       symb_items symb_map_items sig
                       mor sym raw_sym proof_tree
        => lid ->
           EndoMap (GTypes.HRawSymbol sym raw_sym) ->
           GTypes.HSign sig ->
           Result (GTypes.HMorphism sig mor)
inducedFromMorphism baseLid sm hsign = do
 let (bm, nm, mm) = foldl (\(b, n, m) (rs1, rs2) -> case (rs1, rs2) of
          (GTypes.BaseRawSymbol s1, GTypes.BaseRawSymbol s2) ->
              (b ++ [(s1, s2)], n, m)
          (GTypes.AKindedSymb k1 i, GTypes.AKindedSymb k2 i') ->
            case (k1, k2) of
             (GTypes.HKindAsG GTypes.Nom,
              GTypes.HKindAsG GTypes.Nom) -> (b, n ++ [(i, i')], m)
             (GTypes.HKindAsG (GTypes.Mod _),
              GTypes.HKindAsG (GTypes.Mod _)) -> (b, n, m ++ [(i, i')])
             _ -> error "kind mismatch" -- TODO:improve message
          (GTypes.ASymbol hsym1, GTypes.ASymbol hsym2) ->
            case (hsym1, hsym2) of
             (GTypes.HSymb i k1,
              GTypes.HSymb i' k2) ->
                case (k1, k2) of
                 (GTypes.Nom, GTypes.Nom) -> (b, n ++ [(i, i')], m)
                 (GTypes.Mod _, GTypes.Mod _) -> (b, n, m ++ [(i, i')])
                 _ -> error "kind mismatch" -- TODO:improve message
             _ -> error "mismatch" -- TODO: better error message
          _ -> error "mismatch" -- TODO: better error message
        ) ([], [], []) $ Map.toList sm
 bMor <- induced_from_morphism baseLid (Map.fromList bm) $
                               GTypes.baseSig hsign
 let tbSig = cod bMor
     tsign = GTypes.HSign tbSig
                 (Set.map (\x -> Map.findWithDefault x
                                      x $ Map.fromList nm) $
                          GTypes.noms hsign)
                  (Map.mapKeys (\x -> Map.findWithDefault x
                                       x $ Map.fromList mm) $
                          GTypes.mods hsign)
     hMor = GTypes.HMorphism hsign tsign bMor
                             (Map.fromList nm) (Map.fromList mm)
 return hMor

inducedFromToMorphism :: Logic lid sublogics basic_spec sen
                       symb_items symb_map_items sig
                       mor sym raw_sym proof_tree
        => lid -> EndoMap (GTypes.HRawSymbol sym raw_sym) ->
                  ExtSign (GTypes.HSign sig) (GTypes.HSymbol sym) ->
                  ExtSign (GTypes.HSign sig) (GTypes.HSymbol sym) ->
                  Result (GTypes.HMorphism sig mor)
inducedFromToMorphism baseLid sm
                      (ExtSign hsign1 hsyms1)
                      (ExtSign hsign2 hsyms2) = do
 let (bm, nm, mm) = foldl (\(b, n, m) (rs1, rs2) -> case (rs1, rs2) of
          (GTypes.BaseRawSymbol s1, GTypes.BaseRawSymbol s2) ->
              (b ++ [(s1, s2)], n, m)
          (GTypes.AKindedSymb k1 i,
           GTypes.AKindedSymb k2 i') -> case (k1, k2) of
             (GTypes.HKindAsG GTypes.Nom, GTypes.HKindAsG GTypes.Nom) ->
                (b, n ++ [(i, i')], m)
             (GTypes.HKindAsG (GTypes.Mod _),
              GTypes.HKindAsG (GTypes.Mod _)) ->
                (b, n, m ++ [(i, i')])
             _ -> error "kind mismatch" -- TODO:improve message
          (GTypes.ASymbol hsym1,
           GTypes.ASymbol hsym2) -> case (hsym1, hsym2) of
             (GTypes.HSymb i k1, GTypes.HSymb i' k2) -> case (k1, k2) of
                (GTypes.Nom, GTypes.Nom) -> (b, n ++ [(i, i')], m)
                (GTypes.Mod _, GTypes.Mod _) -> (b, n, m ++ [(i, i')])
                _ -> error "kind mismatch" -- TODO:improve message
             _ -> error "mismatch" -- TODO: better error message
          _ -> error "mismatch" -- TODO: better error message
                           ) ([], [], []) $ Map.toList sm
     bsyms1 = concatMap (\x -> case x of
                                 GTypes.BaseSymb s -> [s]
                                 _ -> []) $ Set.toList hsyms1
     bsyms2 = concatMap (\x -> case x of
                                 GTypes.BaseSymb s -> [s]
                                 _ -> []) $ Set.toList hsyms2
 bMor <- induced_from_to_morphism baseLid (Map.fromList bm)
          (ExtSign (GTypes.baseSig hsign1) $ Set.fromList bsyms1)
          (ExtSign (GTypes.baseSig hsign2) $ Set.fromList bsyms2)
 return $ GTypes.HMorphism hsign1 hsign2 bMor
                           (Map.fromList nm) (Map.fromList mm)
-- TODO: should check that these actually fit the signatures


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
      => Bool ->
-- flag: has quantification on nominals?
         [String] ->
-- kinds allowed in quantification on base symbols, empty for none
         lid ->
-- lid of the base logic, to call methods in Logic class
         String ->
-- name of the hybrid logic, for qualifications
         Maybe sublogics ->
-- if we make the hybridization of a sublogic,
-- check that the case theory lives in that sublogic
         (GTypes.H_BASIC_SPEC sen symb_items raw_sym,
          GTypes.HSign sig,
          GlobalAnnos) ->
         Result (GTypes.H_BASIC_SPEC sen symb_items raw_sym,
                 ExtSign (GTypes.HSign sig) (GTypes.HSymbol sym),
                 [Named (GTypes.HFORMULA sen symb_items raw_sym)])
basicHAnalysis hasQNominals kVars baseLid hLogic mSubl (bs, inSig, ga) = let
  hth = HTheoryAna inSig Set.empty [] [] ga []
  (newBs, accTh) =
   CState.runState (anaBasicHSpec hasQNominals kVars baseLid hLogic bs) hth
  ds = reverse $ anaDiags accTh
  outSig = hSign accTh
  sents = hSens accTh
  (baseSig, baseSens) = (GTypes.baseSig outSig,
                         concatMap (getBaseSens . sentence) sents)
 in case mSubl of
     Nothing ->
                Result ds $ Just (newBs,
                                  ExtSign outSig $ declSyms accTh, sents)
     Just aSub ->
                  do
       let tSub = sublogicOfTheo baseLid (baseSig, baseSens)
       if isSubElem tSub aSub
         then Result ds $ Just (newBs, ExtSign outSig $ declSyms accTh, sents)
         else fail $
                "The sublogic of the analyzed theory should be " ++
                 sublogicName aSub ++ ", but it is " ++
                 sublogicName tSub

getBaseSens :: GTypes.HFORMULA sen symb_items raw_sym -> [sen]
getBaseSens s = case s of
 GTypes.Base_formula f _ -> [f]
 GTypes.Negation hf _ -> getBaseSens hf
 GTypes.Conjunction hfs _ -> concatMap getBaseSens hfs
 GTypes.Disjunction hfs _ -> concatMap getBaseSens hfs
 GTypes.Implication hf1 hf2 _ -> getBaseSens hf1 ++ getBaseSens hf2
 GTypes.Equivalence hf1 hf2 _ -> getBaseSens hf1 ++ getBaseSens hf2
 GTypes.AtState _ _ hf _ -> getBaseSens hf
 GTypes.BoxFormula  _ _ hf _ -> getBaseSens hf
 GTypes.DiamondFormula  _ _ hf _ -> getBaseSens hf
 _ -> []

anaBasicHSpec :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
      =>  Bool -> [String] -> lid -> String
       -> GTypes.H_BASIC_SPEC sen symb_items raw_sym
       -> CState.State (HTheoryAna sig sen symb_items raw_sym sym)
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
anaBasicHSpec hasQNominals kVars baseLid hLogic (GTypes.Basic_spec al) =
  fmap GTypes.Basic_spec $
      mapAnM (anaBasicHItems hasQNominals kVars baseLid hLogic) al

anaBasicHItems :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
      => Bool -> [String] -> lid -> String
      -> GTypes.H_BASIC_ITEMS sen symb_items raw_sym
      -> CState.State (HTheoryAna sig sen symb_items raw_sym sym)
                      (GTypes.H_BASIC_ITEMS sen symb_items raw_sym)
anaBasicHItems hasQNominals kVars baseLid hLogic bi =
 case bi of
  GTypes.Nom_decl (GTypes.Nom_item noms _) -> do
    hth <- CState.get
    let hsign = hSign hth
    let Result ds mhsign' =
          foldM (\s n -> addNomToSig s $ mkId [n]) hsign noms
    case mhsign' of
     Nothing -> error $ "cannot add nominals" ++ show ds
     Just hsign' -> do
      CState.put $ hth {hSign = hsign', anaDiags = ds ++ anaDiags hth}
      return bi
  GTypes.Mod_decl (GTypes.Mod_item mods i _) -> do
    hth <- CState.get
    let hsign = hSign hth
    let Result ds mhsign' =
          foldM (\s m -> addModToSig s (mkId [m]) i) hsign mods
    case mhsign' of
      Nothing -> error $ "cannot add modalities" ++ show ds
      Just hsign' -> do
       CState.put $ hth { hSign = hsign', anaDiags = ds ++ anaDiags hth }
       return bi
  GTypes.Axiom_items annofs -> do
    hth <- CState.get
    let (hth', annofs') = foldl (\(h, l) f ->
                                    let (f', h') = CState.runState
                                                    (anaHFORMULA hasQNominals
                                                     kVars baseLid hLogic f)
                                                    h
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
   => lid ->  GTypes.HSign sig -> GTypes.HFORMULA sen symb_items raw_sym ->
      GTypes.HFORMULA sen symb_items raw_sym
simplifyHSen baseLid hsig hsen =
 case hsen of
  GTypes.Base_formula pfrm r ->
    let pfrm' = simplify_sen baseLid (GTypes.baseSig hsig) pfrm
    in GTypes.Base_formula pfrm' r
  GTypes.Nominal _ _ _ _ ->
    hsen
  GTypes.AtState s nom frm r ->
    GTypes.AtState s nom (simplifyHSen baseLid hsig frm) r
  GTypes.BoxFormula s md frm r ->
    GTypes.BoxFormula s md (simplifyHSen baseLid hsig frm) r
  GTypes.DiamondFormula s md frm r ->
    GTypes.DiamondFormula s md (simplifyHSen baseLid hsig frm) r
  GTypes.Negation frm r ->
    GTypes.Negation (simplifyHSen baseLid hsig frm) r
  GTypes.Conjunction xs r ->
    GTypes.Conjunction (map (simplifyHSen baseLid hsig) xs) r
  GTypes.Disjunction xs r ->
    GTypes.Disjunction (map (simplifyHSen baseLid hsig) xs) r
  GTypes.Implication x y r ->
    GTypes.Implication (simplifyHSen baseLid hsig x)
                       (simplifyHSen baseLid hsig y) r
  GTypes.Equivalence x y r ->
    GTypes.Equivalence (simplifyHSen baseLid hsig x)
                       (simplifyHSen baseLid hsig y) r
  GTypes.QuantVarsParse _ _ _ _ ->
    error "GenHyb.GenMethods.simplifyHSen: sentence not analyzed"
  GTypes.QuantVars q vdecls frm r ->
   let Result ds msig = foldM (add_symb_to_sign baseLid)
                              (GTypes.baseSig hsig) $
                        map (\x -> fromJust $ raw_to_symbol baseLid x) vdecls
   in case msig of
       Nothing -> error $ "GenHyb.GenMethods.simplifyHSen:" ++ show ds
       Just bsig -> GTypes.QuantVars q vdecls
                       (simplifyHSen baseLid hsig{GTypes.baseSig = bsig} frm)
                       r
  GTypes.QuantNominals q noms frm r ->
    GTypes.QuantNominals q noms (simplifyHSen baseLid hsig frm) r

getNomVars :: HTheoryAna sig sen symb_items raw_sym sym -> Set.Set Id
getNomVars hth =
  Set.fromList $
   concatMap (\i -> case i of
    GTypes.ASymbol (GTypes.HSymb v GTypes.Nom) -> [v]
    _ -> []) $
  hVars hth

anaHFORMULA :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
      => Bool -> [String] -> lid ->
         String -> -- the name of the hybrid logic, for qualfications
         Annoted (GTypes.HFORMULA sen symb_items raw_sym) ->
         CState.State (HTheoryAna sig sen symb_items raw_sym sym)
                       (Annoted (GTypes.HFORMULA sen symb_items raw_sym),
                        Annoted (GTypes.HFORMULA sen symb_items raw_sym)
                      )
anaHFORMULA hasQNominals kVars baseLid hLogic hf = case item hf of
 GTypes.Base_formula bsen r -> do
   hth <- CState.get
   let (isNom, mNomName) = is_nominal_sen baseLid
                             (Set.union (GTypes.noms $ hSign hth) $
                                        getNomVars hth)
                             bsen
   if not isNom then do
     let senAnaBase = case sen_analysis baseLid of
                       Nothing ->
                        error $ "sentence analysis not implemented for logic "
                                ++ show baseLid
                       Just f -> f
         emptyBasicSpec = case convertTheory baseLid of
                            Nothing ->
                              error $ "can't convert theory in logic "
                                      ++ show baseLid
                            Just f -> f $ (empty_signature baseLid, [])
         baseVars = concatMap (\s -> case s of
                                      GTypes.BaseRawSymbol rs -> [rs]
                                      _ -> [] ) $ hVars hth
         baseVarsSyms = fromJust $ convertRawSyms baseLid baseVars
     let Result dadd mAnaSig = foldM (add_symb_to_sign baseLid)
                                     (GTypes.baseSig $ hSign hth) baseVarsSyms
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
          Nothing ->
            error "Can't have nominal formula without nominal name"
            -- should never happen!
          Just i ->
            let iNom = GTypes.ASymbol $ GTypes.HSymb i GTypes.Nom
            in if iNom `elem` hVars hth then
                  let hf' = hf { item = GTypes.Nominal ""
                                               True (idToSimpleId i)
                                               nullRange }
                  -- "" because we default to the top logic
                  in return (hf', hf')
                 else if i `elem` (GTypes.noms $ hSign hth) then
                         let hf' = hf { item = GTypes.Nominal ""
                                                      False (idToSimpleId i)
                                                      nullRange }
                         in return (hf', hf')
                       else do
-- TODO: undeclared nominals are not identified as nominals in isNominalSen!
                          CState.put $
                            hth {anaDiags = (mkDiag Error
                                                    "undeclared nominal" i) :
                                            (anaDiags hth) }
                          return (hf, hf)
 GTypes.Negation f r -> do
   (af1, af2) <- anaHFORMULA hasQNominals kVars baseLid hLogic $ emptyAnno f
   let hf'= hf { item = GTypes.Negation (item af2) r}
   return (hf{item = GTypes.Negation (item af1) r}, hf')
 GTypes.Conjunction fs r -> do
   afs' <- mapM (anaHFORMULA hasQNominals kVars baseLid hLogic) $
                map emptyAnno fs
   return $ (hf { item = GTypes.Conjunction (map (item.fst) afs') r},
             hf { item = GTypes.Conjunction (map (item.snd) afs') r})
 GTypes.Disjunction fs r -> do
   afs' <- mapM (anaHFORMULA hasQNominals kVars baseLid hLogic) $
                map emptyAnno fs
   return $ (hf { item = GTypes.Disjunction (map (item.fst) afs') r},
             hf { item = GTypes.Disjunction (map (item.snd) afs') r})
 GTypes.Implication f1 f2 r -> do
   f1' <- anaHFORMULA hasQNominals kVars baseLid hLogic $ emptyAnno f1
   f2' <- anaHFORMULA hasQNominals kVars baseLid hLogic $ emptyAnno f2
   return $ (hf {item = GTypes.Implication (item $ fst f1')
                                           (item $ fst f2') r},
             hf {item = GTypes.Implication (item $ snd f1')
                                           (item $ snd f2') r})
 GTypes.Equivalence f1 f2 r -> do
   f1' <- anaHFORMULA hasQNominals kVars baseLid hLogic $ emptyAnno f1
   f2' <- anaHFORMULA hasQNominals kVars baseLid hLogic $ emptyAnno f2
   return $ (hf {item = GTypes.Equivalence (item $ fst f1')
                                           (item $ fst f2') r},
             hf {item = GTypes.Equivalence (item $ snd f1')
                                           (item $ snd f2') r})
 GTypes.Nominal s _b i _r ->
  if (s /= "") && (s /= hLogic) then
   error $ "Expected logic " ++ hLogic ++
           " but got " ++ s ++ "instead. Check that qualification is correct."
  else do
   hth <- CState.get --TODO: check that if b holds, i must be a variable?
   if ( Set.member (simpleIdToId i) (GTypes.noms $ hSign hth) ) ||
       ( (GTypes.ASymbol $ GTypes.HSymb (simpleIdToId i) GTypes.Nom)
         `elem` (hVars hth))
           then return (hf, hf)
           else do
     CState.put $ hth {anaDiags = (mkDiag Error "undeclared nominal" i)
                                  : (anaDiags hth)}
     return (hf,hf)
 GTypes.AtState s i f r ->
  if (s /= "") && (s /= hLogic) then
   error $ "Expected logic " ++ hLogic ++ " but got "
           ++ s ++ "instead. Check that qualification is correct."
  else do
   hth <- CState.get
   if ( Set.member (simpleIdToId i) (GTypes.noms $ hSign hth) ) ||
      ( (GTypes.ASymbol $ GTypes.HSymb (simpleIdToId i) GTypes.Nom)
        `elem` (hVars hth))
           then do
    f' <- anaHFORMULA hasQNominals kVars baseLid hLogic $ emptyAnno f
    return $ (hf { item = GTypes.AtState s i (item $ fst f') r},
              hf { item = GTypes.AtState s i (item $ snd f') r})
           else do
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared nominal" i)
                                 : (anaDiags hth)}
    return (hf,hf)
 GTypes.BoxFormula s i f r ->
  if (s /= "") && (s /= hLogic) then
   error $ "Expected logic " ++ hLogic ++ " but got "
           ++ s ++ "instead. Check that qualification is correct."
  else do
   hth <- CState.get
   if (simpleIdToId i) `elem` (Map.keys $ GTypes.mods $ hSign hth)
            then do
    f' <- anaHFORMULA hasQNominals kVars baseLid hLogic $ emptyAnno f
    return $ (hf { item = GTypes.BoxFormula s i (item $ fst f') r},
              hf { item = GTypes.BoxFormula s i (item $ snd f') r})
   else do
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared modality" i)
                      : (anaDiags hth)}
    return (hf,hf)
 GTypes.DiamondFormula s i f r ->
  if (s /= "") && (s /= hLogic) then
   error $ "Expected logic " ++ hLogic ++ " but got "
           ++ s ++ "instead. Check that qualification is correct."
  else do
   hth <- CState.get
   if (simpleIdToId i) `elem` (Map.keys $ GTypes.mods $ hSign hth)
            then do
    f' <- anaHFORMULA hasQNominals kVars baseLid hLogic $ emptyAnno f
    return $ (hf { item = GTypes.DiamondFormula s i (item $ fst f') r},
              hf { item = GTypes.DiamondFormula s i (item $ snd f') r})
   else do
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared modality" i)
                                 : (anaDiags hth)}
    return (hf,hf)
 GTypes.QuantVarsParse q vs f r -> do
  let s = case q of
           GTypes.HUniversal x -> x
           GTypes.HExistential x -> x
  if (s /= "") && (s /= hLogic) then
     error $ "Expected logic " ++ hLogic ++ " but got "
             ++ s ++ "instead. Check that qualification is correct."
  else do
   hth <- CState.get
   if null kVars then do
     CState.put $
      hth {anaDiags = (mkDiag Error
                              "quantification on base symbols not allowed:"
                              (show hf))
                      : (anaDiags hth)}
     return (hf, hf)
   else do
    let Result dsyms mrsyms = stat_symb_items baseLid
                                              (GTypes.baseSig $ hSign hth) vs
       -- the variables don't appear in hSign hth, that's why we get Nothing!
    case mrsyms of
     Nothing -> do
       CState.put $ hth {anaDiags = dsyms ++ anaDiags hth}
       return (hf, hf)
     Just rsyms ->
                   do
      let msyms = convertRawSyms baseLid rsyms
 -- TODO: this should be a Result, not a Maybe, so we know which symbol failed
      case msyms of
       Nothing -> do
        CState.put $
         hth {anaDiags = (mkDiag Error
                           "could not convert all raw symbols to symbols"
                           (show rsyms))
                         : anaDiags hth}
        return (hf, hf)
       Just syms -> do
        let symsKinds = filter (\x -> not (x `elem` kVars)) $
                         map (extSymKind baseLid) syms
        case symsKinds of
         [] -> do
           let (f', hth') = CState.runState
                             (anaHFORMULA hasQNominals kVars
                                          baseLid hLogic $ emptyAnno f) $
                         hth {hVars = hVars hth ++
                                      map GTypes.BaseRawSymbol rsyms }
           CState.put $ hth {anaDiags = anaDiags hth' ++ anaDiags hth}
           return $ (hf{item = GTypes.QuantVars q rsyms (item $ fst f') r},
                    hf{item = GTypes.QuantVars q rsyms (item $ snd f') r})
         _ -> do -- TODO: better error message!
           let diagKinds =
                map (\k -> mkDiag Error
                             ("quantification not allowed on symbols of kind "
                              ++ k)
                             (show hf) )
                symsKinds
           CState.put $ hth {anaDiags = diagKinds ++ (anaDiags hth)}
           return (hf, hf)
 GTypes.QuantVars _ _ _ _ -> error $ "Already analyzed sentence:" ++ show hf
 GTypes.QuantNominals q ns f r ->
  if hasQNominals then do
   hth <- CState.get
   let (f', hth') =
          CState.runState (anaHFORMULA hasQNominals kVars
                                       baseLid hLogic $ emptyAnno f) $
                 hth {hVars = hVars hth ++
                              map (\i -> GTypes.ASymbol $
                                          GTypes.HSymb (simpleIdToId i)
                                                       GTypes.Nom) ns}
   CState.put $ hth {anaDiags = anaDiags hth' ++ anaDiags hth}
   return $ (hf { item = GTypes.QuantNominals q ns (item $ fst f') r},
             hf { item = GTypes.QuantNominals q ns (item $ snd f') r})
  else error "the logic does not allow quantification on nominals"

convertRawSyms :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
                => lid -> [raw_sym] -> Maybe [sym]
convertRawSyms baseLid rawSymList =
           let mSymList = map (raw_to_symbol baseLid) rawSymList
           in if Nothing `elem` mSymList then
                  -- trace (show mSymList) $
                 Nothing
               else -- trace "convertRawSyms2" $
                    Just $ map fromJust mSymList

-- translate constraints to CASL sentences
-- for some this can be done independent of the underlying logic
-- for others, this requires logic-dependent analysis

constrToSens :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
             => lid -> GTypes.HSign sig -> String ->
                SemanticConstraint -> Result ([Named CBasic.CASLFORMULA])
constrToSens lid hsign a c =
 let binMods = map fst $
               filter (\(_, y) -> y == 2) $
               Map.toList $ GTypes.mods hsign
     st = genName $ "ST_" ++ a
 in case c of
     ReflexiveMod ->
 -- forall w : st . m(w,w)
      return $
      map (\m -> makeNamed ("ga_reflexive_" ++ show m) $
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w") st] $
                  CBasic.mkPredication
                    (CBasic.mkQualPred m $
                        CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w") st nullRange,
                     CBasic.Qual_var (genToken "w") st nullRange]
          )
       binMods
     SymmetricMod ->
-- forall w1, w2 : st . m(w1,w2) => m(w2, w1)
       return $
       map (\m -> makeNamed ("ga_symmetric_" ++ show m) $
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st,
                                  CBasic.mkVarDecl (genToken "w2") st] $
                  CBasic.mkImpl
                  (CBasic.mkPredication
                    (CBasic.mkQualPred m $
                       CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange,
                     CBasic.Qual_var (genToken "w2") st nullRange])
                  (CBasic.mkPredication
                    (CBasic.mkQualPred m $
                       CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w2") st nullRange,
                     CBasic.Qual_var (genToken "w1") st nullRange])
          )
       binMods
     TransitiveMod ->
-- forall w1, w2,w3 : st . m(w1,w2) /\ m(w2, w3) => m(w1, w3)
      return $
      map (\m -> makeNamed ("ga_transitive_" ++ show m) $
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st,
                                  CBasic.mkVarDecl (genToken "w2") st,
                                  CBasic.mkVarDecl (genToken "w3") st] $
                  CBasic.mkImpl
                  (CBasic.conjunct
                   [ CBasic.mkPredication
                      (CBasic.mkQualPred m $
                        CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange,
                       CBasic.Qual_var (genToken "w2") st nullRange],
                     CBasic.mkPredication
                      (CBasic.mkQualPred m $
                         CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w2") st nullRange,
                       CBasic.Qual_var (genToken "w3") st nullRange]
                   ]
                  )
                  (CBasic.mkPredication
                    (CBasic.mkQualPred m $
                      CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange,
                     CBasic.Qual_var (genToken "w3") st nullRange])
          )
       binMods
     SerialMod ->
-- forall w1 : st . exists w2 : st . m(w1, w2)
      return $
      map (\m -> makeNamed ("ga_serial_" ++ show m) $
                 CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st] $
                  CBasic.mkExist [CBasic.mkVarDecl (genToken "w2") st] $
                   CBasic.mkPredication
                    (CBasic.mkQualPred m $
                      CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange,
                     CBasic.Qual_var (genToken "w2") st nullRange]
          )
       binMods
     EuclideanMod ->
-- forall w1, w2,w3 : st . m(w1,w2) /\ m(w1, w3) => m(w2, w3)
      return $
      map (\m -> makeNamed ("ga_Euclidean_" ++ show m) $
                 CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st,
                                  CBasic.mkVarDecl (genToken "w2") st,
                                  CBasic.mkVarDecl (genToken "w3") st] $
                  CBasic.mkImpl
                  (CBasic.conjunct
                   [ CBasic.mkPredication
                      (CBasic.mkQualPred m $
                        CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange,
                       CBasic.Qual_var (genToken "w2") st nullRange],
                     CBasic.mkPredication
                      (CBasic.mkQualPred m $
                        CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange,
                       CBasic.Qual_var (genToken "w3") st nullRange]
                   ]
                  )
                  (CBasic.mkPredication
                    (CBasic.mkQualPred m $
                       CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w2") st nullRange,
                     CBasic.Qual_var (genToken "w3") st nullRange])
          )
       binMods
     FunctionalMod ->
-- forall w1 : st . exists! w2 : st . m(w1, w2)
      return $
      map (\m -> makeNamed ("ga_functional_" ++ show m) $
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st] $
                  CBasic.Quantification
                   CBasic.Unique_existential
                   [CBasic.mkVarDecl (genToken "w2") st]
                   (CBasic.mkPredication
                    (CBasic.mkQualPred m $
                       CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange,
                     CBasic.Qual_var (genToken "w2") st nullRange]
                   )
                   nullRange
          )
       binMods
     LinearMod ->
-- forall w1, w2,w3 : st . m(w1,w2) /\ m(w1, w3)
--                         => (m(w2, w3) \/ m(w3, w2) \/ w3 = w2)
      return $
      map (\m -> makeNamed ("ga_linear_" ++ show m) $
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st,
                                  CBasic.mkVarDecl (genToken "w2") st,
                                  CBasic.mkVarDecl (genToken "w3") st] $
                  CBasic.mkImpl
                  (CBasic.conjunct
                   [ CBasic.mkPredication
                      (CBasic.mkQualPred m $
                         CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange,
                       CBasic.Qual_var (genToken "w2") st nullRange],
                     CBasic.mkPredication
                      (CBasic.mkQualPred m $
                         CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w1") st nullRange,
                       CBasic.Qual_var (genToken "w3") st nullRange]
                   ]
                  )
                  (CBasic.disjunct
                    [CBasic.mkPredication
                      (CBasic.mkQualPred m $
                        CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w2") st nullRange,
                       CBasic.Qual_var (genToken "w3") st nullRange],
                     CBasic.mkPredication
                      (CBasic.mkQualPred m $
                        CBasic.Pred_type [st, st] nullRange)
                      [CBasic.Qual_var (genToken "w3") st nullRange,
                       CBasic.Qual_var (genToken "w2") st nullRange],
                     CBasic.mkStEq (CBasic.mkVarTerm (genToken "w2") st)
                                   (CBasic.mkVarTerm (genToken "w3") st)
                   ]
                  )
          )
       binMods
     TotalMod ->
-- forall w1, w2 : st . m(w1,w2) \/ m(w2, w1)
      return $
      map (\m -> makeNamed ("ga_total_" ++ show m) $
                  CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st,
                                  CBasic.mkVarDecl (genToken "w2") st] $
                  CBasic.disjunct
                  [CBasic.mkPredication
                    (CBasic.mkQualPred m $
                       CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w1") st nullRange,
                     CBasic.Qual_var (genToken "w2") st nullRange],
                   CBasic.mkPredication
                    (CBasic.mkQualPred m $
                       CBasic.Pred_type [st, st] nullRange)
                    [CBasic.Qual_var (genToken "w2") st nullRange,
                     CBasic.Qual_var (genToken "w1") st nullRange]
                  ]
          )
       binMods
     _ -> constr_to_sens lid (GTypes.baseSig hsign) a c


senAnalysis :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
               => Bool -> [String] -> lid -> String ->
                 Maybe ((GTypes.H_BASIC_SPEC sen symb_items raw_sym,
                         GTypes.HSign sig,
                         GTypes.HFORMULA sen symb_items raw_sym
                         ) ->
                         Result (GTypes.HFORMULA sen symb_items raw_sym,
                                 GTypes.HFORMULA sen symb_items raw_sym)
                        )
senAnalysis hasQNominals kVars baseLid hLogic = Just $
  \ (_hBSpec, hsign, hsen) -> do
      let
        hth = HTheoryAna hsign Set.empty [] [] emptyGlobalAnnos []
        f = Annoted hsen nullRange [] []
        (annofs, _hth') =
           CState.runState (anaHFORMULA hasQNominals
                               kVars baseLid hLogic f) hth
      return (item $ fst annofs, item $ snd annofs)

isNominalSenH :: Logic lid sublogics basic_spec sen
                  symb_items symb_map_items sig
                   mor sym raw_sym proof_tree
                 => lid -> Set.Set Id ->
                    GTypes.HFORMULA sen symb_items raw_sym
                    -> (Bool, Maybe Id)
isNominalSenH baseLid noms (GTypes.Base_formula sen _) =
  is_nominal_sen baseLid noms sen
isNominalSenH _ _ _ = (False, Nothing)

--------------------------------------------------------------------
-- double hybridization
--------------------------------------------------------------------

senHAnalysis :: (Show sym,
                 Show raw_sym,
                 Show sen,
                 Show symb_items,
                 Show sublogics',
                 Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree')
  => Bool -> [String] -> hlid -> String ->
    Maybe ((GTypes.H_BASIC_SPEC (GTypes.HFORMULA sen symb_items raw_sym)
                                (GTypes.H_SYMB_ITEMS sym symb_items)
                                (GTypes.HRawSymbol sym raw_sym),
            GTypes.HSign (GTypes.HSign sig),
            GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                            (GTypes.H_SYMB_ITEMS sym symb_items)
                            (GTypes.HRawSymbol sym raw_sym)
            ) ->
            Result (GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                                    (GTypes.H_SYMB_ITEMS sym symb_items)
                                    (GTypes.HRawSymbol sym raw_sym),
                    GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                                    (GTypes.H_SYMB_ITEMS sym symb_items)
                                    (GTypes.HRawSymbol sym raw_sym)
                    )
          )
senHAnalysis hasQNominals kVars hlid hhLogic = Just $
  \ (_hBSpec, hsign, hsen) -> do
      let
        hth = HTheoryAna hsign Set.empty [] [] emptyGlobalAnnos []
        f = Annoted hsen nullRange [] []
        (annofs, _hth') =
          CState.runState (anaLHFORMULA hasQNominals kVars hlid hhLogic f) hth
      return (item $ fst annofs, item $ snd annofs)

basicHHAnalysis :: (Show sym,
                 Show raw_sym,
                 Show sen,
                 Show symb_items,
                 Show sublogics',
                 Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
                )
      => Bool ->
-- flag: has quantification on nominals?
         [String] ->
-- kinds allowed in quantification on base symbols, empty for none
         hlid ->
-- lid of the base logic, to call methods in Logic class
         String ->
 -- name of the hybrid logic, for qualifications
         Maybe sublogics' ->
-- if we make the hybridization of a sublogic,
-- check that the case theory lives in that sublogic
         (GTypes.H_BASIC_SPEC (GTypes.HFORMULA sen symb_items raw_sym)
                              (GTypes.H_SYMB_ITEMS sym symb_items)
                              (GTypes.HRawSymbol sym raw_sym),
          GTypes.HSign (GTypes.HSign sig), GlobalAnnos) ->
         Result (GTypes.H_BASIC_SPEC (GTypes.HFORMULA sen symb_items raw_sym)
                                     (GTypes.H_SYMB_ITEMS sym symb_items)
                                     (GTypes.HRawSymbol sym raw_sym),
                 ExtSign (GTypes.HSign (GTypes.HSign sig))
                         (GTypes.HSymbol (GTypes.HSymbol sym)),
                 [Named (GTypes.HFORMULA
                           (GTypes.HFORMULA sen symb_items raw_sym)
                           (GTypes.H_SYMB_ITEMS sym symb_items)
                           (GTypes.HRawSymbol sym raw_sym)
                         )]
                )
basicHHAnalysis hasQNominals kVars hlid hhLogic mSubl (bs, inSig, ga) =  let
  hth = HTheoryAna inSig Set.empty [] [] ga []
  (newBs, accTh) =
   CState.runState (anaBasicHHSpec hasQNominals kVars hlid hhLogic bs) hth
  ds = reverse $ anaDiags accTh
  outSig = hSign accTh
  sents = hSens accTh
  (baseSig, baseSens) = (GTypes.baseSig outSig,
                         concatMap (\s -> case sentence s of
                                           GTypes.Base_formula f _ -> [f]
                                           _ -> []) sents)
 in case mSubl of
     Nothing ->
                Result ds $
                 Just (newBs, ExtSign outSig $ declSyms accTh, sents)
     Just aSub -> do
       let tSub = sublogicOfTheo hlid (baseSig, baseSens)
       if isSubElem tSub aSub then
         Result ds $ Just (newBs, ExtSign outSig $ declSyms accTh, sents)
       else fail $ "The sublogic of the analyzed theory should be " ++
                   sublogicName aSub ++ ", but it is " ++ sublogicName tSub

anaBasicHHSpec :: (Show sym,
                 Show raw_sym,
                 Show sen,
                 Show symb_items,
                 Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
                )
      =>  Bool -> [String] -> hlid -> String
       -> GTypes.H_BASIC_SPEC (GTypes.HFORMULA sen symb_items raw_sym)
                              (GTypes.H_SYMB_ITEMS sym symb_items)
                              (GTypes.HRawSymbol sym raw_sym)
       -> CState.State
              (HTheoryAna (GTypes.HSign sig)
                          (GTypes.HFORMULA sen symb_items raw_sym)
                          (GTypes.H_SYMB_ITEMS sym symb_items)
                          (GTypes.HRawSymbol sym raw_sym)
                          (GTypes.HSymbol sym)
              )
              (GTypes.H_BASIC_SPEC (GTypes.HFORMULA sen symb_items raw_sym)
                                   (GTypes.H_SYMB_ITEMS sym symb_items)
                                   (GTypes.HRawSymbol sym raw_sym))
anaBasicHHSpec hasQNominals kVars hlid hhLogic (GTypes.Basic_spec al) =
  fmap GTypes.Basic_spec $
   mapAnM (anaBasicHHItems hasQNominals kVars hlid hhLogic) al

anaBasicHHItems :: (Show sym,
                 Show raw_sym,
                 Show sen,
                 Show symb_items,
                 Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
                )
      => Bool -> [String] -> hlid -> String
      -> GTypes.H_BASIC_ITEMS (GTypes.HFORMULA sen symb_items raw_sym)
                              (GTypes.H_SYMB_ITEMS sym symb_items)
                              (GTypes.HRawSymbol sym raw_sym)
      -> CState.State (HTheoryAna (GTypes.HSign sig)
                          (GTypes.HFORMULA sen symb_items raw_sym)
                          (GTypes.H_SYMB_ITEMS sym symb_items)
                          (GTypes.HRawSymbol sym raw_sym)
                          (GTypes.HSymbol sym))
                      (GTypes.H_BASIC_ITEMS
                          (GTypes.HFORMULA sen symb_items raw_sym)
                          (GTypes.H_SYMB_ITEMS sym symb_items)
                          (GTypes.HRawSymbol sym raw_sym))
anaBasicHHItems hasQNominals kVars hlid hhLogic bi =
 case bi of
  GTypes.Nom_decl (GTypes.Nom_item noms _) -> do
    hth <- CState.get
    let hsign = hSign hth
    let Result ds mhsign' = foldM (\s n -> addNomToSig s $ mkId [n])
                                  hsign noms
    case mhsign' of
     Nothing -> error $ "cannot add nominals" ++ show ds
     Just hsign' -> do
      CState.put $ hth {hSign = hsign', anaDiags = ds ++ anaDiags hth}
      return bi
  GTypes.Mod_decl (GTypes.Mod_item mods i _) -> do
    hth <- CState.get
    let hsign = hSign hth
    let Result ds mhsign' = foldM (\s m -> addModToSig s (mkId [m]) i)
                                  hsign mods
    case mhsign' of
      Nothing -> error $ "cannot add modalities" ++ show ds
      Just hsign' -> do
       CState.put $ hth { hSign = hsign', anaDiags = ds ++ anaDiags hth }
       return bi
  GTypes.Axiom_items annofs -> do
    hth <- CState.get
    let (hth', annofs') = foldl (\(h, l) f ->
                                   let (f', h') =
                                         CState.runState
                                          (anaLHFORMULA hasQNominals
                                           kVars hlid hhLogic f) h
                                   in (h', f':l)) (hth, []) annofs
    let replfs = reverse annofs'
        nfs = map (makeNamedSen.snd) replfs
    CState.put $ hth' {hSens = nfs ++ hSens hth'}
    return $ GTypes.Axiom_items $ map fst replfs

downcastHSen :: String ->
                GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                                (GTypes.H_SYMB_ITEMS sym symb_items)
                                (GTypes.HRawSymbol sym raw_sym) ->
                Result (GTypes.HFORMULA sen symb_items raw_sym)
downcastHSen hLogic hhsen =
 case hhsen of
  GTypes.Base_formula hsen _ -> return hsen
  GTypes.Nominal s b i r->
    if (s == hLogic) then
-- TODO: if s is "", warning that the default logic
-- changes from hLogic to its base?
     error $ "Cannot convert nominal from " ++
              hLogic ++ "to a sentence in the base logic"
    else return $ GTypes.Nominal s b i r
  GTypes.AtState s nom frm r ->
    if (s == hLogic) then
     error $ "Cannot convert sentence from " ++
             hLogic ++ "to a sentence in the base logic"
    else do
     frm' <- downcastHSen hLogic frm
     return $ GTypes.AtState s nom frm' r
  GTypes.BoxFormula s md frm r ->
   if (s == hLogic) then
     error $ "Cannot convert sentence from " ++
             hLogic ++ "to a sentence in the base logic"
    else do
     frm' <- downcastHSen hLogic frm
     return $ GTypes.BoxFormula s md frm' r
  GTypes.DiamondFormula s md frm r ->
    if (s == hLogic) then
     error $ "Cannot convert sentence from " ++
             hLogic ++ "to a sentence in the base logic"
    else do
     frm' <- downcastHSen hLogic frm
     return $ GTypes.DiamondFormula s md frm' r
  GTypes.Negation frm r -> do
    frm' <- downcastHSen hLogic frm
    return $ GTypes.Negation frm' r
  GTypes.Conjunction xs r -> do
    xs' <- mapM (downcastHSen hLogic) xs
    return $ GTypes.Conjunction xs' r
  GTypes.Disjunction xs r -> do
    xs' <- mapM (downcastHSen hLogic) xs
    return $ GTypes.Disjunction xs' r
  GTypes.Implication x y r -> do
    x' <- downcastHSen hLogic x
    y' <- downcastHSen hLogic y
    return $ GTypes.Implication x' y' r
  GTypes.Equivalence x y r -> do
    x' <- downcastHSen hLogic x
    y' <- downcastHSen hLogic y
    return $ GTypes.Equivalence x' y' r
  _ ->
    error $ "Cannot convert quantified sentence from " ++
            hLogic ++ "to a sentence in the base logic"

anaLHFORMULA :: (Show sym,
                 Show raw_sym,
                 Show sen,
                 Show symb_items,
                 Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
                )
      => Bool -> [String] -> hlid -> String ->
         Annoted (GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                                  (GTypes.H_SYMB_ITEMS sym symb_items)
                                  (GTypes.HRawSymbol sym raw_sym)) ->
         CState.State (HTheoryAna (GTypes.HSign sig)
                                  (GTypes.HFORMULA sen symb_items raw_sym)
                                  (GTypes.H_SYMB_ITEMS sym symb_items)
                                  (GTypes.HRawSymbol sym raw_sym)
                                  (GTypes.HSymbol sym))
                       (Annoted (GTypes.HFORMULA
                                  (GTypes.HFORMULA sen symb_items raw_sym)
                                  (GTypes.H_SYMB_ITEMS sym symb_items)
                                  (GTypes.HRawSymbol sym raw_sym)),
                        Annoted (GTypes.HFORMULA
                                  (GTypes.HFORMULA sen symb_items raw_sym)
                                  (GTypes.H_SYMB_ITEMS sym symb_items)
                                  (GTypes.HRawSymbol sym raw_sym))
                      )
anaLHFORMULA hasQNominals kVars hlid hhLogic hhf = case item hhf of
 GTypes.Base_formula hsen r -> do
  hth <- CState.get
  let allNoms = Set.union (getNomVars hth) $
                Set.union (GTypes.noms $ hSign hth)
                          (GTypes.noms $ GTypes.baseSig $ hSign hth)
  let (isNom, mNomName) = is_nominal_sen hlid allNoms hsen
-- TODO: perhaps add the variables too?
  if not isNom then do
     let senAnaBase = case sen_analysis hlid of
          Nothing -> error $ "sentence analysis not implemented for logic "
                              ++ show hlid
          Just f -> f
         emptyBasicSpec = case convertTheory hlid of
          Nothing -> error $ "can't convert theory in logic "
                                       ++ show hlid
          Just f -> f $ (empty_signature hlid, [])
         baseVars = concatMap (\s -> case s of
          GTypes.BaseRawSymbol rs -> [rs]
          _ -> [] ) $ hVars hth
         baseVarsSyms = fromJust $ convertRawSyms hlid baseVars
     let Result dadd mAnaSig = foldM (add_symb_to_sign hlid)
                               (GTypes.baseSig $ hSign hth) baseVarsSyms
     case mAnaSig of
      Nothing -> do
       CState.put $ hth {anaDiags = dadd ++ anaDiags hth}
       return (hhf, hhf)
      Just anaSig -> do
       let Result ds mf = senAnaBase
                           (emptyBasicSpec,
                            anaSig,
                            hsen)
       case mf of
         Nothing -> do
           CState.put $ hth {anaDiags = ds ++ anaDiags hth}
           return (hhf, hhf)
         Just (f1, f2) -> do
           let hhf1 = hhf {item = GTypes.Base_formula f1 r}
               hhf2 = hhf {item = GTypes.Base_formula f2 r}
           CState.put $ hth {anaDiags = ds ++ anaDiags hth}
           return (hhf1, hhf2)
    else case mNomName of
          Nothing -> error "Can't have nominal formula without nominal name"
                     -- should never happen!
          Just i -> -- trace ("i:" ++ show i) $
            let iNom = GTypes.ASymbol $ GTypes.HSymb i GTypes.Nom
            in if iNom `elem` hVars hth then
                  let hhf' = hhf { item = GTypes.Nominal "" True
                                          (idToSimpleId i) nullRange }
                      -- TODO: should variables always be top?
                  in return (hhf', hhf')
                 else if i `elem` (GTypes.noms $ hSign hth) then
                         let hhf' = hhf { item = GTypes.Nominal "" False
                                                 (idToSimpleId i) nullRange }
                      -- top layer
                         in return (hhf', hhf')
                       else if i `elem`
                               (GTypes.noms $ GTypes.baseSig $ hSign hth )
                            then let hhf' = hhf { item = GTypes.Base_formula
                                                          (GTypes.Nominal ""
                                                            False
                                                            (idToSimpleId i)
                                                            nullRange)
                                                         nullRange }
                            -- lower layer
                                 in return (hhf', hhf')
                            else do
-- TODO: undeclared nominals are not identified as nominals in isNominalSen!
                             CState.put $
                               hth {anaDiags = (mkDiag Error
                                                "undeclared nominal" i)
                                               : (anaDiags hth) }
                             return (hhf, hhf)
 GTypes.Negation f r -> do
   (af1, af2) <- anaLHFORMULA hasQNominals kVars hlid hhLogic (emptyAnno f)
   let hhf'= hhf { item = GTypes.Negation (item af2) r}
   return (hhf{item = GTypes.Negation (item af1) r}, hhf')
 GTypes.Conjunction fs r -> do
   afs' <- mapM (anaLHFORMULA hasQNominals kVars hlid hhLogic) $
             map emptyAnno fs
   return $ (hhf { item = GTypes.Conjunction (map (item.fst) afs') r},
             hhf { item = GTypes.Conjunction (map (item.snd) afs') r})
 GTypes.Disjunction fs r -> do
   afs' <- mapM (anaLHFORMULA hasQNominals kVars hlid hhLogic) $
             map emptyAnno fs
   return $ (hhf { item = GTypes.Disjunction (map (item.fst) afs') r},
             hhf { item = GTypes.Disjunction (map (item.snd) afs') r})
 GTypes.Implication f1 f2 r -> do
   f1' <- anaLHFORMULA hasQNominals kVars hlid hhLogic $ emptyAnno f1
   f2' <- anaLHFORMULA hasQNominals kVars hlid hhLogic $ emptyAnno f2
   return $ (hhf {item = GTypes.Implication (item $ fst f1')
                                            (item $ fst f2') r},
             hhf {item = GTypes.Implication (item $ snd f1')
                                            (item $ snd f2') r})
 GTypes.Equivalence f1 f2 r -> do
   f1' <- anaLHFORMULA hasQNominals kVars hlid hhLogic $ emptyAnno f1
   f2' <- anaLHFORMULA hasQNominals kVars hlid hhLogic $ emptyAnno f2
   return $ (hhf {item = GTypes.Equivalence (item $ fst f1')
                                            (item $ fst f2') r},
             hhf {item = GTypes.Equivalence (item $ snd f1')
                                            (item $ snd f2') r})
 GTypes.Nominal s b i r ->
  if (s /= language_name hlid) then do
-- if s is hlid, then the nominal has been qualified
-- with the name of the lower level logic
-- TODO: better pass the name of the toplogic and check.
-- Thus one could downcast defaults too...
   hth <- CState.get --TODO: check that if b holds, i must be a variable?
   if ( Set.member (simpleIdToId i) (GTypes.noms $ hSign hth) ) ||
      ( (GTypes.ASymbol $ GTypes.HSymb (simpleIdToId i) GTypes.Nom)
         `elem` (hVars hth))
    then return (hhf, hhf)
    else do
     CState.put $ hth {anaDiags = (mkDiag Error "undeclared nominal" i)
                                  : (anaDiags hth)}
     return (hhf,hhf)
  else anaLHFORMULA hasQNominals kVars hlid hhLogic $
       emptyAnno $
        GTypes.Base_formula (GTypes.Nominal s b i r) nullRange
 GTypes.AtState s i f r ->
  if (s /= language_name hlid) then do
   hth <- CState.get
   if ( Set.member (simpleIdToId i) (GTypes.noms $ hSign hth) ) ||
      ( (GTypes.ASymbol $ GTypes.HSymb (simpleIdToId i) GTypes.Nom)
        `elem` (hVars hth))
           then do
    f' <- anaLHFORMULA hasQNominals kVars hlid hhLogic $ emptyAnno f
    return $ (hhf { item = GTypes.AtState s i (item $ fst f') r},
              hhf { item = GTypes.AtState s i (item $ snd f') r})
           else do
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared nominal" i)
                                 : (anaDiags hth)}
    return (hhf,hhf)
   else do
    let Result diag mhsen = downcastHSen hhLogic f
    case mhsen of
     Nothing -> error $ "could not convert formula " ++ show f ++
                " to lower layer of hybridization:" ++ show diag
     Just hsen ->
      anaLHFORMULA hasQNominals kVars hlid hhLogic $
      emptyAnno $
       GTypes.Base_formula (GTypes.AtState s i hsen r) nullRange
 GTypes.BoxFormula s i f r ->
  if (s /= language_name hlid) then do
   hth <- CState.get
   if (simpleIdToId i) `elem` (Map.keys $ GTypes.mods $ hSign hth)
            then do
    f' <- anaLHFORMULA hasQNominals kVars hlid hhLogic $ emptyAnno f
    return $ (hhf { item = GTypes.BoxFormula s i (item $ fst f') r},
              hhf { item = GTypes.BoxFormula s i (item $ snd f') r})
   else do
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared modality" i)
                                 : (anaDiags hth)}
    return (hhf,hhf)
  else do
    let Result diag mhsen = downcastHSen hhLogic f
    case mhsen of
     Nothing -> error $ "could not convert formula " ++ show f ++
                " to lower layer of hybridization:" ++ show diag
     Just hsen ->
      anaLHFORMULA hasQNominals kVars hlid hhLogic $
       emptyAnno $
         GTypes.Base_formula (GTypes.BoxFormula s i hsen r) nullRange
 GTypes.DiamondFormula s i f r ->
  if (s /= language_name hlid) then do
   hth <- CState.get
   if (simpleIdToId i) `elem` (Map.keys $ GTypes.mods $ hSign hth)
            then do
    f' <- anaLHFORMULA hasQNominals kVars hlid hhLogic $ emptyAnno f
    return $ (hhf { item = GTypes.DiamondFormula s i (item $ fst f') r},
              hhf { item = GTypes.DiamondFormula s i (item $ snd f') r})
   else do
    CState.put $ hth {anaDiags = (mkDiag Error "undeclared modality" i)
                                 : (anaDiags hth)}
    return (hhf,hhf)
  else do
    let Result diag mhsen = downcastHSen hhLogic f
    case mhsen of
     Nothing -> error $ "could not convert formula " ++ show f ++
                " to lower layer of hybridization:" ++ show diag
     Just hsen ->
      anaLHFORMULA hasQNominals kVars hlid hhLogic $
       emptyAnno $
        GTypes.Base_formula (GTypes.DiamondFormula s i hsen r) nullRange
 GTypes.QuantVarsParse q vs f r -> do
  let s = case q of
           GTypes.HUniversal x -> x
           GTypes.HExistential x -> x
  if (s /= language_name hlid) then do
   hth <- CState.get
   if null kVars then do
     CState.put $
       hth {anaDiags = (mkDiag Error
                         "quantification on base symbols not allowed:"
                         (show hhf))
                       : (anaDiags hth)}
     return (hhf, hhf)
   else do
    let Result dsyms mrsyms =
         stat_symb_items hlid (GTypes.baseSig $ hSign hth) vs
    case mrsyms of
     Nothing -> do
       CState.put $ hth {anaDiags = dsyms ++ anaDiags hth}
       return (hhf, hhf)
     Just rsyms -> do
      let msyms = convertRawSyms hlid rsyms
-- TODO: this should be a Result, not a Maybe, so we know which symbols failed
      case msyms of
       Nothing -> do
        CState.put $
          hth {anaDiags = (mkDiag Error
                           "could not convert all raw symbols to symbols"
                           (show rsyms))
                          : anaDiags hth}
        return (hhf, hhf)
       Just syms -> do
        let symsKinds = filter (\x -> not (x `elem` kVars)) $
                        map (extSymKind hlid) syms
        case symsKinds of
         [] -> do
           let (f', _) = CState.runState
                           (anaLHFORMULA hasQNominals kVars
                                        hlid hhLogic $ emptyAnno f) $
                         hth {hVars = hVars hth ++
                                      map GTypes.BaseRawSymbol rsyms }
           --trace ("f' : " ++ show f' ) $
           return $ (hhf{item = GTypes.QuantVars q rsyms (item $ fst f') r},
                      hhf{item = GTypes.QuantVars q rsyms (item $ snd f') r})
         _ -> do -- TODO: better error message!
           let diagKinds =
                map (\k -> mkDiag Error
                            ("quantification not allowed on symbols of kind "
                             ++ k) (show hhf) )
                symsKinds
           CState.put $ hth {anaDiags = diagKinds ++ (anaDiags hth)}
           return (hhf, hhf)
  else do
-- here downcastHSen on f is not enough,
-- we must also downcast the list of variables
-- only GTypes.BaseSymbItems are allowed
    let Result diag mhsen = downcastHSen hhLogic f
    case mhsen of
     Nothing -> error $ "could not convert formula " ++ show f ++
                        " to lower layer of hybridization:" ++ show diag
     Just hsen -> do
       let vs' = map (\x -> case x of
                             GTypes.BaseSymbItems y -> y
                             _ -> error $ "only base symbols allowed" ++
                                          " in lower layer quantification:"
                                           ++ show x )
                     vs
       anaLHFORMULA hasQNominals kVars hlid hhLogic $
         emptyAnno $
          GTypes.Base_formula (GTypes.QuantVarsParse q vs' hsen r) nullRange
 GTypes.QuantVars _ _ _ _ ->
   error $ "Already analyzed sentence:" ++ show hhf
 GTypes.QuantNominals q ns f r -> do
  let s = case q of
           GTypes.HUniversal x -> x
           GTypes.HExistential x -> x
  if (s /= language_name hlid) then do
   if hasQNominals then do
    hth <- CState.get
    let (f',_) = CState.runState
                  (anaLHFORMULA hasQNominals kVars
                                hlid hhLogic $ emptyAnno f) $
                  hth {hVars = hVars hth ++
                               map (\i -> GTypes.ASymbol $
                                          GTypes.HSymb (simpleIdToId i)
                                                       GTypes.Nom)
                                   ns}
    return $ (hhf { item = GTypes.QuantNominals q ns (item $ fst f') r},
              hhf { item = GTypes.QuantNominals q ns (item $ snd f') r})
   else error "the logic does not allow quantification on nominals"
  else do
   let Result diag mhsen = downcastHSen hhLogic f
   case mhsen of
    Nothing -> error $ "could not convert formula " ++ show f ++
                       " to lower layer of hybridization:" ++ show diag
    Just hsen ->
     anaLHFORMULA hasQNominals kVars hlid hhLogic $
      emptyAnno $
        GTypes.Base_formula (GTypes.QuantNominals q ns hsen r) nullRange

------------------------------------
-- parser for double hybridization
------------------------------------

parseHHBasicSpec :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      =>           Bool -- True for eng. notation, False for math. notation
                -> Bool -- admits quantification on nominals
                -> Bool -- admits quantification on symbols of base logic
                -> hlid -- lid for base logic
                -> PrefixMap
                ->  AParser st (GTypes.H_BASIC_SPEC
                                 (GTypes.HFORMULA sen symb_items raw_sym)
                                 (GTypes.H_SYMB_ITEMS sym symb_items)
                                 (GTypes.HRawSymbol sym raw_sym))
parseHHBasicSpec eng hasQNominals kVars hlid pm =
  fmap GTypes.Basic_spec
        (annosParser (parseHHBasicItems eng hasQNominals kVars hlid pm))
  <|> (oBraceT >> cBraceT >> return (GTypes.Basic_spec []))

parseHHBasicItems :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> PrefixMap ->
         AParser st (GTypes.H_BASIC_ITEMS
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.HRawSymbol sym raw_sym))
parseHHBasicItems eng hasQNominals kVars hlid pm =
     parseHHAxItems eng hasQNominals kVars hlid pm
-- if this is not first,
-- the parser for basic items consumes more than it should
  <|>
  do (as, ps) <- keyThenList (nomP eng) simpleId
     return $ GTypes.Nom_decl $ GTypes.Nom_item as ps
  <|>
  do (as, ps) <- keyThenList (modP eng) simpleId
     _c <- colonT
     ni <- getNumber
     let i = read ni :: Int
     return $ GTypes.Mod_decl $ GTypes.Mod_item as i ps

parseHHAxItems :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> PrefixMap ->
         AParser st (GTypes.H_BASIC_ITEMS
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.HRawSymbol sym raw_sym))
parseHHAxItems eng hasQNominals kVars hlid pm = do
       d <- dotT
       (fs, ds) <- (aHHFormula eng hasQNominals kVars hlid pm)
                   `separatedBy` dotT
       (_, an) <- optSemi
       let _ = catRange (d : ds)
           ns = init fs ++ [appendAnno (last fs) an]
       return $ GTypes.Axiom_items ns

-- | parser for annoted formulae
aHHFormula :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> PrefixMap ->
         AParser st (Annoted (GTypes.HFORMULA
                               (GTypes.HFORMULA sen symb_items raw_sym)
                               (GTypes.H_SYMB_ITEMS sym symb_items)
                               (GTypes.HRawSymbol sym raw_sym)))
aHHFormula eng hasQNominals kVars hlid pm =
  allAnnoParser (topHHformula eng hasQNominals kVars hlid pm)

-- | toplevel formula parser
topHHformula :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> PrefixMap ->
         AParser st (GTypes.HFORMULA
                      (GTypes.HFORMULA sen symb_items raw_sym)
                      (GTypes.H_SYMB_ITEMS sym symb_items)
                      (GTypes.HRawSymbol sym raw_sym))
topHHformula eng hasQNominals kVars hlid pm =
 (andOrHHFormula eng hasQNominals kVars hlid pm)
 >>= (optImplHHForm eng hasQNominals kVars hlid pm)

andOrHHFormula :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> PrefixMap ->
         AParser st (GTypes.HFORMULA
                      (GTypes.HFORMULA sen symb_items raw_sym)
                      (GTypes.H_SYMB_ITEMS sym symb_items)
                      (GTypes.HRawSymbol sym raw_sym))
andOrHHFormula eng hasQNominals kVars hlid pm =
 (hhFormula eng hasQNominals kVars hlid pm)
  >>= (optAndOrHH eng hasQNominals kVars hlid pm)

optImplHHForm :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> PrefixMap
      -> GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                         (GTypes.H_SYMB_ITEMS sym symb_items)
                         (GTypes.HRawSymbol sym raw_sym)
      -> AParser st (GTypes.HFORMULA
                      (GTypes.HFORMULA sen symb_items raw_sym)
                      (GTypes.H_SYMB_ITEMS sym symb_items)
                      (GTypes.HRawSymbol sym raw_sym))
optImplHHForm eng hasQNominals kVars hlid pm f = do
      _c <- CFormula.implKey
      (fs, _ps) <- (andOrHHFormula eng hasQNominals kVars hlid pm)
                   `separatedBy` CFormula.implKey
      return $ makeImpl (f : fs)
    <|> do
      c <- asKey equivS
      g <- andOrHHFormula eng hasQNominals kVars hlid pm
      return $ GTypes.Equivalence f g $ tokPos c
    <|> return f

optAndOrHH :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> PrefixMap ->
         GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                         (GTypes.H_SYMB_ITEMS sym symb_items)
                         (GTypes.HRawSymbol sym raw_sym)
      -> AParser st (GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                                     (GTypes.H_SYMB_ITEMS sym symb_items)
                                     (GTypes.HRawSymbol sym raw_sym))
optAndOrHH eng hasQNominals kVars hlid pm f = do
      c <- CFormula.andKey
      (fs, ps) <- (hhFormula eng hasQNominals kVars hlid pm)
                  `separatedBy` CFormula.andKey
      return $ GTypes.Conjunction (f : fs) $ catRange $ c : ps
    <|> do
      c <- CFormula.orKey
      (fs, ps) <- (hhFormula eng hasQNominals kVars hlid pm)
                  `separatedBy` CFormula.orKey
      return $ GTypes.Disjunction (f : fs) $ catRange $ c : ps
    <|> return f

hhFormula :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> PrefixMap ->
         AParser st (GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                                     (GTypes.H_SYMB_ITEMS sym symb_items)
                                     (GTypes.HRawSymbol sym raw_sym))
hhFormula eng hasQNominals kVars hlid pm =
 if eng
 then
   do
      c <- asKey "At state"
      n <- simpleId
      s <- optQual
      _ <- colonT
      f <- topHHformula eng hasQNominals kVars hlid pm
 -- here should be formula without @?
      return $ GTypes.AtState s n f $ tokPos c
 <|>
   do
    c <- asKey notS <|> asKey negS <?> "\"not\""
    f <- hhFormula eng hasQNominals kVars hlid pm --topformula
    return $ GTypes.Negation f $ tokPos c
   <|>
     do
        c1 <- asKey "Through" --lessS
        md <- propId ["sometimes", "always"]
        s <- optQual
        _ <- commaT
        sen <- do
                 c2 <- asKey "sometimes"
                 f <- topHHformula eng hasQNominals kVars hlid pm
                 return $ GTypes.DiamondFormula s md f $ toRange c1 [] c2
               <|> do
                 c2 <- asKey "always"
                 f <- topHHformula eng hasQNominals kVars hlid pm
                 return $ GTypes.BoxFormula s md f $ toRange c1 [] c2
        return sen
 <|>
     parenHHFormula eng hasQNominals kVars hlid pm
 <|>
     do
       (q, p) <- quant
       let s = case q of
                GTypes.HUniversal x ->  x
                GTypes.HExistential x -> x
       if (s /= show hlid) then
        parseQHHFormula eng hasQNominals kVars hlid (q, p) pm
       else do
          let (hasQNominalsBase, kVarsBase) = fromJust $ hyb_params hlid
          case parse_q_formula hlid of
           Nothing -> error "should never happen"
-- TODO: improve error message
           Just qFormParser -> do
            f <- qFormParser eng hasQNominalsBase
                             (not $ null kVarsBase) (q, p) pm
            return $ GTypes.Base_formula f nullRange
 <|>
     do
        let fparser = case parse_prim_formula hlid of
                Nothing ->
                  error $ "no prim formula parser for logic " ++ show hlid
                Just f -> f
        f <- fparser pm
        return $ GTypes.Base_formula f nullRange
        -- this should also catch nominals as terms.
        -- We have to make sure during static analysis that this is reverted!
 <|> do -- qualified symbols are nominals
       nom <- simpleId
       _ <- asKey "::"
       qual <- simpleId
       return $ GTypes.Nominal (show qual) False nom nullRange

 else
   do
      c <- asKey asP
      n <- simpleId
      s <- optQual
      _ <- colonT
      f <- topHHformula eng hasQNominals kVars hlid pm
      return $ GTypes.AtState s n f $ tokPos c
 <|>
   do
    c <- asKey notS <|> asKey negS <?> "\"not\""
    f <- hhFormula eng hasQNominals kVars hlid pm
    return $ GTypes.Negation f $ tokPos c
   <|>
     do
        c1 <- asKey lessS
        md <- propId [greaterS]
        s <- optQual
        c2 <- asKey greaterS
        f <- topHHformula eng hasQNominals kVars hlid pm
        return $ GTypes.DiamondFormula s md f $ toRange c1 [] c2
 <|>
     do
        c1 <- oBracketT
        md <- propId ["]"]
        s <- optQual
        c2 <- cBracketT
        f <- topHHformula eng hasQNominals kVars hlid pm
        return $ GTypes.BoxFormula s md f $ toRange c1 [] c2
 <|>
     parenHHFormula eng hasQNominals kVars hlid pm
 <|>
     do
       (q, p) <- quant
       let s = case q of
                GTypes.HUniversal x -> x
                GTypes.HExistential x -> x
       if (s /= show hlid) then
        parseQHHFormula eng hasQNominals kVars hlid (q, p) pm
       else do
          let (hasQNominalsBase, kVarsBase) = fromJust $ hyb_params hlid
          case parse_q_formula hlid of
           Nothing -> error "should never happen"
 -- TODO: improve error message
           Just qFormParser -> do
            f <- qFormParser eng hasQNominalsBase
                             (not $ null kVarsBase) (q, p) pm
            return $ GTypes.Base_formula f nullRange
 <|>
     do
        let fparser = case parse_prim_formula hlid of
                Nothing ->
                 error $ "no prim formula parser for logic " ++ show hlid
                Just f -> f
        f <- fparser pm
        return $ GTypes.Base_formula f nullRange
        -- this should also catch nominals as terms.
        -- We have to make sure during static analysis that this is reverted!
 <|> do -- qualified symbols are nominals
       nom <- simpleId
       _ <- asKey "::"
       qual <- simpleId
       return $ GTypes.Nominal (show qual) False nom nullRange
  -- Note: always False here, no qualifications for variables

parenHHFormula :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> PrefixMap ->
         AParser st (GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                                     (GTypes.H_SYMB_ITEMS sym symb_items)
                                     (GTypes.HRawSymbol sym raw_sym))
parenHHFormula eng hasQNominals kVars hlid pm = do
       oParenT << addAnnos
       f <- topHHformula eng hasQNominals kVars hlid  pm << addAnnos
       cParenT >> return f

parseQHHFormula :: Logic hlid
                       sublogics'
                       (GTypes.H_BASIC_SPEC sen symb_items raw_sym)
                       (GTypes.HFORMULA sen symb_items raw_sym)
                       (GTypes.H_SYMB_ITEMS sym symb_items)
                       (GTypes.H_SYMB_MAP_ITEMS symb_map_items)
                       (GTypes.HSign sig)
                       (GTypes.HMorphism sig mor)
                       (GTypes.HSymbol sym)
                       (GTypes.HRawSymbol sym raw_sym)
                       proof_tree'
      => Bool -> Bool -> Bool -> hlid -> (GTypes.HQUANT, Token) -> PrefixMap 
      -> AParser st (GTypes.HFORMULA (GTypes.HFORMULA sen symb_items raw_sym)
                                     (GTypes.H_SYMB_ITEMS sym symb_items)
                                     (GTypes.HRawSymbol sym raw_sym))
parseQHHFormula eng hasQNominals kVars hlid (q, p) pm =
  do -- first try quantification on nominals, or the parser will complain
     (vs, _ps) <- keyThenList (nomP eng) simpleId
     _d <- dotT
     f <- topHHformula eng hasQNominals kVars hlid pm
     if hasQNominals then
      return $ GTypes.QuantNominals q vs f nullRange
     else error $ "the logic does not admit quantification on nominals"
    <|>
  do
     let symParser = case parse_symb_items hlid of
                  Nothing ->
                   error $ "no symbol parser for logic " ++ show hlid
                  Just f -> f
     (sitems, ps) <- (symParser pm) `separatedBy` commaT
     d <- dotT
     f <- topHHformula eng hasQNominals kVars hlid pm
     if kVars then
      return $ GTypes.QuantVarsParse q sitems f $ toRange p ps d
     else error $ "the logic does not admit quantification on base symbols"
