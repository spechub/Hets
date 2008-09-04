{- |
Module      :  $Header$
Description :  parser for HasCASL basic Items
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

parser for HasCASL basic Items
-}

module HasCASL.ParseItem (basicItems, basicSpec) where

import Text.ParserCombinators.Parsec

import Common.AS_Annotation
import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token

import HasCASL.HToken
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.ParseTerm

-- * adapted item list parser (using 'itemAux')

hasCaslItemList :: String -> AParser st b
                -> ([Annoted b] -> Range -> a) -> AParser st a
hasCaslItemList kw ip constr = do
    p <- pluralKeyword kw
    auxItemList hasCaslStartKeywords [p] ip constr

hasCaslItemAux :: [Token] -> AParser st b -> ([Annoted b] -> Range -> a)
               -> AParser st a
hasCaslItemAux ps = auxItemList hasCaslStartKeywords ps

-- * parsing type items

commaTypeDecl :: TypePattern -> AParser st TypeItem
commaTypeDecl s = do
    c <- anComma
    (is, cs) <- typePattern `separatedBy` anComma
    let l = s : is
        p = c : cs
    subTypeDecl (l, p) <|> kindedTypeDecl (l, p)
        <|> return (TypeDecl l universe $ catRange p)

kindedTypeDecl :: ([TypePattern], [Token]) -> AParser st TypeItem
kindedTypeDecl (l, p) = do
    t <- colT
    s <- kind
    let d = TypeDecl l s $ catRange $ p ++ [t]
    case l of
      [hd] -> pseudoTypeDef hd (Just s) [t] <|> dataDef hd s [t] <|> return d
      _ -> return d

isoDecl :: TypePattern -> AParser st TypeItem
isoDecl s = do
    e <- equalT
    subTypeDefn (s, e) <|> do
        (l, p) <- typePattern `separatedBy` equalT
        return $ IsoDecl (s : l) $ catRange $ e : p

vars :: AParser st Vars
vars = fmap Var var <|> do
    o <- oParenT
    (vs, ps) <- vars `separatedBy` anComma
    c <- cParenT
    return $ VarTuple vs $ toRange o ps c

subTypeDefn :: (TypePattern, Token) -> AParser st TypeItem
subTypeDefn (s, e) = do
    a <- annos
    o <- oBraceT
    v <- vars
    c <- colT
    t <- parseType
    d <- dotT -- or bar
    f <- term
    p <- cBraceT
    let qs = toRange e [o,c,d] p
    return $ SubtypeDefn s v t (Annoted f qs a []) qs

subTypeDecl :: ([TypePattern], [Token]) -> AParser st TypeItem
subTypeDecl (l, p) = do
    t <- lessT
    s <- parseType
    return $ SubtypeDecl l s $ catRange $ p ++ [t]

sortItem :: AParser st TypeItem
sortItem = do
    s <- typePattern
    subTypeDecl ([s],[])
        <|> kindedTypeDecl ([s],[])
        <|> commaTypeDecl s
        <|> isoDecl s
        <|> return (TypeDecl [s] universe nullRange)

sortItems :: AParser st SigItems
sortItems = hasCaslItemList sortS sortItem (TypeItems Plain)

typeItem :: AParser st TypeItem
typeItem = do
    s <- typePattern;
    subTypeDecl ([s],[])
        <|> dataDef s universe []
        <|> pseudoTypeDef s Nothing []
        <|> kindedTypeDecl ([s],[])
        <|> commaTypeDecl s
        <|> isoDecl s
        <|> return (TypeDecl [s] universe nullRange)

typeItemList :: [Token] -> Instance -> AParser st SigItems
typeItemList ps k = hasCaslItemAux ps typeItem $ TypeItems k

typeItems :: AParser st SigItems
typeItems = do
    p <- pluralKeyword typeS
    do  q <- pluralKeyword instanceS
        typeItemList [p, q] Instance
      <|> typeItemList [p] Plain

-- | several 'typeArg's
typeArgs :: AParser st ([TypeArg], [Token])
typeArgs = do
    l <- many1 typeArg
    return (map fst l, concatMap snd l)

pseudoType :: AParser st TypeScheme
pseudoType = do
    l <- asKey lamS
    (ts, pps) <- typeArgs
    d <- dotT
    t <- pseudoType
    let qs = toRange l pps d
    case t of
      TypeScheme ts1 gt ps ->
          return $ TypeScheme (ts ++ ts1) gt $ appRange qs ps
  <|> do
    st <- parseType
    return $ simpleTypeScheme st

pseudoTypeDef :: TypePattern -> Maybe Kind -> [Token] -> AParser st TypeItem
pseudoTypeDef t k l = do
    c <- asKey assignS
    p <- pseudoType
    return $ AliasType t k p $ catRange $ l ++ [c]

-- * parsing datatypes

component :: AParser st [Component]
component = try (do
    (is, cs) <- opId `separatedBy` anComma
    compType is cs) <|> do
    t <- parseType
    return [NoSelector t]

concatFst :: [[a]] -> Range -> ([a], Range)
concatFst as ps = (concat as, ps)

tupleComponent :: AParser st ([Component], Range)
tupleComponent = bracketParser component oParenT cParenT anSemi concatFst

altComponent :: AParser st ([Component], Range)
altComponent = tupleComponent <|> do
    i <- typeVar
    let t = case i of
          Id [tok] [] _ -> TypeToken tok
          _ -> error "altComponent"
    return ([NoSelector t], nullRange)

compType :: [Id] -> [Token] -> AParser st [Component]
compType is cs = do
    c <- colonST
    t <- parseType
    let makeComps l1 l2 = case (l1, l2) of
          ([a], [b]) -> [Selector a Total t Other $ tokPos b]
          (a : r, b : s) -> Selector a Total t Comma (tokPos b) : makeComps r s
          _ -> error "makeComps: empty selector list"
    return $ makeComps is $ cs ++ [c]

alternative :: AParser st Alternative
alternative = do
    s <- pluralKeyword sortS <|> pluralKeyword typeS
    (ts, cs) <- parseType `separatedBy` anComma
    return $ Subtype ts $ catRange $ s : cs
  <|> do
    i <- hconsId
    cps <- many altComponent
    let ps = concatMapRange snd cps
        cs = map fst cps
    do  q <- quMarkT
        return $ Constructor i cs Partial $ appRange ps $ tokPos q
      <|> return (Constructor i cs Total ps)

dataDef :: TypePattern -> Kind -> [Token] -> AParser st TypeItem
dataDef t k l = do
    c <- asKey defnS
    a <- annos
    let aAlternative = bind (\ i an -> Annoted i nullRange [] an)
          alternative annos
    (Annoted v _ _ b : as, ps) <- aAlternative `separatedBy` barT
    let aa = Annoted v nullRange a b : as
        qs = catRange $ l ++ c : ps
    do  d <- asKey derivingS
        (cs, cps) <- classId `separatedBy` anComma
        return $ Datatype $ DatatypeDecl t k aa cs
                    $ appRange qs $ appRange (tokPos d) $ catRange cps
      <|> return (Datatype (DatatypeDecl t k aa [] qs))

dataItem :: AParser st DatatypeDecl
dataItem = do
     t <- typePattern
     do  c <- colT
         k <- kind
         Datatype d <- dataDef t k [c]
         return d
       <|> do
         Datatype d <- dataDef t universe []
         return d

dataItems :: AParser st BasicItem
dataItems = hasCaslItemList typeS dataItem FreeDatatype

-- * parse class items

classDecl :: AParser st ClassDecl
classDecl = do
    (is, cs) <- classId `separatedBy` anComma
    (ps, k) <- option ([], universe) $ bind  (,) (single lessT) kind
    return $ ClassDecl is k $ catRange $ cs ++ ps

classItem :: AParser st ClassItem
classItem = do
    c <- classDecl
    do  o <- oBraceT
        is <- annosParser basicItems
        p <- cBraceT
        return $ ClassItem c is $ toRange o [] p
      <|> return (ClassItem c [] nullRange)

classItemList :: [Token] -> Instance -> AParser st BasicItem
classItemList ps k = hasCaslItemAux ps classItem $ ClassItems k

classItems :: AParser st BasicItem
classItems = do
    p <- asKey (classS ++ "es") <|> asKey classS <?> classS
    do  q <- pluralKeyword instanceS
        classItemList [p, q] Instance
      <|> classItemList [p] Plain

-- * parse op items

opAttr :: AParser st OpAttr
opAttr = let l = [Assoc, Comm, Idem] in
    choice (map ( \ a -> do
      b <- asKey $ show a
      return $ BinOpAttr a $ tokPos b) l)
    <|> do
    a <- asKey unitS
    t <- term
    return $ UnitOpAttr t $ tokPos a

multiTypeScheme :: [PolyId] -> AParser st TypeScheme
multiTypeScheme os = case os of
    p : r -> if null r || all ( \ (PolyId _ tys _) -> null tys) os
      then typeScheme p
      else fail $ "instantiation list in identifier list: "
               ++ show (map ( \ (PolyId i _ _) -> i) os)
    _ -> error "HasCASL.ParseItem.opDecl"

opDecl :: [PolyId] -> [Token] -> AParser st OpItem
opDecl os ps = do
    c <- colonST
    t <- multiTypeScheme os
    opAttrs os ps c t <|> return (OpDecl os t [] $ catRange $ ps ++ [c])

opAttrs :: [PolyId] -> [Token] -> Token -> TypeScheme -> AParser st OpItem
opAttrs os ps c t = do
    d <- anComma
    (attrs, cs) <- opAttr `separatedBy` anComma
    return $ OpDecl os t attrs $ catRange $ ps ++ [c, d] ++ cs

opArg :: AParser st ([VarDecl], Range)
opArg = bracketParser varDecls oParenT cParenT anSemi concatFst

opArgs :: AParser st ([[VarDecl]], Range)
opArgs = do
    cps <- many1 opArg
    return (map fst cps, concatMapRange snd cps)

opDeclOrDefn :: PolyId -> AParser st OpItem
opDeclOrDefn o = do
    c <- colonST
    t <- typeScheme o
    opAttrs [o] [] c t <|> opTerm o [] nullRange c t
        <|> return (OpDecl [o] t [] $ tokPos c)
  <|> do
    (args, ps) <- opArgs
    c <- colonST
    t <- fmap simpleTypeScheme parseType
    opTerm o args ps c t

opTerm :: PolyId -> [[VarDecl]] -> Range -> Token -> TypeScheme
       -> AParser st OpItem
opTerm o as ps c sc = do
    e <- equalT
    f <- term
    return $ OpDefn o as sc f $ appRange ps $ toRange c [] e

opItem :: AParser st OpItem
opItem = do
    (os, ps) <- parsePolyId `separatedBy` anComma
    case os of
      [hd] -> opDeclOrDefn hd
      _ -> opDecl os ps

opItems :: AParser st SigItems
opItems = hasCaslItemList opS opItem (OpItems Op)
    <|> hasCaslItemList functS opItem (OpItems Fun)

-- * parse pred items as op items

predDecl :: [PolyId] -> [Token] -> AParser st OpItem
predDecl os ps = do
    c <- colT
    t <- multiTypeScheme os
    let p = catRange $ ps ++ [c]
    return $ OpDecl os (predTypeScheme p t) [] p

predDefn :: PolyId -> AParser st OpItem
predDefn o = do
    (args, ps) <- opArg
    e <- asKey equivS
    f <- term
    let p = appRange ps $ tokPos e
    return $ OpDefn o [args]
        (simpleTypeScheme $ mkLazyType $ unitTypeWithRange p) f p

predItem :: AParser st OpItem
predItem = do
    (os, ps) <- parsePolyId `separatedBy` anComma
    let d = predDecl os ps
    case os of
      [hd] -> d <|> predDefn hd
      _ -> d

predItems :: AParser st SigItems
predItems = hasCaslItemList predS predItem (OpItems Pred)

-- * other items

sigItems :: AParser st SigItems
sigItems = sortItems <|> opItems <|> predItems <|> typeItems

generatedItems :: AParser st BasicItem
generatedItems = do
    g <- asKey generatedS
    do  FreeDatatype ds ps <- dataItems
        return $ GenItems [Annoted (TypeItems Plain (map ( \ d -> Annoted
            (Datatype $ item d) nullRange (l_annos d) (r_annos d)) ds) ps)
                          nullRange [] []] $ tokPos g
      <|> do
        o <- oBraceT
        is <- annosParser sigItems
        c <- cBraceT
        return $ GenItems is $ toRange g [o] c

genVarItems :: AParser st ([GenVarDecl], [Token])
genVarItems = do
    vs <- genVarDecls
    do  s <- try (addAnnos >> Common.Lexer.semiT << addLineAnnos)
        do  tryItemEnd hasCaslStartKeywords
            return (vs, [s])
          <|> do
            (ws, ts) <- genVarItems
            return (vs ++ ws, s : ts)
      <|> return (vs, [])

freeDatatype :: AParser st BasicItem
freeDatatype = do
    f <- asKey freeS
    FreeDatatype ds ps <- dataItems
    return $ FreeDatatype ds $ appRange (tokPos f) ps

progItems :: AParser st BasicItem
progItems = hasCaslItemList programS
    (patternTermPair [equalS] (WithIn, []) equalS) ProgItems

axiomItems :: AParser st BasicItem
axiomItems = hasCaslItemList axiomS term $ AxiomItems []

forallItem :: AParser st BasicItem
forallItem = do
    f <- forallT
    (vs, ps) <- genVarDecls `separatedBy` anSemi
    a <- annos
    AxiomItems _ ((Annoted ft qs as rs):fs) ds <- dotFormulae
    let aft = Annoted ft qs (a ++ as) rs
    return $ AxiomItems (concat vs) (aft : fs) $ appRange (catRange $ f : ps) ds

genVarItem :: AParser st BasicItem
genVarItem = do
    v <- pluralKeyword varS
    (vs, ps) <- genVarItems
    return $ GenVarItems vs $ catRange $ v:ps

dotFormulae :: AParser st BasicItem
dotFormulae = do
    d <- dotT
    let aFormula = bind appendAnno (annoParser term) lineAnnos
    (fs, ds) <- aFormula `separatedBy` dotT
    let ps = catRange $ d : ds
        lst = last fs
    if null $ r_annos lst then do
        (m, an) <- optSemi
        return $ AxiomItems [] (init fs ++ [appendAnno lst an]) $ appRange ps
               $ catRange m
       else return $ AxiomItems [] fs ps

internalItems :: AParser st BasicItem
internalItems = do
    i <- asKey internalS
    o <- oBraceT
    is <- annosParser basicItems
    p <- cBraceT
    return (Internal is $ toRange i [o] p)

basicItems :: AParser st BasicItem
basicItems = fmap SigItems sigItems
    <|> classItems
    <|> progItems
    <|> generatedItems
    <|> freeDatatype
    <|> genVarItem
    <|> forallItem
    <|> dotFormulae
    <|> axiomItems
    <|> internalItems

basicSpec :: AParser st BasicSpec
basicSpec = fmap BasicSpec (annosParser basicItems)
