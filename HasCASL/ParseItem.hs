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

module HasCASL.ParseItem where

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
hasCaslItemList kw ip constr =
    do p <- pluralKeyword kw
       auxItemList hasCaslStartKeywords [p] ip constr

hasCaslItemAux :: [Token] -> AParser st b
               -> ([Annoted b] -> Range -> a) -> AParser st a
hasCaslItemAux ps = auxItemList hasCaslStartKeywords ps

-- * parsing type items

commaTypeDecl :: TypePattern -> AParser st TypeItem
commaTypeDecl s = do c <- anComma
                     (is, cs) <- typePattern `separatedBy` anComma
                     let l = s : is
                         p = c : cs
                     subTypeDecl (l, p)
                       <|> kindedTypeDecl (l, p)
                       <|> return (TypeDecl l universe $ catPos p)

kindedTypeDecl :: ([TypePattern], [Token]) -> AParser st TypeItem
kindedTypeDecl (l, p) =
    do t <- colT
       s <- kind
       let d = TypeDecl l s $ catPos $ p++[t]
       if isSingle l then
          pseudoTypeDef (head l) (Just s) [t]
                   <|> dataDef (head l) s [t]
                   <|> return d
          else return d

isoDecl :: TypePattern -> AParser st TypeItem
isoDecl s = do e <- equalT
               subTypeDefn (s, e)
                 <|> do (l, p) <- typePattern `separatedBy` equalT
                        return (IsoDecl (s:l) $ catPos $ e:p)

vars :: AParser st Vars
vars = fmap Var var
       <|> do o <- oParenT
              (vs, ps) <- vars `separatedBy` anComma
              c <- cParenT
              return (VarTuple vs $ toPos o ps c)

subTypeDefn :: (TypePattern, Token) -> AParser st TypeItem
subTypeDefn (s, e) = do a <- annos
                        o <- oBraceT
                        v <- vars
                        c <- colT
                        t <- parseType
                        d <- dotT -- or bar
                        f <- term
                        p <- cBraceT
                        return (SubtypeDefn s v t (Annoted f nullRange a [])
                                  (toPos e [o,c,d] p))

subTypeDecl :: ([TypePattern], [Token]) -> AParser st TypeItem
subTypeDecl (l, p) =
    do t <- lessT
       s <- parseType
       return (SubtypeDecl l s $ catPos $ p++[t])

sortItem :: AParser st TypeItem
sortItem = do s <- typePattern
              subTypeDecl ([s],[])
                    <|>
                    kindedTypeDecl ([s],[])
                    <|>
                    commaTypeDecl s
                    <|>
                    isoDecl s
                    <|>
                    return (TypeDecl [s] universe nullRange)

sortItems :: AParser st SigItems
sortItems = hasCaslItemList sortS sortItem (TypeItems Plain)

typeItem :: AParser st TypeItem
typeItem = do s <- typePattern;
              subTypeDecl ([s],[])
                    <|>
                    dataDef s universe []
                    <|>
                    pseudoTypeDef s Nothing []
                    <|>
                    kindedTypeDecl ([s],[])
                    <|>
                    commaTypeDecl s
                    <|>
                    isoDecl s
                    <|>
                    return (TypeDecl [s] universe nullRange)

typeItemList :: [Token] -> Instance -> AParser st SigItems
typeItemList ps k = hasCaslItemAux ps typeItem $ TypeItems k

typeItems :: AParser st SigItems
typeItems = do p <- pluralKeyword typeS
               do    q <- pluralKeyword instanceS
                     typeItemList [p, q] Instance
                 <|> typeItemList [p] Plain

-- | several 'typeArg's
typeArgs :: AParser st ([TypeArg], [Token])
typeArgs =
    do l <- many1 typeArg
       return (map fst l, concatMap snd l)

pseudoType :: AParser st TypeScheme
pseudoType = do l <- asKey lamS
                (ts, pps) <- typeArgs
                d <- dotT
                t <- pseudoType
                let qs = toPos l pps d
                case t of
                       TypeScheme ts1 gt ps ->
                           return $ TypeScheme (ts1++ts) gt (ps `appRange` qs)
             <|> do st <- parseType
                    return $ simpleTypeScheme st

pseudoTypeDef :: TypePattern -> Maybe Kind -> [Token] -> AParser st TypeItem
pseudoTypeDef t k l =
    do c <- asKey assignS
       p <- pseudoType
       return (AliasType t k p $ catPos $ l++[c])

-- * parsing datatypes

component :: AParser st [Component]
component =
    try (do (is, cs) <- uninstOpId `separatedBy` anComma
            compType is cs)
            <|> do t <- parseType
                   return [NoSelector t]


concatFst :: [[a]] -> Range -> ([a], Range)
concatFst as ps = (concat as, ps)

tupleComponent :: AParser st ([Component], Range)
tupleComponent = bracketParser component oParenT cParenT anSemi concatFst

altComponent :: AParser st ([Component], Range)
altComponent =
    tupleComponent
    <|> do i <- typeVar
           return ([NoSelector $ idToType i], nullRange)
        where idToType :: Id -> Type
              idToType (Id [t] [] _) = TypeToken t
              idToType _ = error "idToType"


compType :: [UninstOpId] -> [Token] -> AParser st [Component]
compType is cs = do c <- colT
                    t <- parseType
                    return (makeComps is (cs++[c]) Total t)
                 <|>
                 do c <- qColonT
                    t <- parseType
                    return (makeComps is (cs++[c]) Partial t)
    where makeComps [a] [b] k t = [Selector a k t Other $ tokPos b]
          makeComps (a:r) (b:s) k t =
              Selector a k t Comma (tokPos b) : makeComps r s k t
          makeComps _ _ _ _ = error "makeComps: empty selector list"

alternative :: AParser st Alternative
alternative = do s <- pluralKeyword sortS <|> pluralKeyword typeS
                 (ts, cs) <- parseType `separatedBy` anComma
                 return (Subtype ts $ catPos $ s:cs)
              <|>
              do i <- hconsId
                 cps <- many altComponent
                 let ps = concatMapRange snd cps
                     cs = map fst cps
                 do q <- quMarkT
                    return (Constructor i cs Partial $ ps `appRange` tokPos q)
                   <|> return (Constructor i cs Total ps)

dataDef :: TypePattern -> Kind -> [Token] -> AParser st TypeItem
dataDef t k l =
    do c <- asKey defnS
       a <- annos
       (Annoted v _ _ b:as, ps) <- aAlternative `separatedBy` barT
       let aa = Annoted v nullRange a b:as
           qs = catPos $ l++c:ps
       do d <- asKey derivingS
          (cs, cps) <- classId `separatedBy` anComma
          return (Datatype (DatatypeDecl t k aa cs
                    $ qs `appRange` tokPos d `appRange` catPos cps))
         <|> return (Datatype (DatatypeDecl t k aa [] qs))
    where aAlternative = bind (\ a an -> Annoted a nullRange [] an)
                         alternative annos

dataItem :: AParser st DatatypeDecl
dataItem = do t <- typePattern
              do   c <- colT
                   k <- kind
                   Datatype d <- dataDef t k [c]
                   return d
                <|> do Datatype d <- dataDef t universe []
                       return d

dataItems :: AParser st BasicItem
dataItems = hasCaslItemList typeS dataItem FreeDatatype

-- * parse class items

classDecl :: AParser st ClassDecl
classDecl = do
    (is, cs) <- classId `separatedBy` anComma
    (ps, k) <- option ([], universe) $ bind  (,) (single $ colT <|> lessT) kind
    return $ ClassDecl is k $ catPos $ cs ++ ps

classItem :: AParser st ClassItem
classItem = do c <- classDecl
               do o <- oBraceT
                  is <- annosParser basicItems
                  p <- cBraceT
                  return (ClassItem c is $ toPos o [] p)
                 <|>
                  return (ClassItem c [] nullRange)

classItemList :: [Token] -> Instance -> AParser st BasicItem
classItemList ps k = hasCaslItemAux ps classItem $ ClassItems k

classItems :: AParser st BasicItem
classItems = do p <- (asKey (classS ++ "es") <|> asKey classS) <?> classS
                do   q <- pluralKeyword instanceS
                     classItemList [p, q] Instance
                 <|> classItemList [p] Plain

-- * parse op items

-- | compound lists or instantiation lists are not distinguished
opId :: AParser st OpId
opId = do
    i@(Id _ _ ps) <- uninstOpId
    return $ OpId i [] ps

opAttr :: AParser st OpAttr
opAttr = do a <- asKey assocS
            return (BinOpAttr Assoc $ tokPos a)
         <|>
         do a <- asKey commS
            return (BinOpAttr Comm $ tokPos a)
         <|>
         do a <- asKey idemS
            return (BinOpAttr Idem $ tokPos a)
         <|>
         do a <- asKey unitS
            t <- term
            return (UnitOpAttr t $ tokPos a)

opDecl :: [OpId] -> [Token] -> AParser st OpItem
opDecl os ps = do (c, t) <- partialTypeScheme
                  opAttrs os ps c t
                    <|> return (OpDecl os t [] $ catPos $ ps++[c])

opAttrs :: [OpId] -> [Token] -> Token -> TypeScheme -> AParser st OpItem
opAttrs os ps c t =
    do   d <- anComma
         (attrs, cs) <- opAttr `separatedBy` anComma
         return $ OpDecl os t attrs $ catPos $ ps++[c,d]++cs

opArg :: AParser st ([VarDecl], Range)
opArg = bracketParser varDecls oParenT cParenT anSemi concatFst

opArgs :: AParser st ([[VarDecl]], Range)
opArgs =
    do cps <- many1 opArg
       return (map fst cps, concatMapRange snd cps)

opDeclOrDefn :: OpId -> AParser st OpItem
opDeclOrDefn o =
    do (c, st) <- typeOrTypeScheme
       let t = toPartialTypeScheme st
       opAttrs [o] [] c t
         <|> opTerm o [] nullRange c st
         <|> return (OpDecl [o] t [] $ tokPos c)
    <|>
    do (args, ps) <- opArgs
       (c, st) <- typeOrTotalType
       opTerm o args ps c st

-- | a 'Total' or a 'Partial' function definition type
typeOrTotalType :: AParser st (Token, TypeOrTypeScheme)
typeOrTotalType =
    do c <- colT
       t <- parseType
       return (c, TotalTypeScheme $ simpleTypeScheme t)
   <|>
   do c <- qColonT
      t <- parseType
      return (c, PartialType t)

opTerm :: OpId -> [[VarDecl]] -> Range -> Token
       -> TypeOrTypeScheme -> AParser st OpItem
opTerm o as ps c st =
    do e <- equalT
       f <- term
       let (p, sc) = case st of
                             PartialType t -> (Partial, simpleTypeScheme t)
                             TotalTypeScheme s -> (Total, s)
       return (OpDefn o as sc p f
                     (ps `appRange` toPos c [] e))

opItem :: AParser st OpItem
opItem = do (os, ps) <- opId `separatedBy` anComma
            if isSingle os then
                    opDeclOrDefn (head os)
                    else opDecl os ps

opItems :: AParser st SigItems
opItems = hasCaslItemList opS opItem (OpItems Op)
          <|> hasCaslItemList functS opItem (OpItems Fun)

-- * parse pred items as op items

predDecl :: [OpId] -> [Token] -> AParser st OpItem
predDecl os ps = do c <- colT
                    t <- typeScheme
                    return $ OpDecl os (predTypeScheme t) []
                            $ catPos $ ps++[c]

predDefn :: OpId -> AParser st OpItem
predDefn o = do (args, ps) <- opArg
                e <- asKey equivS
                f <- term
                return $ OpDefn o [args] (simpleTypeScheme unitType)
                        Partial f (ps `appRange` tokPos e)

predItem :: AParser st OpItem
predItem = do (os, ps) <- opId `separatedBy` anComma
              if isSingle os then
                 predDecl os ps
                 <|>
                 predDefn (head os)
                 else predDecl os ps

predItems :: AParser st SigItems
predItems = hasCaslItemList predS predItem (OpItems Pred)


-- * other items

sigItems :: AParser st SigItems
sigItems = sortItems <|> opItems <|> predItems <|> typeItems

generatedItems :: AParser st BasicItem
generatedItems = do g <- asKey generatedS
                    do FreeDatatype ds ps <- dataItems
                       return (GenItems [Annoted (TypeItems Plain
                                   (map (\d -> Annoted
                                                        (Datatype (item d))
                                         nullRange (l_annos d) (r_annos d)) ds) ps)
                                         nullRange [] []]
                                   $ tokPos g)
                      <|>
                      do o <- oBraceT
                         is <- annosParser sigItems
                         c <- cBraceT
                         return (GenItems is
                                   (toPos g [o] c))

genVarItems :: AParser st ([GenVarDecl], [Token])
genVarItems =
           do vs <- genVarDecls
              do s <- try (addAnnos >> Common.Lexer.semiT << addLineAnnos)
                 do tryItemEnd hasCaslStartKeywords
                    return (vs, [s])
                   <|>
                     do (ws, ts) <- genVarItems
                        return (vs++ws, s:ts)
                <|>
                return (vs, [])


freeDatatype, progItems, axiomItems, forallItem, genVarItem, dotFormulae,
  basicItems, internalItems :: AParser st BasicItem

freeDatatype =   do f <- asKey freeS
                    FreeDatatype ds ps <- dataItems
                    return $ FreeDatatype ds (tokPos f `appRange` ps)

progItems = hasCaslItemList programS (patternTermPair [equalS]
                                      (WithIn, []) equalS) ProgItems

axiomItems = hasCaslItemList axiomS term $ AxiomItems []

forallItem =     do f <- forallT
                    (vs, ps) <- genVarDecls `separatedBy` anSemi
                    a <- annos
                    AxiomItems _ ((Annoted ft qs as rs):fs) ds <- dotFormulae
                    let aft = Annoted ft qs (a++as) rs
                    return $ AxiomItems (concat vs) (aft:fs)
                            $ catPos (f:ps) `appRange` ds

genVarItem = do v <- pluralKeyword varS
                (vs, ps) <- genVarItems
                return $ GenVarItems vs $ catPos $ v:ps

dotFormulae = do d <- dotT
                 (fs, ds) <- aFormula `separatedBy` dotT
                 let ps = catPos $ d:ds
                 if null (r_annos(last fs)) then
                   do (m, an) <- optSemi
                      return (AxiomItems []
                               (init fs ++ [appendAnno (last fs) an])
                               (ps `appRange` catPos m))
                   else return (AxiomItems [] fs ps)
    where aFormula = bind appendAnno
                     (annoParser term) lineAnnos

internalItems =
    do i <- asKey internalS
       o <- oBraceT
       is <- annosParser basicItems
       p <- cBraceT
       return (Internal is $ toPos i [o] p)

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
basicSpec = (fmap BasicSpec $ annosParser basicItems)
            <|> (oBraceT >> cBraceT >> return (BasicSpec []))

