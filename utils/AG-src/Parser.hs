{- UU_AG
 - Copyright:  S. Doaitse Swierstra, Arthur I. Baars and Andres Loeh
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT
               the Netherlands
               {swierstra,arthurb,andres}@cs.uu.nl -}
module Parser --(parseAG)
where
import UU_Parsing hiding (Alternative)
import ConcreteSyntax
import CommonTypes
import Patterns
import UU_Pretty(text,PP_Doc,empty,(>-<))
import TokenDef
import List (intersperse)
import Char
import IOExts
import Scanner
import List
import Expression
type AGParser  = AnaParser Input Id (Token Char)


parseAG :: String -> IO (AG,Reports (Token Char))
parseAG  file = do (es,_,reps) <- parseFile file
                   return (AG es, reps)


parseFile :: String -> IO  ([Elem],[String] ,Reports (Token Char))
parseFile file = do txt <- readFile file
                    let litMode = ".lag" `isSuffixOf` file
                        (files,text) = if litMode then scanLit txt
                                       else ([],txt)
                        input        = Input (agScan (initPos file) text)

                        ((es,fls),reports) = parse pElemsFiles input
                        stop (es,fs,reps) = null fs
                        cont (es,fs,reps) = do res <- mapM parseFile fs
                                               let (ess,fss,repss) = unzip3 res
                                               return (concat (es:ess), concat fss,foldr concReps NoMoreReports (reps:repss))
                    loop stop cont (es,files++fls,reports)

concReps r1 r2 = case r1 of
             Insert a b c rs' -> Insert a b c (concReps rs' r2)
             Delete a b c rs' -> Delete a b c (concReps rs' r2)
             NoMoreReports    -> r2

loop ::(a->Bool) -> (a->IO a) -> a ->  IO a
loop pred cont x | pred x = return x
                 | otherwise = do x' <- cont x
                                  loop pred cont x'
pElemsFiles :: AGParser ([Elem],[String])
pElemsFiles = pFoldr (($),([],[])) pElem'
   where pElem' =  addElem <$> pElem
               <|> pINCLUDE *> (addInc <$> pStrLit `opt` id)
         addElem e      (es,fs) = (e:es,   fs)
         addInc  (fn,_) (es,fs) = (  es,fn:fs)

pCodescrapL = (\tok -> (code tok,loc tok))<$>
            parseScrapL  <?> "a code block"

parseScrapL :: AGParser (Token Char)
parseScrapL = let fi  = EOr []
                  len = Succ (Zero)
                  p   = P (\k (Input inp) ->
                            let (sc,rest) = case inp of
                                  ((t@(Codescrap _ _),_):rs) -> (t,rs)

                                  _ -> let (p1,inp1) = case inp of
                                             ((_,(p1,inp1)):_) -> (p1,inp1)
                                             _                  -> (noPos,[])
                                           (tok,p2,inp2) = codescrapL p1 inp1
                                       in (tok, agScan p2 inp2)
                                ( ~(result, msgs), st)   = k (Input rest)
                            in  ((acceptR sc result , msgs), Ok st)
                       )
              in anaDynN  fi len p

codescrapL p []                 = (Codescrap [] p,p,[])
codescrapL p (x:xs) | isSpace x = (updPos'  x p)  codescrapL xs
                    | otherwise = let refcol = column p
                                      (p',sc,rest) = scrapL refcol p  (x:xs)
                                  in (Codescrap sc p,p',rest)

scrapL ref p (x:xs) | isSpace x || column p >= ref =
                          let (p'',sc,inp) = updPos'  x p (scrapL ref)  xs
                          in  (p'',x:sc,inp)
                    | otherwise       =(p,[],x:xs)
scrapL ref p []     = (p,[],[])

pParens, pBrackets :: AGParser a -> AGParser a
pParens   p = pPacked pOParens pCParens p
pBrackets p = pPacked pOBrack  pCBrack  p

pAG  :: AGParser AG
pAG  = AG <$> pElems

pElems :: AGParser Elems
pElems = pList_ng pElem

pElem :: AGParser Elem
pElem =  Data <$> pDATA
              <*> pConid'
              <*> pOptAttrs
              <*> pAlts
             <*> pSucceed False
     <|> Attr <$> pATTR
              <*> pList1 pConid'
              <*> pAttrs
     <|> Type <$> pTYPE
              <*> pConid'
              <*  pEquals
              <*> pBrackets pType
     <|> Sem  <$> pSEM
              <*> pConid'
              <*> pOptAttrs
              <*> pSemAlts
     <|> codeBlock <$> (pVarid' <|> pSucceed "") <*> pCodeBlock <?> "a statement"
           where codeBlock nm (txt,pos) = Txt pos nm (lines txt)

-- Insertion is expensive for pCodeBlock in order to prevent infinite inserts.
pCodeBlock ::  AGParser (String,Pos)
pCodeBlock   = (\tok -> (code tok,loc tok)) <$>
               pCostSym' 90 (Codescrap [] noPos) <?> "a code block"


pAttrs :: AGParser Attrs
pAttrs = Attrs <$> pOBrack <*> (concat <$> pList pInhAttrNames <?> "inherited attribute declarations")
                           <* pBar    <*> (concat <$> pList pAttrNames <?> "chained attribute declarations"  )
                           <* pBar    <*> (concat <$> pList pAttrNames <?> "synthesised attribute declarations"  )
                           <* pCBrack

pOptAttrs :: AGParser Attrs
pOptAttrs = pAttrs `opt` Attrs noPos [] [] []

pType :: AGParser String
pType =  pConid'
     <|> pCodescrap'  <?> "a type"


pInhAttrNames :: AGParser AttrNames
pInhAttrNames   = (\vs tp -> map (\v -> (v,tp,("",""))) vs)
                  <$> pVarids <*  pColon <*> pType <?> "attribute declarations"

pVarids :: AGParser [String]
pVarids         = pList1Sep pComma pVarid' <?> "lowercase identifiers"


pAttrNames :: AGParser AttrNames
pAttrNames = (\vs use tp -> map (\v -> (v,tp,use)) vs)
             <$> pVarids <*> pUse <* pColon <*> pType <?> "attribute declarations"

pUse :: AGParser (String,String)
pUse = ((,) <$ pUSE <*> pCodescrap'  <*> pCodescrap')` opt` ("","") <?> "USE declaration"

pAlt :: AGParser Alt
pAlt =  Alt <$> pBar <*> pConid' <*> pFields <?> "a datatype alternative"

pAlts :: AGParser Alts
pAlts =  pList_ng pAlt <?> "datatype alternatives"

pFields    :: AGParser Fields
pFields    = concat <$> pList_ng pField <?> "fields"

pField     :: AGParser Fields
pField     =  (\nms tp -> map (flip (,) tp) nms)
           <$> pVarids <* pColon <*> pType
           <|> (\s -> [(mklower s,s)]) <$> pConid'

mklower :: String -> String
mklower (x:xs) = toLower x : xs

pSemAlt :: AGParser SemAlt
pSemAlt  = SemAlt
          <$> pBar <*> pConid' <*> pSemDefs <?> "SEM alternative"

pSemAlts :: AGParser SemAlts
pSemAlts =  pList1 pSemAlt <?> "SEM alternatives"

pSemDefs :: AGParser SemDefs
pSemDefs =  concat <$> pList_ng pSemDef  <?> "attribute rules"

pSemDef :: AGParser [SemDef]
pSemDef =  pVarid <**>  pAttrDefs
       <|> pLOC <**>  pLocDefs

pExpr :: AGParser Expression
pExpr = (\(str,pos) ->  Expression pos str) <$> ( pCodescrapL  ) <?> "an expression"

pAssign :: AGParser Bool
pAssign =  False <$ pSym (Equals noPos)
       <|> True  <$ pSym (ColonEquals noPos)

pAttrDefs :: AGParser ((String,Pos) -> [SemDef])
pAttrDefs = (\fs field -> map ($field) fs) <$> pList1 pAttrDef  <?> "attribute definitions"

pAttrDef :: AGParser ((String,Pos) -> SemDef)
pAttrDef = (\v owrt e (f,p) -> Def p f v e owrt)
           <$ pDot <*> pVarid' <*> pAssign <*> pExpr

pLocDefs :: AGParser (Pos ->[SemDef])
pLocDefs = (\fs pos -> map ($pos) fs)
        <$> pList1 pLocDef
        <?> "local definitions"

pLocDef :: AGParser  (Pos -> SemDef)
pLocDef = (\p owrt e pos -> LocDef pos p e owrt)
          <$ pDot <*> pPattern <*> pAssign <*> pExpr

pPattern :: AGParser Pattern
pPattern =  (\ (v,p) f -> f p v) <$> pVarid <*> (((\pat p v -> Alias p v pat) <$ pAt <*> pPattern) `opt` Var )
        <|> (mkTuple <$> pOParens <*> pListSep pComma pComplexPattern <* pCParens )
        <|> Underscore <$> pUScore <?> "a pattern"
  where mkTuple _ [x] = x
        mkTuple p xs  = Product p xs


pComplexPattern :: AGParser Pattern
pComplexPattern =  (\(i,p) -> Constr p i)
               <$> pConid <*> pList  pPattern
               <|> pPattern <?> "a pattern"

pVarid' , pConid' :: AGParser String
pVarid'     = fst <$> pVarid
pConid'     = fst <$> pConid

pCostSym'' :: Int -> Token Char -> AGParser Pos
pCostSym'' c s = loc <$> pCostSym' c s


pTkError     :: AGParser (Token Char)
pTkError     = pCostSym' 10000 (TkError  "<message>"   noPos) <?> ""
  -- never insert an error

pCostSym' c t = pCostSym c t t

pCodescrap' ::  AGParser String
pCodescrap' = fst <$> pCodescrap

pCodescrap ::  AGParser (String,Pos)
pCodescrap   = (\tok -> (code tok,loc tok)) <$>
               pCostSym' 90 (Codescrap []             noPos) <?> "a code block"
pVarid, pConid, pStrLit :: AGParser (String,Pos)
pVarid       = (\tok -> (varid tok,loc tok))
            <$> pCostSym' 5 (Varid     "<identifier>" noPos)  <?> "a lowercase identifier"

pConid       = (\tok -> (conid tok,loc tok))
            <$> pCostSym' 5 (Conid     "<Identifier>" noPos) <?> "an uppercase identifier"
pStrLit     = (\tok -> (string tok,loc tok))
            <$> pCostSym' 5 (StrLit "<String>" noPos) <?> "a string literal"


pSEM, pATTR, pDATA, pUSE, pLOC,pINCLUDE, pTYPE, pEquals, pColonEquals,
      pOBrack, pCBrack, pOParens, pCParens, pBar, pColon, pComma,
      pDot, pUScore, pEXT,pAt,pOBrace,pCBrace
      :: AGParser  Pos
pDATA        = pCostSym'' 90 (DATA        noPos) <?> "DATA"
pEXT         = pCostSym'' 90 (EXT         noPos) <?> "EXT"
pATTR        = pCostSym'' 90 (ATTR        noPos) <?> "ATTR"
pSEM         = pCostSym'' 90 (SEM         noPos) <?> "SEM"
pINCLUDE     = pCostSym'' 90 (INCLUDE     noPos) <?> "INCLUDE"
pTYPE        = pCostSym'' 90 (TYPE        noPos) <?> "TYPE"
pUSE         = pCostSym'' 5  (USE         noPos) <?> "USE"
pLOC         = pCostSym'' 5  (LOC         noPos) <?> "loc"
pAt          = pCostSym'' 5  (At          noPos) <?> "@"
pDot         = pCostSym'' 5  (Dot         noPos) <?> "."
pComma       = pCostSym'' 5  (Comma       noPos) <?> ","
pUScore      = pCostSym'' 5  (UScore      noPos) <?> "_"
pOBrack      = pCostSym'' 5  (OBrack      noPos) <?> "["
pCBrack      = pCostSym'' 5  (CBrack      noPos) <?> "]"
pOParens     = pCostSym'' 5  (OParens     noPos) <?> "("
pCParens     = pCostSym'' 5  (CParens     noPos) <?> ")"
pOBrace      = pCostSym'' 5  (OBrace      noPos) <?> "{"
pCBrace      = pCostSym'' 5  (CBrace      noPos) <?> "}"
pColon       = pCostSym'' 5  (Colon       noPos) <?> ":"
pEquals      = pCostSym'' 5  (Equals      noPos) <?> "="
pColonEquals = pCostSym'' 5  (ColonEquals noPos) <?> ":="
pBar         = pCostSym'' 5  (Bar         noPos) <?> "|"
