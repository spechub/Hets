{- UU_AG
 - Copyright:  S. Doaitse Swierstra and Arthur I. Baars
               Department of Computer Science
               Utrecht University
               P.O. Box 80.089
               3508 TB UTRECHT
               the Netherlands
               {swierstra,arthurb}@cs.uu.nl -}
module UU_AG_Parser (parseAG) where
import UU_Parsing
import UU_AG_Transform
import UU_Pretty(text,PP_Doc,empty,(>-<))
import UU_AG_TokenDef
import List (intersperse)
import Char
import IOExts
import UU_AG_Scanner

parseAG ::  [Token Char] -> (T_AG,Reports (Token Char))
parseAG     =  parse pAG

type AGParser a = Parser (Token Char) a

pAG  :: AGParser T_AG
pAG  = sem_AG_AG <$> pElems

pElems :: AGParser T_Elems
pElems = pFoldr_ng (($),sem_Elems_Nil)
         (    sem_Elems_Cons <$> pElem
         <|> (\fn -> sem_Elems_Append (include fn))
               <$ pINCLUDE <*> pConid'
         )

include :: String -> T_Elems
include fn = unsafePerformIO $
             do { tks <- catch (scanFile (fn++".ag"))
                               (const (do {putStrLn $ "file not found: " ++ fn++".ag" ;return []}))
                ; let (res,errs) = parse pElems  tks
                ; putStr . show $ errs
                ; return res
                }
pElem :: AGParser T_Elem
pElem =  sem_Elem_Data <$  pDATA
                       <*> pConid'
                       <*> pOptAttrs
                       <*> pAlts
                       <*> pSucceed False
     <|> sem_Elem_Attr <$  pATTR
                       <*> pList pConid'
                       <*> pAttrs
     <|> sem_Elem_Sem  <$  pSEM
                       <*> pConid'
                       <*> pOptAttrs
                       <*> pSemAlts
     <|> (\name block -> sem_Elem_Txt name [block])
                       <$> (pVarid' <|> pSucceed "") <*> pCodescrap'


pAttrs :: AGParser T_Attrs
pAttrs = sem_Attrs_Attrs <$ pOBrack <*> (concat <$> pList pInhAttrNames)
                         <* pBar    <*> (concat <$> pList pAttrNames   )
                         <* pBar    <*> (concat <$> pList pAttrNames   )
                         <* pCBrack

pOptAttrs :: AGParser T_Attrs
pOptAttrs = pAttrs `opt` sem_Attrs_Attrs [] [] []

pType :: AGParser String
pType =  pConid'
     <|> pCodescrap'

pInhAttrNames :: AGParser AttrNames
pInhAttrNames   = (\vs tp -> map (\v -> (v,tp,("",""))) vs)
                  <$> pVarids <*  pColon <*> pType

pVarids :: AGParser [String]
pVarids         = pListSep pComma pVarid'


pAttrNames :: AGParser AttrNames
pAttrNames = (\vs use tp -> map (\v -> (v,tp,use)) vs)
             <$> pVarids <*> pUse <* pColon <*> pType

pUse :: AGParser (String,String)
pUse = ((,) <$ pUSE <*> pCodescrap'  <*> pCodescrap')` opt` ("","")

pAlt :: AGParser T_Alt
pAlt = sem_Alt_Alt <$ pBar <*> pConid' <*> pFields

pAlts :: AGParser T_Alt
pAlts =  (foldr sem_Alts_Cons sem_Alts_Nil ) <$> pList_ng pAlt

pFields    :: AGParser Fields
pFields    = concat <$> pList_ng pField

pField     :: AGParser Fields
pField     =  (\nms tp -> map (flip (,) tp) nms)
           <$> pVarids <* pColon <*> pType
           <|> (\s -> [(mklower s,s)]) <$> pConid'

mklower :: String -> String
mklower (x:xs) = toLower x : xs

pSemAlt :: AGParser T_SemAlt
pSemAlt  = sem_SemAlt_SemAlt
          <$ pBar <*> pConid' <*> pSemDefs

pSemAlts :: AGParser T_SemAlts
pSemAlts =  (foldr sem_SemAlts_Cons sem_SemAlts_Nil ) <$> pList pSemAlt

pSemDefs :: AGParser T_SemDefs
pSemDefs =  (foldr sem_SemDefs_Cons sem_SemDefs_Nil .concat) <$> pList_ng pSemDef

pSemDef :: AGParser [T_SemDef]
pSemDef =  (pVarid' <|> "LHS" <$ pLHS) <**>  pAttrDefs
       <|> pLOC *>  pLocDefs

pExpr :: AGParser PP_Doc
pExpr = (normalizeCode) <$> pCodescrap

pAssign :: AGParser Bool
pAssign =  False <$ pEquals
       <|> True  <$ pColonEquals

pAttrDefs :: AGParser (String -> [T_SemDef])
pAttrDefs = (\fs field -> map ($field) fs) <$> pList1 pAttrDef

pAttrDef :: AGParser (String -> T_SemDef)
pAttrDef = (\v owrt e f -> sem_SemDef_Def f v e owrt)
           <$ pTilde <*> pVarid' <*> pAssign <*> pExpr

pLocDefs :: AGParser [T_SemDef]
pLocDefs = pList1 pLocDef

pLocDef :: AGParser T_SemDef
pLocDef = (\p owrt e -> sem_SemDef_LocDef p e owrt)
          <$ pTilde <*> pPattern <*> pAssign <*> pExpr

pPattern :: AGParser T_Pat
pPattern =  pVarid' <**> ((flip sem_Pat_At <$ pAt <*> pPattern) `opt` sem_Pat_Var )
        <|> pParens ( mkTuple <$> pListSep pComma pComplexPattern )
        <|> sem_Pat_Underscore <$ pUScore
  where mkTuple [x] = x
        mkTuple xs  = sem_Pat_Product $ foldr sem_Pats_Cons sem_Pats_Nil xs


pParens :: AGParser a -> AGParser a
pParens p = pPacked pOParens pCParens p

pComplexPattern :: AGParser T_Pat
pComplexPattern =  sem_Pat_Constr
               <$> pConid' <*> (pFoldr (sem_Pats_Cons,sem_Pats_Nil) pPattern)
               <|> pPattern

pVarid' , pConid' , pCodescrap' :: AGParser String
pVarid'     = fst <$> pVarid
pConid'     = fst <$> pConid
pCodescrap' = fst <$> pCodescrap

normalizeCode :: (String,Pos) -> PP_Doc
normalizeCode (code,loc) = foldr (>-<) empty
                         . map text
                         . cutSpaces
                         . map removeTabs
                         . addspaces
                         . filter (not.allSpace)
                         . lines
                         . replace '~' '_'
                         $ code
    where allSpace = and . map isSpace
          addspaces []     = []
          addspaces (x:xs) = (replicate (column loc -1) ' ' ++ x) : xs
          cutSpaces xs     = let n = minimum (map (length . takeWhile (' '==)) xs)
                             in map (drop n) xs
          removeTabs xs    = foldr handleTab (const "") xs 1
          handleTab x r    = \col -> case x of
                                      '\t' -> let w= 8 - ((col-1) `mod` 8)
                                              in replicate w ' ' ++  r (col+w)
                                      _    -> x : (col `seq` r (col+1))

replace x y xs = map f xs
  where f a | a==x      = y
            | otherwise = a