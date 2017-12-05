module UML.UML2CL where
import qualified Data.Map                   as Map
import           UML.UML
import           UML.UML2CL_preamble


import           CommonLogic.AS_CommonLogic

import           Common.Id                  as Id

import           Data.Char
import           Data.List
import           Data.Maybe
import           UML.Sign
import           UML.Utils




{-
translateModel2Text :: Model -> TEXT
translateModel2Text m = Text (translateModel2Phrases m)  nullRange

translateModel2Phrases :: Model -> [PHRASE]
translateModel2Phrases (ClassModel cm) = preamble ++ (translateClasses (cmClasses cm))
                            ++ (map translateEnumPreamble $ ((Map.elems).cmEnums) cm)
                            ++ (foldl (++) [] $ (map translateComposition compositions))
                            ++ (map translateComPair (pairs compositions))
                            ++ (map translateAssociation (Map.elems $ cmAssociations cm))
                            ++ (foldl (++) [] (map translatePackage (cmPackages cm)))
                            ++  postamble
                where
                    compositions = filter isComposition $ Map.elems $ cmAssociations cm-}

translateSign2Phrases :: UML.Sign.Sign -> [TEXT_META]
translateSign2Phrases sign = (( foldl (++) [] (map (map phrases2TM) preambleSens))
    ++ (map translateEnumPreamble $ filterEnums $ fst $ signClassHier sign)
    ++ (map translateInherit (snd $ signClassHier sign))
    ++ (foldl (++) [] $ map translateAttribute (signAttribute sign))
    ++ (foldl (++) [] $ map translateProcedure (signOperations sign))
    ++ (foldl (++) [] $ map translateComposition (signCompositions sign))
    ++ (map translateComPair (pairs $ signCompositions sign))
    ++ (foldl (++) [] $ map translateAssociation (signAssociations sign))
    ++ (foldl (++) [] $ map translateBinAsso $ filter ((2 ==) . length . snd) (signAssociations sign)))

phrases2TM :: [PHRASE] -> TEXT_META
phrases2TM p = Text_meta { getText = Text p nullRange
                          , textIri = Nothing
                          , nondiscourseNames = Nothing
                          , prefix_map = [] }

phrase2TM :: PHRASE -> TEXT_META
phrase2TM p = phrases2TM [p]

filterEnums :: [ClassEntity] -> [UML.UML.Enum]
filterEnums [] = []
filterEnums ((EN en) : lis) = en : (filterEnums lis)
filterEnums (_ : lis) = filterEnums lis
{-
 (foldl (++) [] $ (map translateCompLabel compositions))
                        ++ (foldl (++) [] $ (map translateAssoLabel (filter (not.isComposition) (Map.elems $ cmAssociations cm))))
            compositions = filter isComposition $ Map.elems $ cmAssociations cm
-}
translateBinAsso :: (String, [(String, Type)]) -> [TEXT_META]
translateBinAsso (n, [(en1, et1), (en2, et2)]) = map fromJust $ filter (not . isNothing) [translateEndCoin n 1 (en1, et1), translateEndCoin n 2 (en2, et2)]
translateBinAsso (_, _) = error "Not a binary association"

translateEndCoin :: String -> Integer -> (String, Type) -> Maybe TEXT_META
translateEndCoin m i (n, et) =
    case umltype et of
        CE ce -> case ce of
                    CL cl -> translateEndCoinCE className attr i m n et cl
                    AC ac -> translateEndCoinCE className attr i m n et $ acClass ac
                    EN _ -> Nothing
                    DT dt -> translateEndCoinCE dtName dtattr i m n et dt 
        _ -> Nothing

translateEndCoinCE :: (a -> String) -> (a -> [Attribute]) -> Integer -> String -> String -> Type -> a -> Maybe TEXT_META
translateEndCoinCE namef attrf i m n et cl = 
  case filter ((n ==) . attrName) (attrf cl) of -- Translate class cl into TEXT_META
    [] -> Nothing
    (_ : _) -> Just $ phrases2TM [Sentence $ Quant_sent Universal [Name o, Name s] (ifSen
        (typeFunction (mkSimpleId $ (namef cl) ++ "." ++ n) [o, s])
        (Atom_sent (Equation (Name_term s) (Funct_term ( Name_term  $ mkSimpleId $ "form:seq2" ++ (map toLower $ translateTargetType et)) [Term_seq $ Funct_term (Name_term $ mkSimpleId $ "form:select" ++ (show i)) [Term_seq $ Name_term o, Term_seq $ Name_term $ mkSimpleId m] nullRange] nullRange)) nullRange)) nullRange]
      where
                      o = mkSimpleId "o"
                      s = mkSimpleId "s"

translateMF2TM :: [Sen] -> TEXT_META
translateMF2TM mfs = Text_meta { getText = Text (fmap Sentence (map translateMult2Sen mfs)) nullRange
    , textIri = Nothing
    , nondiscourseNames = Nothing
    , prefix_map = [] }

translateMult2Sen :: Sen -> SENTENCE
translateMult2Sen mf = case mf of
                NLeqF l (NumAttr (MFAttribute c p (MFType t cp))) -> Quant_sent Universal [Name x, Name y, Name n] (ifSen    (andSen [    typeFunction (mkSimpleId $ c ++ "." ++ p) [x, y],
                                        (typeFunction (mkSimpleId $ "form:" ++ (map toLower $ show t) ++ "-size") [y, n])])
                                (typeFunction (mkSimpleId "buml:leq") [mkSimpleId $ show l, n])) nullRange
                    where
                        [x, y, n] = map mkSimpleId $ generateNames [c, p, cp, annotString t] 3
                NLeqF l (NumAss (MFAssociation a endL) p1) -> Quant_sent Universal (map (\ p -> Name p) xs)
                    (ifSen    (andSen $ (map (\ (x, c) -> typeFunction c [x]) (zip xs cs)) ++
                        [Atom_sent (Atom (Name_term  $ mkSimpleId "form:sequence-size")  [Term_seq $ Funct_term (Name_term  $ mkSimpleId "form:n-select") [Term_seq $ Name_term $ mkSimpleId a, Term_seq $ Name_term $ mkSimpleId $ show i, insertList xs, Term_seq $ Name_term n] nullRange]) nullRange])
                                (typeFunction (mkSimpleId "buml:leq") [mkSimpleId $ show l, n])) nullRange
                    where
                        (n : xs) = map mkSimpleId $ generateNames ([show l, a, p1] ++ (map fst pcs)) $ (length pcs) + 1
                        pcs =  filter (\ (p, _) -> not $ p == p1) endL
                        cs = map (mkSimpleId . fst) pcs
                        i = snd $ head $ filter (\ ((p, _), _) -> p == p1) (zip endL [i0 | i0 <- [1 .. (length endL)]])

                NLeqF l (NumComp (MFComposition m p1 (MFType t1 c1) p2 (MFType t2 c2)) p0) -> Quant_sent Universal [Name x]  (ifSen    (andSen [    (typeFunction (mkSimpleId c3mi) [x]), Atom_sent (Atom (Name_term  $ mkSimpleId $ "form:" ++ (map toLower $ show t3mi) ++ "-size") [Term_seq $ Funct_term (Name_term  $ mkSimpleId $ "form:select" ++ i) [Term_seq $ Name_term x, Term_seq $ Name_term $ mkSimpleId m] nullRange, Term_seq $ Name_term n] ) nullRange])
                                (typeFunction (mkSimpleId "buml:leq") [mkSimpleId $ show l, n])) nullRange
                    where
                        [x, n] = map mkSimpleId $ generateNames [c1, p1, c2, p2, annotString t1, annotString t2, m] 2
                        (c3mi, t3mi, i) = case p0 == p1 of
                                True -> (c2, t2, "1")
                                _ -> (c1, t1, "2")
                                --_ -> error $ "Error! unknown name: " ++ (show pi)
                FLeqN (NumAttr (MFAttribute c p (MFType t cp))) l -> Quant_sent Universal [Name x, Name y, Name n] (ifSen    (andSen [    typeFunction (mkSimpleId $ c ++ "." ++ p) [x, y],
                                        (typeFunction (mkSimpleId $ "form:" ++ (map toLower $ show t) ++ "-size") [y, n])])
                                (typeFunction (mkSimpleId "buml:leq") [n, mkSimpleId $ show l])) nullRange
                    where
                        [x, y, n] = map mkSimpleId $ generateNames [c, p, cp, annotString t] 3


                FLeqN (NumAss (MFAssociation a endL) p0) l -> Quant_sent Universal (map (\ p -> Name p) xs)
                    (ifSen    (andSen $ (map (\ (x, c) -> typeFunction c [x]) (zip xs cs)) ++
                        [Atom_sent (Atom (Name_term  $ mkSimpleId "form:sequence-size")  [Term_seq $ Funct_term (Name_term  $ mkSimpleId "form:n-select") [Term_seq $ Name_term $ mkSimpleId a, Term_seq $ Name_term $ mkSimpleId $ show i, insertList xs, Term_seq $ Name_term n] nullRange]) nullRange])
                                (typeFunction (mkSimpleId "buml:leq") [n, mkSimpleId $ show l])) nullRange
                    where
                        (n : xs) = map mkSimpleId $ generateNames ([show l, a, p0] ++ (map fst pcs)) $ (length pcs) + 1
                        pcs =  filter (\ (p, _) -> not $ p == p0) endL
                        cs = map (mkSimpleId . fst) pcs
                        i = snd $ head $ filter (\ ((p, _), _) -> p == p0) (zip endL [i0 | i0 <- [1 .. (length endL)]])

                FLeqN (NumComp (MFComposition m p1 (MFType t1 c1) p2 (MFType t2 c2)) p0) l -> Quant_sent Universal [Name x]  (ifSen    (andSen [    (typeFunction (mkSimpleId c3mi) [x]),
                                        Atom_sent (Atom (Name_term  $ mkSimpleId $ "form:" ++ (map toLower $ show t3mi) ++ "-size") [Term_seq $ Funct_term (Name_term  $ mkSimpleId $ "form:select" ++ i) [Term_seq $ Name_term x, Term_seq $ Name_term $ mkSimpleId m] nullRange, Term_seq $ Name_term n] ) nullRange])
                                (typeFunction (mkSimpleId "buml:leq") [n, mkSimpleId $ show l])) nullRange
                    where
                        [x, n] = map mkSimpleId $ generateNames [c1, p1, c2, p2, annotString t1, annotString t2, m] 2
                        (c3mi, t3mi, i) = case p0 == p1 of
                                True -> (c2, t2, "1")
                                _ -> (c1, t1, "2")
                                --_ -> error $ "Error! unknown name: " ++ (show pi)


insertList :: [Token] -> TERM_SEQ
insertList [] = Term_seq $ Name_term $ mkSimpleId "form:empty-sequence"
insertList (x : lis) = Term_seq $ Funct_term (Name_term  $ mkSimpleId "form:sequence-insert") [Term_seq $ Name_term x, insertList lis] nullRange

{-translatePackage :: Package -> [PHRASE]
translatePackage pack = (translateClasses (classes pack))
                        ++ (map translateEnumPreamble $ ((Map.elems).packageEnums) pack)
                        ++ (foldl (++) [] $ (map translateComposition compositions))
                        ++ (map translateComPair (pairs compositions))
                        ++ (map translateAssociation (Map.elems $ associations pack))
                    where compositions = filter isComposition $ Map.elems $ associations pack-}

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x : lis) = [(x, y) | y <- (x : lis)] ++ (pairs lis)



translateAssociation :: (String, [(String, Type)]) -> [TEXT_META]
translateAssociation (n, endL)  = [phrases2TM [    Sentence $ typeFunction (mkSimpleId "form:Sequence") [mkSimpleId n],
                                    Sentence $ Quant_sent Universal [Name t] (ifSen (typeFunction (mkSimpleId "form:sequence-member") [t, a]) (Quant_sent Existential (map (\ (x0, _) -> Name x0) endPairs) (andSen $ (map (\ (x0, c) -> typeFunction c [x0]) endPairs) ++ [(Atom_sent (Equation (Name_term t) (x2inserts $ map fst endPairs)) nullRange)]) nullRange)) nullRange]]
            where
                endPairs = zip names (map mkSimpleId endTypes)
                endTypes = map (translateType . snd) endL --(map (translateType.defaultType.endTarget) $ ends as)
                x = head $ filter (\ x0 -> not $ any (isPrefixOf x0) endTypes) allStrings
                t = mkSimpleId "t"
                a = mkSimpleId n
                names = [mkSimpleId $ x ++ (show i) | i <- [1 .. (length $ endL)]]
                allStrings = concatMap (\ s -> map (: s) $ ['a' .. 'z'] ++ ['0' .. '9']) $ "" : allStrings
                x2inserts (x0 : (y : ls)) = Funct_term (Name_term $ mkSimpleId "form:sequence-insert") [Term_seq $ Name_term x0, Term_seq $ (x2inserts (y : ls))] nullRange
                x2inserts [x0] = Funct_term (Name_term $ mkSimpleId "form:sequence-insert") [Term_seq $ Name_term x0, Term_seq $ Name_term $ mkSimpleId "form:empty-sequence"] nullRange
                x2inserts [] = error "empty association"

generateNames :: [String] -> Int -> [String]
generateNames  lis n = [x ++ (show i) | i <- [1 .. n]]
            where
                x = head $ filter (\ x0 -> not $ any (isPrefixOf x0) lis) allStrings
                allStrings = concatMap (\ s -> map (: s) $ ['a' .. 'z'] ++ ['0' .. '9']) $ "" : allStrings

rlookup :: (Ord s) => Map.Map s t -> s -> Maybe t
rlookup m k = Map.lookup k m

{-getCompoRelevants :: Association -> (Token, Token, Token)
getCompoRelevants ass = (mkSimpleId $ translateType $ defaultType  (endTarget origin),
            mkSimpleId $ assoName ass,
            mkSimpleId $ translateType $ defaultType $ endTarget target)
            where
                origin = head $ filter isComposedEnd $ ends ass
                target = case (filter (not.(origin==)) (ends ass)) of
                            (x:lis) -> x
                            [] -> error $ show $ ends ass
                originToken = (translateType $ defaultType (endTarget origin))-}

translateComPair :: (((String, ClassEntity), String, (String, Type)), ((String, ClassEntity), String, (String, Type))) -> TEXT_META
translateComPair ((_, n1, _), (_, n2, _)) = phrases2TM [Sentence $ Quant_sent Universal [Name o, Name op, Name i] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent ( Atom (Name_term $ mkSimpleId "form:sequence-member") [Term_seq $ Funct_term (Name_term $ mkSimpleId "form:pair") [Term_seq $ Name_term o, Term_seq $ Name_term i] nullRange, Term_seq $ Name_term $ m]) nullRange, Atom_sent ( Atom (Name_term $ mkSimpleId "form:sequence-member") [Term_seq $ Funct_term (Name_term $ mkSimpleId "form:pair") [Term_seq $ Name_term op, Term_seq $ Name_term i] nullRange, Term_seq $ Name_term mp]) nullRange] ) nullRange) (equalSen o op)) nullRange) nullRange]
    where    --(c1, m, c2) = getCompoRelevants a1
        --(c1p, mp, c2p) = getCompoRelevants a2
        o = mkSimpleId "o"
        op = mkSimpleId "op"
        i = mkSimpleId "i"
        m = mkSimpleId n1
        mp = mkSimpleId n2


equalSen :: Token -> Token -> SENTENCE
equalSen a b = (Atom_sent (Equation (Name_term a) (Name_term b)) nullRange)


ifSen :: SENTENCE -> SENTENCE -> SENTENCE
ifSen a b = Bool_sent (BinOp Implication a b) nullRange

iffSen :: SENTENCE -> SENTENCE -> SENTENCE
iffSen a b = Bool_sent (BinOp Biconditional a b) nullRange

andSen ::  [SENTENCE] -> SENTENCE
andSen sens = Bool_sent (Junction Conjunction sens) nullRange


translateComposition :: ((String, ClassEntity), String, (String, Type)) -> [TEXT_META]
translateComposition ((on, ot), n, (tn, tt)) = (translateComposition2 (mkSimpleId $ showClassEntityName ot, mkSimpleId n, mkSimpleId $ translateType tt)) ++ (map fromJust $ filter (not . isNothing) [translateEndCoin n 1 (on, defaultType  ot), translateEndCoin n 2 (tn, tt)])

translateComposition2 :: (Token, Token, Token) -> [TEXT_META]
translateComposition2 (c1, m, c2) = [phrases2TM [
    Sentence $ typeFunction (mkSimpleId "form:Sequence") [m],
    Sentence $ Quant_sent Universal [Name p] (Bool_sent (BinOp Implication (typeFunction (mkSimpleId "form:sequence-member") [p, m])  (Bool_sent (Junction Conjunction [typeFunction (mkSimpleId "form:Pair") [p], Atom_sent ( Atom (Name_term c1) [Term_seq $ Funct_term (Name_term $ mkSimpleId "form:first") [Term_seq $ Name_term p] nullRange]) nullRange, Atom_sent ( Atom (Name_term c2) [Term_seq $ Funct_term (Name_term $ mkSimpleId "form:second") [Term_seq $ Name_term p] nullRange]) nullRange] ) nullRange)) nullRange) nullRange]]
    where p = mkSimpleId "p"



{-[    Sentence $ Quant_sent Universal [Name x] (
                        Bool_sent (BinOp Implication (typeFunction origin [x]) (Quant_sent Existential [Name y] (Bool_sent(Junction Conjunction [
                typeFunction comp [x, y],
                typeFunction target [y]
                        ]) nullRange) nullRange)) nullRange) nullRange,

                    Sentence $ Quant_sent Universal [Name x, Name y] (
                        Bool_sent (BinOp Implication (typeFunction comp [x, y])  (Bool_sent(Junction Conjunction [
                typeFunction origin [x],
                typeFunction target [y]
                        ]) nullRange)) nullRange) nullRange,

                    Sentence $ Quant_sent Universal [Name x, Name y, Name z] (
                        Bool_sent (BinOp Implication (Bool_sent(Junction Conjunction [
                typeFunction comp [x, y],
                typeFunction comp [x, z]
                        ]) nullRange) (typeFunction (mkSimpleId "=") [y, z]  )) nullRange) nullRange]
    where     x = mkSimpleId "x"
        y = mkSimpleId "y"
        z = mkSimpleId "z"-}

translateEnumPreamble :: UML.UML.Enum -> TEXT_META
translateEnumPreamble en = phrases2TM [Sentence $ typeFunction (mkSimpleId "enumeration") $ (mkSimpleId $ enumName en) : (map (mkSimpleId . literalName) (enumLiterals en))]

{-translateClasses :: Map.Map UML.UML.Id UML.UML.Class -> [PHRASE]
translateClasses cmap =   foldl (++) [] $ map translateClass (Map.elems cmap)-}

{-translateClass :: ClassEntity -> [PHRASE]
translateClass cl = (translateInherit (CL cl) (super cl)) ++ (foldl (++) [] (map (translateAttribute cl) (attr cl))) ++ (foldl (++) [] (map (translateProcedure cl) (proc cl)))-}


translateInherit :: (ClassEntity, ClassEntity) -> TEXT_META
translateInherit (cl, superc) =  phrases2TM [(Sentence (Quant_sent Universal [Name t]  (Bool_sent (BinOp Implication
                    (typeFunction (mkSimpleId (showClassEntityName cl)) [t])
                    (typeFunction (mkSimpleId (showClassEntityName superc)) [t])) nullRange) nullRange))]
                    where t = mkSimpleId "x"


typeFunction :: Token -> [Token] ->  SENTENCE
typeFunction f l  = Atom_sent (Atom (Name_term f) (map (\ t -> Term_seq $ Name_term t) l)) nullRange

--typeFunction :: Token -> [Token] -> TERM
--typeFunction f l = (Funct_term (Name_term f) (map (\t -> Term_seq (Name_term t)) l) nullRange)

typeFunctionSeq :: Token -> [NAME_OR_SEQMARK]  ->  SENTENCE
typeFunctionSeq f l = Atom_sent (Atom (Name_term f) (map termNOS l)) nullRange

termNOS :: NAME_OR_SEQMARK -> TERM_SEQ
termNOS (Name n) = Term_seq $ Name_term  n
termNOS (SeqMark s) = Seq_marks  s

translateProperty :: Token -> [(Token, Token)] -> SENTENCE -> PHRASE
translateProperty c l sen = Sentence (Quant_sent Universal (map (\ (_, b) -> Name b) l) (Bool_sent (BinOp Implication ((typeFunction c (map snd l))) (sen) ) nullRange) nullRange)

translateAttribute :: (Class, String, Type) -> [TEXT_META]
translateAttribute (cl, n, t) = map phrase2TM $ mem ++ (map (translateProperty attrt l) sens)
            where
                x = mkSimpleId "x"
                y = mkSimpleId "y"
                l = [(c, x), (cp, y)]
                sens = [typeFunction c [x], translateTau m (cp, cptar, y)]
                attrt = mkSimpleId $ (className cl) ++ "." ++ n
                c =  mkSimpleId $ translateType $ defaultType $ CL cl
                cp = mkSimpleId $ translateType t
                cptar = mkSimpleId $ translateTargetType t
                m = (mkSimpleId "m")
                mem = [    --(memberRule attrt l (cp, y) ),
                    leftTotallityRule attrt l (cp, y),
                    rightUniqueRule attrt l (cp, y) (mkSimpleId "z")]

translateTau :: Token -> (Token, Token, Token) -> SENTENCE
translateTau m (c, t, x) = andSen [typeFunction (mkSimpleId $ "form:" ++ (tokStr t)) [x], Quant_sent Universal [Name m] (ifSen (typeFunction (mkSimpleId $ "form:" ++ (map toLower $ tokStr t) ++ "-member") [m, x]) (typeFunction c [m])) nullRange]

translateTuple :: (Token, Token)  -> SENTENCE
translateTuple (c, x) = typeFunction c [x]

{-memberRule :: Token -> [(Token, Token)] -> (Token, Token) -> Token -> PHRASE
memberRule c l (cy, y) m = Sentence (Quant_sent Universal (map (\(a, b) -> Name b) (l++[(m, m)])) (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [( (typeFunction c (map snd l))), (typeFunction (mkSimpleId "member") [m, y] )] ) nullRange ) ( (typeFunction cy [m])) ) nullRange) nullRange) -}

translateProcedure :: (Class, String, [(String, Type)], Type) -> [TEXT_META]
translateProcedure (cl, n, paras, t) = map phrase2TM $ mem ++ (map (translateProperty proct l) sens)
            where
                x = mkSimpleId $ getStringNotInList "x" paraNames
                y = mkSimpleId $ getStringNotInList "y" ((tokStr x) : paraNames)
                sens = (map translateTuple ([(c, x)] ++ (map (translateParameter) paras))) ++ [translateTau m (mkSimpleId $ translateUMLType $ umltype t, mkSimpleId $ translateTargetType t, y)]
                l = case Just t of
                    Nothing -> [(c, x)] ++ (map (translateParameter) paras)
                    Just ret -> [(c, x)] ++ (map (translateParameter) paras) ++ [(mkSimpleId (translateType ret), y)]
                mem = case Just t of
                    Nothing -> []
                    Just ret -> [    --(memberRule proct l (mkSimpleId (translateType ret), y) (mkSimpleId $ getStringNotInList "m" ([(tokStr x)++(tokStr y)]++paraNames))),
                            leftTotallityRule proct l (mkSimpleId (translateType ret), y),
                            rightUniqueRule proct l (mkSimpleId (translateType ret), y) (mkSimpleId $ getStringNotInList "z" ([(tokStr x) ++ (tokStr y)] ++ paraNames))]
                paraNames = map fst paras
                m = mkSimpleId "m"
                proct = mkSimpleId $ (className cl) ++ "." ++ n
                c =  mkSimpleId $ translateType ctype
                ctype = Type {    umltype = CE $ CL cl,
                        typeOrdered = False,
                        typeUnique = True}

leftTotallityRule  :: Token -> [(Token, Token)] -> (Token, Token) -> PHRASE
leftTotallityRule c l (cz, z) = Sentence (Quant_sent Universal (map (\ (_, b) -> Name b) (delete (cz, z) l)) (Quant_sent Existential [Name z] (typeFunction c (map snd l)) nullRange) nullRange)

{-translateCompLabel :: Association -> [PHRASE]
translateCompLabel ass = (foldl (++) [] $ map ((translateCompLabel1 (mkSimpleId $ assoName ass)).label) (ends ass))

translateCompLabel1 :: Token -> Label -> [PHRASE]
translateCompLabel1 r l = map (translateCompLabel2 r) $ case upperValue l of
    "*" ->[(mkSimpleId "geq", mkSimpleId $ lowerValue l)]
    _ -> [(mkSimpleId "geq", mkSimpleId $ lowerValue l), (mkSimpleId "leq", mkSimpleId $ upperValue l)]

translateCompLabel2 :: Token -> (Token, Token) -> PHRASE
translateCompLabel2 r (f, l)  = Sentence (Quant_sent Universal [Name x, Name y, Name n] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [ typeFunction r [x, y], typeFunction (mkSimpleId "form:sequence-length") [y, n]]) nullRange) (typeFunction f [l, n])) nullRange) nullRange)
    where
        x = mkSimpleId "x"
        y = mkSimpleId "y"
        n = mkSimpleId "n"

translateAssoLabel :: Association -> [PHRASE]
translateAssoLabel ass = map (translateAssoLabel2 (mkSimpleId $ assoName ass) (zip endNames (map mkSimpleId classNames))) [(map (mkSimpleId.lowerValue.label) (ends ass), "min-card-tuple"), (map (mkSimpleId.upperValue.label) (ends ass), "max-card-tuple")]
            where     endNames = map mkSimpleId $ generateNames ((assoName ass):classNames) (length classNames)
                classNames = (map (translateType.defaultType.endTarget) (ends ass))

translateAssoLabel2 :: Token -> [(Token, Token)] -> ([Token], String) -> PHRASE
translateAssoLabel2 a xcl (sels, f)=  Sentence (Quant_sent Universal (map (\(x, c)-> Name x) xcl) (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction (map (\(x, c) ->  typeFunction c [x]) xcl)) nullRange) (Atom_sent (Atom (Funct_term (Name_term $ mkSimpleId f) ((Term_seq $ Name_term a) : (map (\(x, c) -> Term_seq $ Name_term x) xcl)) nullRange) (map (\t -> Term_seq (Name_term $ t)) sels)) nullRange)) nullRange) nullRange)-}

rightUniqueRule ::  Token -> [(Token, Token)] -> (Token, Token) -> Token -> PHRASE
rightUniqueRule c l (_, y) z = Sentence (Quant_sent Universal ((map (\ (_, b) -> Name b) l) ++ [Name z]) (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [( (typeFunction c (map snd l))), ((typeFunction c (((delete y (map snd l)) ++ [z]))))]) nullRange) (Atom_sent (Equation (Name_term y) (Name_term z)) nullRange) ) nullRange) nullRange)

memberRule :: Token -> [(Token, Token)] -> (Token, Token) -> Token -> PHRASE
memberRule c l (cy, y) m = Sentence (Quant_sent Universal (map (\ (_, b) -> Name b) (l ++ [(m, m)])) (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [( (typeFunction c (map snd l))), (typeFunction (mkSimpleId "member") [m, y] )] ) nullRange ) ( (typeFunction cy [m])) ) nullRange) nullRange)

translateParameter :: (String, Type) -> (Token, Token)
translateParameter (s, t) = ( mkSimpleId (translateType $ t), mkSimpleId $ s)


translateType :: Type -> String
translateType t = translateUMLType $ umltype t

translateTargetType :: Type -> String
translateTargetType t =  listType -- ++ "[" ++ (translateUMLType $ umltype t) ++ "]"
            where listType = case (typeOrdered t, typeUnique t) of
                    (True, True) -> "Ordered-Set"
                    (True, False) -> "Sequence"
                    (False, True) -> "Set"
                    (False, False) -> "Bag"

translateUMLType :: UMLType -> String
translateUMLType UMLBool = "buml:Boolean"
translateUMLType UMLString = "buml:String"
translateUMLType UMLInteger = "buml:Integer"
translateUMLType UMLUnlimitedNatural = "form:NaturalNumber"
translateUMLType UMLReal = "buml:Real"
translateUMLType (CE x) = showClassEntityName x
translateUMLType t = error $ "TypeTranslation unimplemented:" ++ show t



--Sign


retrieveSen :: CM -> [Sen]
retrieveSen m = foldl (++) [] ((map class2MFs $ fmap CL (Map.elems $ cmClasses m))
                ++ (map asso2MFs (filter (not . isComposition) $ Map.elems $ cmAssociations m))
                ++ (map comp2MFs (filter (isComposition) $ Map.elems $  cmAssociations m))
                ++ map retrieveSenPack (cmPackages m))

retrieveSenPack :: Package -> [Sen]
retrieveSenPack pack = foldl (++) [] ((map class2MFs $ fmap CL (Map.elems $ classes pack))
                ++ (map asso2MFs (filter (not . isComposition) $ Map.elems $ associations pack))
                ++ (map comp2MFs (filter (isComposition) $ Map.elems $ associations pack))
                ++ map retrieveSenPack (packagePackages pack))

class2MFs :: ClassEntity -> [Sen]
class2MFs (CL cl) = foldl (++) [] $ map (attr2MFs cl) (attr cl)
class2MFs (AC ac) = class2MFs (CL $ acClass ac)
class2MFs (EN _) = []
class2MFs (DT _) = []

attr2MFs :: Class -> Attribute -> [Sen]
attr2MFs cl attri = bounds2MFs (attrLowerValue attri) (attrUpperValue attri) (NumAttr $ MFAttribute (className cl) (attrName attri) (type2mftype $ attrType attri) )

bounds2MFs :: String -> String -> FunExpr -> [Sen]
bounds2MFs low upp fe = (NLeqF (read low) fe) :
                    case upp of
                        "*" -> []
                        _ -> [FLeqN fe (read upp)]

end2StrMFT :: End -> (String, MFTYPE)
end2StrMFT end = (fromJust $ endName end, type2mftype $ defaultType $ endTarget end)

asso2MFs :: Association -> [Sen]
asso2MFs ass = foldl (++) [] $  map (end2MFs (NumAss (MFAssociation (assoName ass) (map end2StrMFT (ends ass))))) (ends ass)


end2MFs :: (String -> FunExpr) -> End -> [Sen]
end2MFs an end = bounds2MFs (lowerValue $ label end) (upperValue $ label end) (an $ fromJust $ endName end)

comp2MFs :: Association -> [Sen]
comp2MFs comp = foldl (++) [] $  map (end2MFs (NumComp $ MFComposition (assoName comp) (fromJust $ endName origin) (MFType Set (showClassEntityName $ endTarget origin)) (fromJust $ endName target) (type2mftype $ defaultType $ endTarget target) )) (ends comp)
                    where
                        origin = head $ filter isComposedEnd $ ends comp
                        target = case (filter (not . (origin ==)) (ends comp)) of
                            (x : _) -> x
                            [] -> error $ show $ ends comp


retrieveSign :: CM -> UML.Sign.Sign
retrieveSign cm = UML.Sign.Sign {
            signClassHier = ((foldl (++) [] (map (fst . signClassHier) packSigs)) ++ (fmap EN enumLis) ++ (map (\ c -> CL c) classLis), (foldl (++) [] (map (snd . signClassHier) packSigs)) ++ (foldl (++) [] (map classToHier classLis))),
            signAttribute = (foldl (++) [] (map signAttribute packSigs)) ++ attributes,
            signOperations = (foldl (++) [] (map signOperations packSigs)) ++ procedures,
            signCompositions = (foldl (++) [] (map signCompositions packSigs)) ++ compositions,
            signAssociations = (foldl (++) [] (map signAssociations packSigs)) ++ associations0
        }
    where
        classLis = Map.elems (cmClasses cm)
        enumLis = Map.elems (cmEnums cm)
        --assoClasses = Map.elems (translateAssociationClasses (cmClasses cm))
        attributes = foldl (++) [] $ map (\ c -> map (signTranslateAttr c) (attr c)) classLis
        compositions = map signTranslateComposition $ filter isComposition $ Map.elems $ cmAssociations cm
        procedures = foldl (++) [] $ map (\ c -> map (signTranslateProc c) $ filter (isJust . procReturnType) (proc c)) classLis
        associations0 = map signTranslateAsso $ filter (not . isComposition) $ Map.elems (cmAssociations cm)
        packSigs = map retrieveSignPackage (cmPackages cm)

retrieveSignPackage :: UML.UML.Package -> UML.Sign.Sign
retrieveSignPackage pack = UML.Sign.Sign {
            signClassHier = ((foldl (++) [] (map (fst . signClassHier) packSigs)) ++ (fmap EN enumLis) ++ (map (\ c -> CL c) classLis), (foldl (++) [] (map (snd . signClassHier) packSigs)) ++ (foldl (++) [] (map classToHier classLis))),
            signAttribute = (foldl (++) [] (map signAttribute packSigs)) ++ attributes,
            signOperations = (foldl (++) [] (map signOperations packSigs)) ++ procedures,
            signCompositions = (foldl (++) [] (map signCompositions packSigs)) ++ compositions,
            signAssociations = (foldl (++) [] (map signAssociations packSigs)) ++ associations0
        }
    where
        classLis = Map.elems (classes pack)
        enumLis = Map.elems (packageEnums pack)
        --assoClasses = Map.elems (translateAssociationClasses (cmClasses cm))
        attributes = foldl (++) [] $ map (\ c -> map (signTranslateAttr c) (attr c)) classLis
        compositions = map signTranslateComposition $ filter isComposition $ Map.elems $ associations pack
        procedures = foldl (++) [] $ map (\ c -> map (signTranslateProc c) $ filter (isJust . procReturnType) (proc c)) classLis -- TODO: Add handling for empty return
        associations0 = map signTranslateAsso $ filter (not . isComposition) $ Map.elems $ associations pack
        packSigs = map retrieveSignPackage (packagePackages pack)

extractClasses :: [ClassEntity] -> [Class]
extractClasses [] = []
extractClasses ((CL c) : lis) = c : (extractClasses lis)
extractClasses (_ : lis) = (extractClasses lis)

signTranslateAttr :: Class -> Attribute -> (Class, String, Type)
signTranslateAttr c a  =  (c,  attrName a, attrType a)


signTranslateProc :: Class -> Procedure -> (Class, String, [(String, Type)], Type)
signTranslateProc c proce = (c, procName proce, map (\ attri -> (attrName attri, attrType attri)) (procPara proce), fromJust $ procReturnType proce)

signTranslateComposition :: Association -> ((String, ClassEntity), String, (String, Type))
signTranslateComposition comp = ((fromJust $ endName origin, endTarget origin), assoName comp, (fromJust $ endName target, defaultType $ endTarget target))
    where
        origin = head $ filter isComposedEnd $ ends comp
        target = case (filter (not . (origin ==)) (ends comp)) of
                    (x : _) -> x
                    [] -> error $ show $ ends comp
signTranslateAsso :: Association -> (String, [(String, Type)])
signTranslateAsso ass = (assoName ass, map signTranslateEnd (ends ass))

signTranslateEnd :: End -> (String, Type)
signTranslateEnd e = (fromJust $ endName e, defaultType $ endTarget e)

classToHier :: Class -> [(ClassEntity, ClassEntity)]
classToHier cl = zip [CL cl] (getAllSupers (CL cl))

getAllSupers :: ClassEntity -> [ClassEntity]
getAllSupers (CL cl) = (super cl) ++ (foldl (++) [] $ map getAllSupers (super cl))
getAllSupers _ = []

