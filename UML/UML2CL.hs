module UML2CL where 
import CommonLogic.Sign 
import CommonLogic.AS_CommonLogic
import UML
import qualified Data.Map as Map
import Common.Id as Id
import Data.Maybe
import Utils
import Data.List
import Utils
translate :: Model -> TEXT
translate (ClassModel cm) = Text phrases nullRange
				where 	phrases = preamble ++ (translateClasses cm (cmClasses cm)) 
						++ (map translateEnumPreamble $ ((Map.elems).cmEnums) cm) 
						++ (foldl (++) [] $ (map translateComposition compositions)) 
						++ (map translateComPair (pairs compositions))
						++ (map translateAssociation (Map.elems $ cmAssociations cm))
					compositions = filter isComposition $ Map.elems $ cmAssociations cm

pairs :: [a] -> [(a,a)] 
pairs [] = []
pairs (x:lis) = [(x,y) | y <- (x:lis)] ++ (pairs lis)

preamble :: [PHRASE]
preamble = [	Sentence (termAtom (Name_term dt )),
		Sentence (termAtom (typeFunction dt [mkSimpleId "x"])),
		Sentence (Bool_sent (BinOp Biconditional (termAtom (typeFunctionSeq dt [Name x, Name y, seq])) (Bool_sent (Junction Conjunction [
			 Bool_sent (Negation (termAtom (typeFunction (mkSimpleId "=") [x, y])) ) nullRange, 
			termAtom (typeFunctionSeq dt [Name x, seq]) , 
			termAtom (typeFunctionSeq dt [Name y, seq]) ]) nullRange)) nullRange),
		Sentence (Bool_sent (Negation $ termAtom (typeFunction oneof [x])) nullRange),
		Sentence (Bool_sent (BinOp Biconditional (termAtom  $ typeFunctionSeq oneof [Name x, Name y,seq]) (Bool_sent (Junction Disjunction [
			termAtom (typeFunctionSeq (mkSimpleId "=") [Name x, Name y]),  
			termAtom  $ typeFunctionSeq oneof [Name x, seq]]) nullRange)) nullRange),
		Sentence $ Quant_sent Universal [Name x, Name s] (Bool_sent (BinOp Implication 				(termAtom $ typeFunction memb [x,s]) 
				(termAtom $ typeFunction (mkSimpleId "form:Sequence") [s])) nullRange)  nullRange,
		Sentence $ Quant_sent Universal [Name x, Name s] (Bool_sent (BinOp Biconditional 				(termAtom $ typeFunction memb [x,s]) 
			(Quant_sent Existential [Name pt] (Bool_sent (Junction  Conjunction[
				(termAtom $ typeFunction (mkSimpleId "form:in-sequence") [s,pt]),
				(termAtom $ typeFunction (mkSimpleId "form:in-position") [pt,x])]) nullRange) nullRange)) nullRange ) nullRange 
		]
		where 	dt = (mkSimpleId "distinct")
			x = mkSimpleId "x"
			y = mkSimpleId "y"
			s = mkSimpleId "s"
			pt = mkSimpleId "pt"
			seq = SeqMark $ mkSimpleId "..."
			oneof = mkSimpleId "oneof"
			memb = mkSimpleId "member"

translateAssociation :: Association -> PHRASE
translateAssociation as = Sentence $ Quant_sent Universal (map (\(x,c) -> Name x) endPairs) (Bool_sent (BinOp Implication (termAtom $ typeFunction aname (map fst endPairs)) (Bool_sent(Junction Conjunction (map (\(x,c)-> termAtom $ typeFunction c [x]) endPairs)) nullRange)) nullRange) nullRange
			where 	endPairs = zip names (map mkSimpleId endTypes)
				endTypes = (map (translateType.defaultType.endTarget) $ ends as)
				x = head $ filter (\x -> not $ any (isPrefixOf x) endTypes) allStrings 
				names = [mkSimpleId $ x ++ (show i)| i <- [1..(length $ ends as)]]
				aname = mkSimpleId $ assoName as	
				allStrings = concatMap (\s -> map (:s) $ ['a'..'z'] ++ ['0'..'9']) $ "" : allStrings  

rlookup :: (Ord s) => Map.Map s t -> s -> Maybe t
rlookup m k = Map.lookup k m

getCompoRelevants :: Association -> (Token, Token, Token)
getCompoRelevants ass = (mkSimpleId $ translateType $ defaultType  (endTarget origin), 
			mkSimpleId $ assoName ass,
			mkSimpleId $ translateTargetType $ defaultType $ endTarget target)
			where 	origin = head $ filter isComposedEnd $ ends ass 
				target = head (filter (not.(origin==)) (ends ass))
				originToken = (translateType $ defaultType (endTarget origin))

translateComPair :: (Association,Association) -> PHRASE 
translateComPair (a1,a2) = Sentence $ Quant_sent Universal [Name x1, Name x2, Name y1, Name y2] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [termAtom $ typeFunction nam1 [x1,y1], termAtom $ typeFunction nam2 [x2,y2]]) nullRange) (Quant_sent Existential [Name z] (Bool_sent (Junction Conjunction [termAtom $ typeFunction member [z,x1], termAtom $ typeFunction member [z,x2]]) nullRange) nullRange) ) nullRange) nullRange
	where 	x1 = mkSimpleId "x1"
		y1 = mkSimpleId "y1"
		x2 = mkSimpleId "x2"
		y2 = mkSimpleId "y2"
		z = mkSimpleId "z" 
		member = mkSimpleId "member"
		(ori1,nam1,tar1) = getCompoRelevants a1
		(ori2,nam2,tar2) = getCompoRelevants a2

translateComposition :: Association -> [PHRASE]
translateComposition ass = translateComposition2 $ getCompoRelevants ass

translateComposition2 :: (Token,Token,Token) -> [PHRASE]
translateComposition2 (origin, comp, target) = [	Sentence $ Quant_sent Universal [Name x] (
						Bool_sent (BinOp Implication (termAtom $ typeFunction origin [x]) (Quant_sent Existential [Name y] (Bool_sent(Junction Conjunction [
				termAtom $ typeFunction comp [x,y],
				termAtom $ typeFunction target [y]
						]) nullRange) nullRange)) nullRange) nullRange,

					Sentence $ Quant_sent Universal [Name x, Name y] (
						Bool_sent (BinOp Implication (termAtom $ typeFunction comp [x,y])  (Bool_sent(Junction Conjunction [
				termAtom $ typeFunction origin [x],
				termAtom $ typeFunction target [y]
						]) nullRange)) nullRange) nullRange,

					Sentence $ Quant_sent Universal [Name x, Name y, Name z] (
						Bool_sent (BinOp Implication (Bool_sent(Junction Conjunction [
				termAtom $ typeFunction comp [x,y],
				termAtom $ typeFunction comp [x,z]
						]) nullRange) (termAtom $ typeFunction (mkSimpleId "=") [y,z]  )) nullRange) nullRange]  
	where 	x = mkSimpleId "x"
		y = mkSimpleId "y"
		z = mkSimpleId "z"

isComposedEnd :: End -> Bool 
isComposedEnd en = (endType en) == Composition

isComposition :: Association -> Bool 
isComposition as = any isComposedEnd (ends as)

translateEnumPreamble :: UML.Enum -> PHRASE
translateEnumPreamble en = Sentence $ termAtom $ typeFunction (mkSimpleId "enumeration") $ (mkSimpleId $ enumName en):(map (mkSimpleId.literalName) (enumLiterals en))

translateClasses :: CM -> Map.Map UML.Id UML.Class -> [PHRASE]
translateClasses cm cmap =   foldl (++) [] $ map (translateClass cm) (Map.elems cmap)

translateClass :: CM -> UML.Class -> [PHRASE]
translateClass cm cl = (translateInherit (CL cl) (super cl)) ++ (foldl (++) [] (map (translateAttribute cm cl) (attr cl))) ++ (foldl (++) [] (map (translateProcedure cm cl) (proc cl)))

translateInherit :: ClassEntity -> [ClassEntity] -> [PHRASE]
translateInherit cl (super:l) =   (Sentence (Quant_sent Universal [Name t]  (Bool_sent (BinOp Implication 
					(Atom_sent (Atom  (typeFunction (mkSimpleId (showClassEntityName cl)) [t]) []) nullRange)
					(Atom_sent (Atom  (typeFunction (mkSimpleId (showClassEntityName super)) [t]) []) nullRange)) nullRange) nullRange)):(translateInherit cl l ) 
					where t = mkSimpleId "x"
translateInherit cl [] = [] 

typeFunction :: Token -> [Token] -> TERM 
typeFunction f l = (Funct_term (Name_term f) (map (\t -> Term_seq (Name_term t)) l) nullRange)

typeFunctionSeq :: Token -> [NAME_OR_SEQMARK] -> TERM 
typeFunctionSeq f l = (Funct_term (Name_term f) (map termNOS l) nullRange)

termNOS:: NAME_OR_SEQMARK -> TERM_SEQ
termNOS (Name n) = Term_seq $ Name_term  n
termNOS (SeqMark s) = Seq_marks  s

translateAttribute :: CM -> Class -> Attribute -> [PHRASE]
translateAttribute cm cl attr = mem ++ (map (translateProperty attrt l) l) 
			where 	x = mkSimpleId "x"
				y = mkSimpleId "y"
				l = [(c,x),(cptar,y)]
				attrt = mkSimpleId $ (className cl) ++ "." ++ (attrName attr)
				c =  mkSimpleId $ translateType $ defaultType $ CL cl
				cp = mkSimpleId $ translateTargetType (attrType attr)
				cptar = mkSimpleId $ translateType (attrType attr)
				mem = [	(memberRule cm attrt l (cp,y) (mkSimpleId "m")), 
					leftTotallityRule cm attrt l (cp,y),
					rightUniqueRule cm attrt l (cp,y) (mkSimpleId "z")]

defaultType :: ClassEntity -> Type
defaultType ce = Type{umltype = CE ce, typeOrdered = False, typeUnique = True}

translateProcedure :: CM -> Class -> Procedure -> [PHRASE]
translateProcedure cm cl proc = mem ++ (map (translateProperty proct l) l)
			where 	x = mkSimpleId $ getStringNotInList "x" paraNames
				y = mkSimpleId $ getStringNotInList "y" ((tokStr x):paraNames)
				l = case (procReturnType proc) of 
					Nothing -> [(c,x)] ++ (map (translateParameter) (procPara proc))
					Just ret -> [(c,x)] ++ (map (translateParameter) (procPara proc)) ++ [(mkSimpleId (translateType ret), y)] 
				mem = case (procReturnType proc) of
					Nothing -> []
					Just ret -> [	(memberRule cm proct l (mkSimpleId (translateType ret),y) (mkSimpleId $ getStringNotInList "m" ([(tokStr x)++(tokStr y)]++paraNames))),
							leftTotallityRule cm proct l (mkSimpleId (translateType ret),y),
							rightUniqueRule cm proct l (mkSimpleId (translateType ret),y) (mkSimpleId $ getStringNotInList "z" ([(tokStr x)++(tokStr y)]++paraNames))]
				paraNames = map attrName (procPara proc) 
				proct = mkSimpleId $ (className cl) ++ "." ++ (procName proc)
				c =  mkSimpleId $ translateType ctype
				ctype = Type{	umltype = CE $ CL cl,
						typeOrdered = False,
						typeUnique = True}

leftTotallityRule  :: CM -> Token -> [(Token,Token)] -> (Token, Token) -> PHRASE
leftTotallityRule cm c l (cz,z) = Sentence (Quant_sent Universal (map (\(a,b) -> Name b) (delete (cz,z) l)) (Quant_sent Existential [Name z] (termAtom (typeFunction c (map snd l))) nullRange) nullRange)


rightUniqueRule :: CM -> Token -> [(Token,Token)] -> (Token,Token) -> Token -> PHRASE
rightUniqueRule cm c l (cy,y) z = Sentence (Quant_sent Universal (map (\(a,b) -> Name b) l) (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [(termAtom (typeFunction c (map snd l))),(termAtom (typeFunction c ((map snd (delete (cy,y) l)++[z]))))]) nullRange) (termAtom (typeFunction (mkSimpleId "=") [y,z])) ) nullRange) nullRange)

memberRule :: CM -> Token -> [(Token,Token)] -> (Token, Token) -> Token -> PHRASE
memberRule cm c l (cy,y) m = Sentence (Quant_sent Universal (map (\(a,b) -> Name b) (l++[(m,m)])) (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [(termAtom (typeFunction c (map snd l))), termAtom (typeFunction (mkSimpleId "member") [m,y] )] ) nullRange ) (termAtom (typeFunction cy [m])) ) nullRange) nullRange) 

translateParameter :: Attribute -> (Token, Token)
translateParameter at = ( mkSimpleId (translateType $ attrType at), mkSimpleId $ attrName at) 

termAtom :: TERM -> SENTENCE
termAtom t = Atom_sent (Atom t []) nullRange

translateType :: Type -> String
translateType t = translateUMLType $ umltype t

translateTargetType :: Type -> String
translateTargetType t =  listType ++ "[" ++ (translateUMLType $ umltype t) ++ "]"
			where listType = case (typeOrdered t, typeUnique t) of 
					(True, True) -> "OrderedSet"
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

translateProperty :: Token -> [(Token,Token)] -> (Token,Token) -> PHRASE
translateProperty c l (cz,z) = Sentence (Quant_sent Universal (map (\(a,b) -> Name b) l) (Bool_sent (BinOp Implication (termAtom (typeFunction c (map snd l))) (termAtom (typeFunction cz [z])) ) nullRange) nullRange)
				where applyType (t1,t2) = typeFunction t1 [t2] 


