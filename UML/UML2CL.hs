module UML.UML2CL where 
import CommonLogic.Sign 
import CommonLogic.AS_CommonLogic
import UML.UML
import qualified Data.Map as Map
import Common.Id as Id
import Common.Doc as Doc hiding (Label)
import Data.Maybe
import UML.Utils
import Data.List
import CommonLogic.Parse_CLIF
import Text.ParserCombinators.Parsec hiding (label)
import qualified Data.Text    as Text
import qualified Data.Text.IO as Text

translate :: Model -> TEXT
translate (ClassModel cm) = Text phrases nullRange
				where 	phrases = preamble ++ (translateClasses (cmClasses cm)) 
						++ (map translateEnumPreamble $ ((Map.elems).cmEnums) cm) 
						++ (foldl (++) [] $ (map translateComposition compositions)) 
						++ (map translateComPair (pairs compositions))
						++ (map translateAssociation (Map.elems $ cmAssociations cm))
						++ (foldl (++) [] (map translatePackage (cmPackages cm)))
						++ (foldl (++) [] $ (map translateCompLabel compositions))
						++ (foldl (++) [] $ (map translateAssoLabel (filter (not.isComposition) (Map.elems $ cmAssociations cm)))) ++ postamble
					compositions = filter isComposition $ Map.elems $ cmAssociations cm


translatePackage :: Package -> [PHRASE]
translatePackage pack = (translateClasses (classes pack))  
						++ (map translateEnumPreamble $ ((Map.elems).packageEnums) pack) 
						++ (foldl (++) [] $ (map translateComposition compositions)) 
						++ (map translateComPair (pairs compositions))
						++ (map translateAssociation (Map.elems $ associations pack))
					where compositions = filter isComposition $ Map.elems $ associations pack
pairs :: [a] -> [(a,a)] 
pairs [] = []
pairs (x:lis) = [(x,y) | y <- (x:lis)] ++ (pairs lis)

preamble :: [PHRASE]
preamble = [	Sentence (Atom_sent (Atom (Name_term (mkSimpleId "distinct")) []) nullRange),Sentence (Atom_sent (Atom (Name_term (mkSimpleId "distinct")) [Term_seq (Name_term (mkSimpleId "x"))]) nullRange),
	Sentence (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "distinct")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "y")),Seq_marks (mkSimpleId "...")]) nullRange) (Bool_sent (Junction Conjunction [Bool_sent (Negation (Atom_sent (Equation (Name_term (mkSimpleId "x")) (Name_term (mkSimpleId "y"))) nullRange)) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "distinct")) [Term_seq (Name_term (mkSimpleId "x")),Seq_marks (mkSimpleId "...")]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "distinct")) [Term_seq (Name_term (mkSimpleId "y")),Seq_marks (mkSimpleId "...")]) nullRange]) nullRange)) nullRange),
	Sentence (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "exhaustive")) [Term_seq (Name_term (mkSimpleId "c")),Seq_marks (mkSimpleId "...")]) nullRange) (Quant_sent Universal [Name (mkSimpleId "x")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "c")) [Term_seq (Name_term (mkSimpleId "x"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "oneof")) [Term_seq (Name_term (mkSimpleId "x")),Seq_marks (mkSimpleId "...")]) nullRange)) nullRange) nullRange)) nullRange),
	Sentence (Bool_sent (Negation (Atom_sent (Atom (Name_term (mkSimpleId "oneof")) [Term_seq (Name_term (mkSimpleId "x"))]) nullRange)) nullRange),
	Sentence (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "oneof")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "y")),Seq_marks (mkSimpleId "...")]) nullRange) (Bool_sent (Junction Disjunction [Atom_sent (Equation (Name_term (mkSimpleId "x")) (Name_term (mkSimpleId "y"))) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "oneof")) [Term_seq (Name_term (mkSimpleId "x")),Seq_marks (mkSimpleId "...")]) nullRange]) nullRange)) nullRange),
	Sentence (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "enumeration")) [Term_seq (Name_term (mkSimpleId "c")),Seq_marks (mkSimpleId "...")]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "exhaustive")) [Term_seq (Name_term (mkSimpleId "c")),Seq_marks (mkSimpleId "...")]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "distinct")) [Seq_marks (mkSimpleId "...")]) nullRange]) nullRange)) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "y")] (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:first")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:pair")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "y"))] nullRange)] nullRange) (Name_term (mkSimpleId "x"))) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "y")] (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:second")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:pair")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "y"))] nullRange)] nullRange) (Name_term (mkSimpleId "y"))) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "y")] (Atom_sent (Atom (Name_term (mkSimpleId "form:Pair")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:pair")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "y"))] nullRange)]) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "p")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Pair")) [Term_seq (Name_term (mkSimpleId "p"))]) nullRange) (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:pair")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:first")) [Term_seq (Name_term (mkSimpleId "p"))] nullRange),Term_seq (Funct_term (Name_term (mkSimpleId "form:second")) [Term_seq (Name_term (mkSimpleId "p"))] nullRange)] nullRange) (Name_term (mkSimpleId "p"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:sequence-member")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "s")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:sequence-member")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "pt")] (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange]) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "o")] (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:select1")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Name_term (mkSimpleId "form:empty-sequence"))] nullRange) (Name_term (mkSimpleId "form:empty-sequence"))) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "o"),Name (mkSimpleId "y"),Name (mkSimpleId "s")] (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:select1")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Funct_term (Name_term (mkSimpleId "form:insert-sequence")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:pair")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Name_term (mkSimpleId "y"))] nullRange)] nullRange)] nullRange) (Funct_term (Name_term (mkSimpleId "form:insert-sequence")) [Term_seq (Name_term (mkSimpleId "y")),Term_seq (Funct_term (Name_term (mkSimpleId "form:select1")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)] nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "o"),Name (mkSimpleId "x"),Name (mkSimpleId "y"),Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Bool_sent (Negation (Atom_sent (Equation (Name_term (mkSimpleId "x")) (Name_term (mkSimpleId "o"))) nullRange)) nullRange) (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:select1")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Funct_term (Name_term (mkSimpleId "form:insert-sequence")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:pair")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "y"))] nullRange)] nullRange)] nullRange) (Funct_term (Name_term (mkSimpleId "form:select1")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "o")] (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:select2")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Name_term (mkSimpleId "form:empty-sequence"))] nullRange) (Name_term (mkSimpleId "form:empty-sequence"))) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "o"),Name (mkSimpleId "x"),Name (mkSimpleId "s")] (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:select2")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Funct_term (Name_term (mkSimpleId "form:insert-sequence")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:pair")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "o"))] nullRange)] nullRange)] nullRange) (Funct_term (Name_term (mkSimpleId "form:insert-sequence")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Funct_term (Name_term (mkSimpleId "form:select2")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)] nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "o"),Name (mkSimpleId "x"),Name (mkSimpleId "y"),Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Bool_sent (Negation (Atom_sent (Equation (Name_term (mkSimpleId "y")) (Name_term (mkSimpleId "o"))) nullRange)) nullRange) (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:select2")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Funct_term (Name_term (mkSimpleId "form:insert-sequence")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:pair")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "y"))] nullRange)] nullRange)] nullRange) (Funct_term (Name_term (mkSimpleId "form:select2")) [Term_seq (Name_term (mkSimpleId "o")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s1"),Name (mkSimpleId "s2")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:same-bag")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "s2"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Bag")) [Term_seq (Name_term (mkSimpleId "s1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Bag")) [Term_seq (Name_term (mkSimpleId "s2"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s1"),Name (mkSimpleId "s2")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:same-bag")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "s2"))]) nullRange) (Quant_sent Universal [Name (mkSimpleId "x")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:bag-member-count")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s1"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:bag-member-count")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s2"))]) nullRange)) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Bag")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:Bag")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:bag-insert")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "y"),Name (mkSimpleId "s")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:bag-member")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Funct_term (Name_term (mkSimpleId "form:bag-insert")) [Term_seq (Name_term (mkSimpleId "y")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)]) nullRange) (Bool_sent (Junction Disjunction [Atom_sent (Equation (Name_term (mkSimpleId "x")) (Name_term (mkSimpleId "y"))) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:bag-member")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Bag")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "buml:UnlimtedNatural")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:bag-member-count")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)]) nullRange)) nullRange) nullRange),
	Sentence (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:bag-member-count")) [Term_seq (Name_term (mkSimpleId "form:empty-bag"))] nullRange) (Name_term (mkSimpleId "form:0"))) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "s")] (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:bag-member-count")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Funct_term (Name_term (mkSimpleId "form:bag-insert")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)] nullRange) (Funct_term (Name_term (mkSimpleId "form:suc")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:bag-member-count")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)] nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "y"),Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Bool_sent (Negation (Atom_sent (Equation (Name_term (mkSimpleId "x")) (Name_term (mkSimpleId "y"))) nullRange)) nullRange) (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:bag-member-count")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Funct_term (Name_term (mkSimpleId "form:bag-insert")) [Term_seq (Name_term (mkSimpleId "y")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)] nullRange) (Funct_term (Name_term (mkSimpleId "form:bag-member-count")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "b")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Bag")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:Set")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:bag2set")) [Term_seq (Name_term (mkSimpleId "b"))] nullRange)]) nullRange)) nullRange) nullRange),
	Sentence (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:bag2set")) [Term_seq (Name_term (mkSimpleId "form:empty-bag"))] nullRange) (Name_term (mkSimpleId "form:empty-set"))) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "b")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Bag")) [Term_seq (Name_term (mkSimpleId "b"))]) nullRange) (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:bag2set")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:set-insert")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "b"))] nullRange)] nullRange) (Funct_term (Name_term (mkSimpleId "form:bag-insert")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Funct_term (Name_term (mkSimpleId "form:bag2set")) [Term_seq (Name_term (mkSimpleId "b"))] nullRange)] nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "b")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:Ordered-Set")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:seq2ordset")) [Term_seq (Name_term (mkSimpleId "s"))] nullRange)]) nullRange)) nullRange) nullRange),
	Sentence (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:seq2ordset")) [Term_seq (Name_term (mkSimpleId "form:empty-empty"))] nullRange) (Name_term (mkSimpleId "form:empty-ordered-set"))) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Atom_sent (Equation (Funct_term (Name_term (mkSimpleId "form:seq2ordset")) [Term_seq (Funct_term (Name_term (mkSimpleId "form:sequence-insert")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Name_term (mkSimpleId "s"))] nullRange)] nullRange) (Funct_term (Name_term (mkSimpleId "form:ordered-set-insert")) [Term_seq (Name_term (mkSimpleId "x")),Term_seq (Funct_term (Name_term (mkSimpleId "form:seq2ordset")) [Term_seq (Name_term (mkSimpleId "s"))] nullRange)] nullRange)) nullRange)) nullRange) nullRange)
		]

translateAssociation :: Association -> PHRASE
translateAssociation as = Sentence $ Quant_sent Universal [Name t] (ifSen (typeFunction (mkSimpleId "form:sequence-member") [t,a]) (Quant_sent Existential (map (\(x,c)-> Name x) endPairs) (andSen $ (map (\(x,c) -> typeFunction c [x]) endPairs) ++ [(Atom_sent (Equation (Name_term t) (x2inserts $ map fst endPairs)) nullRange)]) nullRange)) nullRange
			where 	endPairs = zip names (map mkSimpleId endTypes)
				endTypes = (map (translateType.defaultType.endTarget) $ ends as)
				x = head $ filter (\x -> not $ any (isPrefixOf x) endTypes) allStrings 
				t = mkSimpleId "t" 
				a = mkSimpleId "a"
				names = [mkSimpleId $ x ++ (show i)| i <- [1..(length $ ends as)]]
				aname = mkSimpleId $ assoName as	
				allStrings = concatMap (\s -> map (:s) $ ['a'..'z'] ++ ['0'..'9']) $ "" : allStrings  
				x2inserts (x:(y:ls)) = Funct_term (Name_term $ mkSimpleId "form:insert-sequence") [Term_seq $ Name_term x,Term_seq $ (x2inserts (y:ls))] nullRange
				x2inserts [x] = Funct_term (Name_term $ mkSimpleId "form:insert-sequence") [Term_seq $ Name_term x, Term_seq $ Name_term $ mkSimpleId "form:empty-sequence"] nullRange

generateNames :: [String] -> Int -> [String]
generateNames  lis n = [x ++ (show i)| i <- [1..n]]
			where 	x = head $ filter (\x -> not $ any (isPrefixOf x) lis) allStrings	
				allStrings = concatMap (\s -> map (:s) $ ['a'..'z'] ++ ['0'..'9']) $ "" : allStrings

rlookup :: (Ord s) => Map.Map s t -> s -> Maybe t
rlookup m k = Map.lookup k m

getCompoRelevants :: Association -> (Token, Token, Token)
getCompoRelevants ass = (mkSimpleId $ translateType $ defaultType  (endTarget origin), 
			mkSimpleId $ assoName ass,
			mkSimpleId $ translateType $ defaultType $ endTarget target)
			where 	
				origin = head $ filter isComposedEnd $ ends ass 
				target = case (filter (not.(origin==)) (ends ass)) of 
							(x:lis) -> x
							[] -> error $ show $ ends ass 
				originToken = (translateType $ defaultType (endTarget origin))

translateComPair :: (Association,Association) -> PHRASE 
translateComPair (a1,a2) = Sentence $ Quant_sent Universal [Name o, Name op, Name i] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent ( Atom (Name_term $ mkSimpleId "form:sequence-member") [Term_seq $ Funct_term (Name_term $ mkSimpleId "form:pair") [Term_seq $ Name_term o,Term_seq $ Name_term i] nullRange, Term_seq $ Name_term m]) nullRange,Atom_sent ( Atom (Name_term $ mkSimpleId "form:sequence-member") [Term_seq $ Funct_term (Name_term $ mkSimpleId "form:pair") [Term_seq $ Name_term op,Term_seq $ Name_term i] nullRange, Term_seq $ Name_term m]) nullRange] ) nullRange) (equalSen o op)) nullRange) nullRange
	where	(c1,m,c2) = getCompoRelevants a1
		(c1p,mp,c2p) = getCompoRelevants a2
		o = mkSimpleId "o" 
		op = mkSimpleId "op"
		i = mkSimpleId "i"


equalSen :: Token -> Token -> SENTENCE
equalSen a b = (Atom_sent (Equation (Name_term a) (Name_term b)) nullRange) 


ifSen :: SENTENCE -> SENTENCE -> SENTENCE 
ifSen a b = Bool_sent (BinOp Implication a b) nullRange

iffSen :: SENTENCE -> SENTENCE -> SENTENCE 
iffSen a b = Bool_sent (BinOp Biconditional a b) nullRange

andSen ::  [SENTENCE] -> SENTENCE
andSen sens = Bool_sent (Junction Conjunction sens) nullRange 


translateComposition :: Association -> [PHRASE]
translateComposition ass = (translateComposition2 $ getCompoRelevants ass) 

translateComposition2 :: (Token,Token,Token) -> [PHRASE]
translateComposition2 (c1, m, c2) = [
	Sentence $ typeFunction (mkSimpleId "form:Sequence") [m],
	Sentence $ Quant_sent Universal [Name p] (Bool_sent (BinOp Implication (typeFunction (mkSimpleId "form:sequence-member") [p,m])  (Bool_sent (Junction Conjunction [typeFunction (mkSimpleId "form:Pair") [p], Atom_sent ( Atom (Name_term c1) [Term_seq $ Funct_term (Name_term $ mkSimpleId "form:first") [Term_seq $ Name_term p] nullRange]) nullRange, Atom_sent ( Atom (Name_term c2) [Term_seq $ Funct_term (Name_term $ mkSimpleId "form:second") [Term_seq $ Name_term p] nullRange]) nullRange] ) nullRange)) nullRange) nullRange]
	where p = mkSimpleId "p"



{-[	Sentence $ Quant_sent Universal [Name x] (
						Bool_sent (BinOp Implication (typeFunction origin [x]) (Quant_sent Existential [Name y] (Bool_sent(Junction Conjunction [
				typeFunction comp [x,y],
				typeFunction target [y]
						]) nullRange) nullRange)) nullRange) nullRange,

					Sentence $ Quant_sent Universal [Name x, Name y] (
						Bool_sent (BinOp Implication (typeFunction comp [x,y])  (Bool_sent(Junction Conjunction [
				typeFunction origin [x],
				typeFunction target [y]
						]) nullRange)) nullRange) nullRange,

					Sentence $ Quant_sent Universal [Name x, Name y, Name z] (
						Bool_sent (BinOp Implication (Bool_sent(Junction Conjunction [
				typeFunction comp [x,y],
				typeFunction comp [x,z]
						]) nullRange) (typeFunction (mkSimpleId "=") [y,z]  )) nullRange) nullRange]  
	where 	x = mkSimpleId "x"
		y = mkSimpleId "y"
		z = mkSimpleId "z"-}

isComposedEnd :: End -> Bool 
isComposedEnd en = (endType en) == Composition

isComposition :: Association -> Bool 
isComposition as = any isComposedEnd (ends as)

translateEnumPreamble :: UML.UML.Enum -> PHRASE
translateEnumPreamble en = Sentence $ typeFunction (mkSimpleId "enumeration") $ (mkSimpleId $ enumName en):(map (mkSimpleId.literalName) (enumLiterals en))

translateClasses :: Map.Map UML.UML.Id UML.UML.Class -> [PHRASE]
translateClasses cmap =   foldl (++) [] $ map translateClass (Map.elems cmap)

translateClass :: UML.UML.Class -> [PHRASE]
translateClass cl = (translateInherit (CL cl) (super cl)) ++ (foldl (++) [] (map (translateAttribute cl) (attr cl))) ++ (foldl (++) [] (map (translateProcedure cl) (proc cl)))

translateInherit :: ClassEntity -> [ClassEntity] -> [PHRASE]
translateInherit cl (super:l) =   (Sentence (Quant_sent Universal [Name t]  (Bool_sent (BinOp Implication 
					(typeFunction (mkSimpleId (showClassEntityName cl)) [t])
					(typeFunction (mkSimpleId (showClassEntityName super)) [t])) nullRange) nullRange)):(translateInherit cl l ) 
					where t = mkSimpleId "x"
translateInherit cl [] = [] 


typeFunction :: Token -> [Token] ->  SENTENCE
typeFunction f l  = Atom_sent (Atom (Name_term f) (map (\t -> Term_seq $ Name_term t) l)) nullRange

--typeFunction :: Token -> [Token] -> TERM 
--typeFunction f l = (Funct_term (Name_term f) (map (\t -> Term_seq (Name_term t)) l) nullRange)

typeFunctionSeq :: Token -> [NAME_OR_SEQMARK]  ->  SENTENCE 
typeFunctionSeq f l = Atom_sent (Atom (Name_term f) (map termNOS l)) nullRange

termNOS:: NAME_OR_SEQMARK -> TERM_SEQ
termNOS (Name n) = Term_seq $ Name_term  n
termNOS (SeqMark s) = Seq_marks  s

translateAttribute :: Class -> Attribute -> [PHRASE]
translateAttribute cl attr = mem ++ (map (translateProperty attrt l) l) 
			where 	x = mkSimpleId "x"
				y = mkSimpleId "y"
				l = [(c,x),(cptar,y)]
				attrt = mkSimpleId $ (className cl) ++ "." ++ (attrName attr)
				c =  mkSimpleId $ translateType $ defaultType $ CL cl
				cp = mkSimpleId $ translateTargetType (attrType attr)
				cptar = mkSimpleId $ translateType (attrType attr)
				mem = [	(memberRule attrt l (cp,y) (mkSimpleId "m")), 
					leftTotallityRule attrt l (cp,y),
					rightUniqueRule attrt l (cp,y) (mkSimpleId "z")]

defaultType :: ClassEntity -> Type
defaultType ce = Type{umltype = CE ce, typeOrdered = False, typeUnique = True}

translateProcedure :: Class -> Procedure -> [PHRASE]
translateProcedure cl proc = mem ++ (map (translateProperty proct l) l)
			where 	x = mkSimpleId $ getStringNotInList "x" paraNames
				y = mkSimpleId $ getStringNotInList "y" ((tokStr x):paraNames)
				l = case (procReturnType proc) of 
					Nothing -> [(c,x)] ++ (map (translateParameter) (procPara proc))
					Just ret -> [(c,x)] ++ (map (translateParameter) (procPara proc)) ++ [(mkSimpleId (translateType ret), y)] 
				mem = case (procReturnType proc) of
					Nothing -> []
					Just ret -> [	(memberRule proct l (mkSimpleId (translateType ret),y) (mkSimpleId $ getStringNotInList "m" ([(tokStr x)++(tokStr y)]++paraNames))),
							leftTotallityRule proct l (mkSimpleId (translateType ret),y),
							rightUniqueRule proct l (mkSimpleId (translateType ret),y) (mkSimpleId $ getStringNotInList "z" ([(tokStr x)++(tokStr y)]++paraNames))]
				paraNames = map attrName (procPara proc) 
				proct = mkSimpleId $ (className cl) ++ "." ++ (procName proc)
				c =  mkSimpleId $ translateType ctype
				ctype = Type{	umltype = CE $ CL cl,
						typeOrdered = False,
						typeUnique = True}

leftTotallityRule  :: Token -> [(Token,Token)] -> (Token, Token) -> PHRASE
leftTotallityRule c l (cz,z) = Sentence (Quant_sent Universal (map (\(a,b) -> Name b) (delete (cz,z) l)) (Quant_sent Existential [Name z] (typeFunction c (map snd l)) nullRange) nullRange)

translateCompLabel :: Association -> [PHRASE]
translateCompLabel ass = (foldl (++) [] $ map ((translateCompLabel1 (mkSimpleId $ assoName ass)).label) (ends ass))

translateCompLabel1 :: Token -> Label -> [PHRASE]
translateCompLabel1 r l = map (translateCompLabel2 r) $ case upperValue l of 
	"*" ->[(mkSimpleId "geq", mkSimpleId $ lowerValue l)] 	
	_ -> [(mkSimpleId "geq", mkSimpleId $ lowerValue l),(mkSimpleId "leq", mkSimpleId $ upperValue l)] 

translateCompLabel2 :: Token -> (Token, Token) -> PHRASE
translateCompLabel2 r (f, l)  = Sentence (Quant_sent Universal [Name x, Name y, Name n] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [ typeFunction r [x,y], typeFunction (mkSimpleId "form:sequence-length") [y,n]]) nullRange) (typeFunction f [l,n])) nullRange) nullRange) 
	where 
		x = mkSimpleId "x" 
		y = mkSimpleId "y" 
		n = mkSimpleId "n" 

translateAssoLabel :: Association -> [PHRASE]
translateAssoLabel ass = map (translateAssoLabel2 (mkSimpleId $ assoName ass) (zip endNames (map mkSimpleId classNames))) [(map (mkSimpleId.lowerValue.label) (ends ass),"min-card-tuple"), (map (mkSimpleId.upperValue.label) (ends ass),"max-card-tuple")]
			where 	endNames = map mkSimpleId $ generateNames ((assoName ass):classNames) (length classNames)
				classNames = (map (translateType.defaultType.endTarget) (ends ass))

translateAssoLabel2 :: Token -> [(Token,Token)] -> ([Token],String) -> PHRASE
translateAssoLabel2 a xcl (sels,f)=  Sentence (Quant_sent Universal (map (\(x,c)-> Name x) xcl) (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction (map (\(x,c) ->  typeFunction c [x]) xcl)) nullRange) (Atom_sent (Atom (Funct_term (Name_term $ mkSimpleId f) ((Term_seq $ Name_term a) : (map (\(x,c) -> Term_seq $ Name_term x) xcl)) nullRange) (map (\t -> Term_seq (Name_term $ t)) sels)) nullRange)) nullRange) nullRange)

rightUniqueRule ::  Token -> [(Token,Token)] -> (Token,Token) -> Token -> PHRASE
rightUniqueRule c l (cy,y) z = Sentence (Quant_sent Universal ((map (\(a,b) -> Name b) l) ++ [Name z]) (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [( (typeFunction c (map snd l))),((typeFunction c (((delete y (map snd l)) ++[z]))))]) nullRange) ((typeFunction (mkSimpleId "=") [y,z])) ) nullRange) nullRange)

memberRule :: Token -> [(Token,Token)] -> (Token, Token) -> Token -> PHRASE
memberRule c l (cy,y) m = Sentence (Quant_sent Universal (map (\(a,b) -> Name b) (l++[(m,m)])) (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [( (typeFunction c (map snd l))), (typeFunction (mkSimpleId "member") [m,y] )] ) nullRange ) ( (typeFunction cy [m])) ) nullRange) nullRange) 

translateParameter :: Attribute -> (Token, Token)
translateParameter at = ( mkSimpleId (translateType $ attrType at), mkSimpleId $ attrName at) 


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
translateProperty c l (cz,z) = Sentence (Quant_sent Universal (map (\(a,b) -> Name b) l) (Bool_sent (BinOp Implication ((typeFunction c (map snd l))) ( (typeFunction cz [z])) ) nullRange) nullRange)
				where applyType (t1,t2) = typeFunction t1 [t2] 

postamble :: [PHRASE]
postamble = [
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s1"),Name (mkSimpleId "s2"),Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s2")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "s1")) (Name_term (mkSimpleId "s2"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "s")] (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt2")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "buml:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt2")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt2")] (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt2")),Term_seq (Name_term (mkSimpleId "pt1"))]) nullRange]) nullRange) nullRange)) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt2"),Name (mkSimpleId "pt11"),Name (mkSimpleId "pt22")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt11")),Term_seq (Name_term (mkSimpleId "pt22"))]) nullRange]) nullRange) (Bool_sent (BinOp Biconditional (Atom_sent (Equation (Name_term (mkSimpleId "pt1")) (Name_term (mkSimpleId "pt11"))) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "pt2")) (Name_term (mkSimpleId "pt22"))) nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Bool_sent (BinOp Implication (Quant_sent Existential [Name (mkSimpleId "pt")] (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) nullRange) (Bool_sent (Junction Conjunction [Quant_sent Existential [Name (mkSimpleId "pt1")] (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt2")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange) nullRange,Quant_sent Existential [Name (mkSimpleId "pt2")] (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange) nullRange]) nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt11")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt2")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt2")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt11")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "pt1")) (Name_term (mkSimpleId "pt11"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "pt2")] (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt2"),Name (mkSimpleId "pt22")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt22"))]) nullRange) nullRange)) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "pt2")) (Name_term (mkSimpleId "pt22"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:empty-sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:empty-sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt")] (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) nullRange)) nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt"),Name (mkSimpleId "n")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "buml:UnlimtedNatural")) [Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt"),Name (mkSimpleId "n1"),Name (mkSimpleId "n2")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n2"))]) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "n1")) (Name_term (mkSimpleId "n2"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "n")] (Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt2")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt2")),Term_seq (Name_term (mkSimpleId "form:1"))]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "n1"),Name (mkSimpleId "pt2"),Name (mkSimpleId "n2")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "n1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt2")),Term_seq (Name_term (mkSimpleId "n2"))]) nullRange]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:add-one")) [Term_seq (Name_term (mkSimpleId "n1")),Term_seq (Name_term (mkSimpleId "n2"))]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "n")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:sequence-length")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "buml:UnlimtedNatural")) [Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "n")] (Bool_sent (BinOp 	Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:sequence-length")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange) (Bool_sent (Junction Disjunction [Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:empty-sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Equation (Name_term (mkSimpleId "n")) (Name_term (mkSimpleId "form:0"))) nullRange]) nullRange,Quant_sent Existential [Name (mkSimpleId "pt1")] (Bool_sent (Junction Conjunction [Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt2")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "pt"),Name (mkSimpleId "x")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "pt"),Name (mkSimpleId "x1"),Name (mkSimpleId "x2")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x2"))]) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "x1")) (Name_term (mkSimpleId "x2"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "x")] (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "n"),Name (mkSimpleId "x")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "n")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "buml:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:NaturalNumber")) [Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "n"),Name (mkSimpleId "x")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "n")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "pt")] (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s1"),Name (mkSimpleId "s2")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:same-sequence")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "s2"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s2"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s1"),Name (mkSimpleId "s2")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:same-sequence")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "s2"))]) nullRange) (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "n")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position-count")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "n")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position-count")) [Term_seq (Name_term (mkSimpleId "s2")),Term_seq (Name_term (mkSimpleId "n")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange)) nullRange) nullRange)) nullRange) nullRange), 
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s1"),Name (mkSimpleId "s2"),Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s2")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "s1")) (Name_term (mkSimpleId "s2"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "s")] (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt2")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "buml:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt2")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt2")] (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt2")),Term_seq (Name_term (mkSimpleId "pt1"))]) nullRange]) nullRange) nullRange)) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt2"),Name (mkSimpleId "pt11"),Name (mkSimpleId "pt22")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt11")),Term_seq (Name_term (mkSimpleId "pt22"))]) nullRange]) nullRange) (Bool_sent (BinOp Biconditional (Atom_sent (Equation (Name_term (mkSimpleId "pt1")) (Name_term (mkSimpleId "pt11"))) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "pt2")) (Name_term (mkSimpleId "pt22"))) nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Bool_sent (BinOp Implication (Quant_sent Existential [Name (mkSimpleId "pt")] (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) nullRange) (Bool_sent (Junction Conjunction [Quant_sent Existential [Name (mkSimpleId "pt1")] (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt2")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange) nullRange,Quant_sent Existential [Name (mkSimpleId "pt2")] (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange) nullRange]) nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "pt11")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt2")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt2")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt11")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "pt1")) (Name_term (mkSimpleId "pt11"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "pt2")] (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt2"),Name (mkSimpleId "pt22")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt22"))]) nullRange) nullRange)) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "pt2")) (Name_term (mkSimpleId "pt22"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:empty-sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:empty-sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange) (Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt")] (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) nullRange)) nullRange)) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt"),Name (mkSimpleId "n")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "buml:UnlimtedNatural")) [Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt"),Name (mkSimpleId "n1"),Name (mkSimpleId "n2")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n2"))]) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "n1")) (Name_term (mkSimpleId "n2"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "n")] (Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt2")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt1")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt2")),Term_seq (Name_term (mkSimpleId "form:1"))]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "pt1"),Name (mkSimpleId "n1"),Name (mkSimpleId "pt2"),Name (mkSimpleId "n2")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "n1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt2")),Term_seq (Name_term (mkSimpleId "n2"))]) nullRange]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:add-one")) [Term_seq (Name_term (mkSimpleId "n1")),Term_seq (Name_term (mkSimpleId "n2"))]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "n")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:sequence-length")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "buml:UnlimtedNatural")) [Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "n")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:sequence-length")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange) (Bool_sent (Junction Disjunction [Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:empty-sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Equation (Name_term (mkSimpleId "n")) (Name_term (mkSimpleId "form:0"))) nullRange]) nullRange,Quant_sent Existential [Name (mkSimpleId "pt1")] (Bool_sent (Junction Conjunction [Bool_sent (Negation (Quant_sent Existential [Name (mkSimpleId "pt2")] (Atom_sent (Atom (Name_term (mkSimpleId "form:before-in-sequence")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "pt2"))]) nullRange) nullRange)) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt1")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "pt"),Name (mkSimpleId "x")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "pt"),Name (mkSimpleId "x1"),Name (mkSimpleId "x2")] (Bool_sent (BinOp Implication (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x2"))]) nullRange]) nullRange) (Atom_sent (Equation (Name_term (mkSimpleId "x1")) (Name_term (mkSimpleId "x2"))) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "pt")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:Position")) [Term_seq (Name_term (mkSimpleId "pt"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "x")] (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "n"),Name (mkSimpleId "x")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "n")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "buml:Sequence")) [Term_seq (Name_term (mkSimpleId "s"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:NaturalNumber")) [Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s"),Name (mkSimpleId "n"),Name (mkSimpleId "x")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "n")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) (Quant_sent Existential [Name (mkSimpleId "pt")] (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:in-position")) [Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:position-count")) [Term_seq (Name_term (mkSimpleId "s")),Term_seq (Name_term (mkSimpleId "pt")),Term_seq (Name_term (mkSimpleId "n"))]) nullRange]) nullRange) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s1"),Name (mkSimpleId "s2")] (Bool_sent (BinOp Implication (Atom_sent (Atom (Name_term (mkSimpleId "form:same-sequence")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "s2"))]) nullRange) (Bool_sent (Junction Conjunction [Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s1"))]) nullRange,Atom_sent (Atom (Name_term (mkSimpleId "form:Sequence")) [Term_seq (Name_term (mkSimpleId "s2"))]) nullRange]) nullRange)) nullRange) nullRange),
	Sentence (Quant_sent Universal [Name (mkSimpleId "s1"),Name (mkSimpleId "s2")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:same-sequence")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "s2"))]) nullRange) (Quant_sent Universal [Name (mkSimpleId "x"),Name (mkSimpleId "n")] (Bool_sent (BinOp Biconditional (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position-count")) [Term_seq (Name_term (mkSimpleId "s1")),Term_seq (Name_term (mkSimpleId "n")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange) (Atom_sent (Atom (Name_term (mkSimpleId "form:in-position-count")) [Term_seq (Name_term (mkSimpleId "s2")),Term_seq (Name_term (mkSimpleId "n")),Term_seq (Name_term (mkSimpleId "x"))]) nullRange)) nullRange) nullRange)) nullRange) nullRange)]
