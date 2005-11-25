{-
The DevGraph-related structures that were first placed in OmdocHXT have
become more complex and as they have little in common with the abstract syntax
trees the functions have been extracted into this module.
Some redundancy was created so there should be a third module for common
functions...
-}
module OmdocDevGraph (module OmdocDevGraph, module Text.XML.HXT.Parser) where

-- XML processing is of course needed.
import Text.XML.HXT.Parser
import Text.XML.HXT.Arrow

-- once there were good reasons for these imports.
-- i still let them here if i run into trouble.
--import Omdoc_HXTAccess

--import CASL.Sign -- call ghc(i) with -i../..
--import CASL.Logic_CASL

--import qualified Common.Lib.Set as Set 
--import qualified Common.Lib.Map as Map 
--import qualified Common.Lib.Rel as Rel

-- For extracting the DevGraph and some CASL-specific funtions
--import qualified Hets as Hets
--import qualified HetsInterface as Hets

-- there is a need to check for certain strings
--import Char(isLower)

-- a shortcut to showXmlTrees
showXmlTreesNS::XmlTrees->String
showXmlTreesNS = flip showXmlTrees ""

-- this function is used to apply XmlFilters an XmlTrees
applyXmlFilter::XmlFilter->XmlTrees->XmlTrees
applyXmlFilter f t = (id .> f) t

typeS :: String
typeS = "type"
caslS :: String
caslS = "casl"
{-
createATP::String->(XmlTree->XmlTrees)
createATP typename =
	etag "OMATP" +=
		((etag "OMS" += ( sattr "cd" caslS +++ sattr "name" typeS ) )
		 +++ (etag "OMS" += ( sattr "cd" caslS +++ sattr "name" typename ) )
		 )
		 
createTypedVar::String->String->(XmlTree->XmlTrees)
createTypedVar typename varname =
	etag "OMATTR" += ( (createATP typename) +++ (etag "OMV" += (sattr "name" varname) ) )
-}	

{-
   Hets-Developement-Graph - first steps
-}

-- DGNodeLab = DGNode ... | DGRef ...

{-
Node as a theory.
DGNode = theory(name=name){ axiom*=dgn_sens oms*=dgn_sign }
name of node is name of theory
sentences go into axiom elements, signature is put in symbols
-> cd on this theory (?)

CASLSign = Sign () ()

data Sign f e = Sign { sortSet :: Set.Set SORT
               , sortRel :: Rel.Rel SORT         
               , opMap :: OpMap
               , assocOps :: OpMap
               , predMap :: Map.Map Id (Set.Set PredType)
               , varMap :: Map.Map SIMPLE_ID SORT
               , sentences :: [Named (FORMULA f)]        
               , envDiags :: [Diagnosis]
               , extendedInfo :: e
               } deriving Show

SORT = Id = Id [Token] [Id] [Pos] -- how to store this effective ?
type OpMap = Map.Map Id (Set.Set OpType)
data OpType = OpType {opKind :: FunKind, opArgs :: [SORT], opRes :: SORT} 
data FunKind = Total | Partial 
data Named s = NamedSen { senName  :: String,
                          sentence :: s }
			  
FORMULA -- see : HetsDataTypes.hs

sentences [OMOBJ]

OpMap -> [OMOBJ]

envDiags -- ignore (?)
extendedInfo -- not for CASL

toList sortSet -> [SORT]
toList sortRel -> [SORT, SORT]
toList OpMap -> [Id, OpType]

<theory name=dng_name>
  <definition>
    <requation>
      <pattern><value>
    </requation>
  </definition>
  -- sign
  <theory name="signature_sortSet">
    ...
    <type name="_SORT_TOKEN_" system="?"> -- system required, OMOBJ+
      <OMOBJ><OMS name="_SORT_TOKEN_" cd="CASL"/></OMOBJ>
    </type>
    ...
  </theory>
  <theory name="signature_sortRel">
    ...
    <type name="_REL_TOKEN_1_" system="?">
      <OMOBJ><OMS name="_REL_TOKEN_2_"/></OMBJ>
    </type>
    ...
  </theory>
</theory>

from CASL/test/X1.casl

1:DGNode {
	dgn_name = (spec,"",0),
	dgn_sign = Sign {
		sortSet = {Int,Nat},
		sortRel = {(Nat,Int)},
		opMap = {0:={OpType {opKind = Total, opArgs = [], opRes = Int},OpType {opKind = Total, opArgs = [], opRes = Nat}},__-?__:={OpType {opKind = Partial, opArgs = [Int,Int], opRes = Int},OpType {opKind = Partial, opArgs = [Nat,Nat], opRes = Nat}}},
		assocOps = {},
		predMap = {},
		varMap = {},
		sentences = [],
		envDiags = [],
		extendedInfo = ()},
	dgn_sens = [NamedSen {senName = "Nat_divide_0", sentence = Definedness (Application (Qual_op_name 0 (Op_type Total [] Nat []) []) [] []) [CASL/test/X1.casl:9.8]}],
	dgn_nf = Nothing, dgn_sigma = Nothing, dgn_origin = DGBasic
	}->[]
	
G_sign _ sign -> Logic -> Sentences -> Category -> (Eq sign) -- sign only needs to be of class Eq...

-}
{-
testSign = Sign {
		sortSet = [Int,Nat],
		sortRel = [(Nat,Int)],
		opMap = [("0",[OpType {opKind = Total, opArgs = [], opRes = Int},OpType {opKind = Total, opArgs = [], opRes = Nat}],
			("__-?__",[OpType {opKind = Partial, opArgs = [Int,Int], opRes = Int},OpType {opKind = Partial, opArgs = [Nat,Nat], opRes = Nat}]],
		assocOps = [],
		predMap = [],
		varMap = [],
		sentences = [],
		envDiags = [],
		extendedInfo = ()}
-}
{-
sortSimulation::[String]->XmlTrees
sortSimulation sl = let t = etag "theory" += sattr "id" "signature_SortSet"
	in if (length sl) > 0 then (t += (txt "\n" +++ (sortSimulation' sl)) +++ txt "\n") emptyRoot else (t +++  txt "\n") emptyRoot where
	sortSimulation' [s] = (createTag s)
	sortSimulation' (s:sl) = (createTag s) +++ (sortSimulation' sl) 
	createTag s = etag "type" += (sattr "id" s +++ sattr "system" caslS ) += txt "\n" +=
		(etag "OMOBJ" += (etag "OMS" += sattr "name" s)) +++ txt "\n"
		
sortRelSimulation::[(String, String)]->XmlTrees
sortRelSimulation sl = let t = etag "theory" += sattr "id" "signature_SortRel"
	in if (length sl) > 0 then (t += (txt "\n" +++ (sortRelSimulation' sl)) +++ txt "\n") emptyRoot else (t +++ txt "\n") emptyRoot where
	sortRelSimulation' [s] = (createTag s)
	sortRelSimulation' (s:sl) = (createTag s) +++ (sortRelSimulation' sl)
	createTag (t, tv) = etag "type" += (sattr "id" t +++ sattr "system" caslS) += txt "\n" +=
		(etag "OMOBJ" += (etag "OMS" += sattr "name" tv)) +++ txt "\n"

-- Embed XmlTrees in a theory-tag		
embedInTheory::String->[XmlTrees]->XmlTrees
embedInTheory name trees =
	let theory = (((etag "theory" += sattr "id" name) += txt "\n") +++ txt "\n") emptyRoot in
		foldr (\t ((NTree a l):x) -> ((NTree a ((txt "\n" emptyRoot)++t++l)):x) ) theory trees

-- sort(list) to OmDOC Symbols. Symbols are must be enclosed in (not exclusive)
-- theories.
sortSetToXmlTrees::[String]->XmlTrees
sortSetToXmlTrees sl = 
	embedInTheory "signature_SortSet" $ map (\a -> (createTag a) emptyRoot) sl where
	createTag s = (etag "symbol" += sattr "kind" typeS += sattr "id" s) 

sortSetToXmlTreesU::String->[String]->XmlTrees
sortSetToXmlTreesU u sl = 
	embedInTheory ("signature_SortSet"++":"++u) $ map (\a -> (createTag a) emptyRoot) sl where
	createTag s = (etag "symbol" += sattr "kind" typeS += sattr "id" s)
	
sortSetToXmlTrees2::[String]->(XmlTree->XmlTrees)
sortSetToXmlTrees2 sorts =
	foldl (\sortsX sort ->
		sortsX +++ (etag "symbol" += (sattr "name" sort +++ sattr "kind" "sort")) +++ txt "\n") (txt "") sorts
	
sortRelToXmlTrees::[(String, String)]->XmlTrees
sortRelToXmlTrees sl =
	embedInTheory "signature_SortRel" $ map (\a -> (createTag a) emptyRoot) sl where  
	createTag (s,r) = (etag "symbol" += sattr "kind" "object" += sattr "id" ("g__inj"++s++r))
	
sortRelToXmlTreesU::String->[(String, String)]->XmlTrees
sortRelToXmlTreesU u sl =
	embedInTheory ("signature_SortRel"++":"++u) $ map (\a -> (createTag a) emptyRoot) sl where  
	createTag (s,r) = (etag "symbol" += sattr "kind" "object" += sattr "id" ("g__inj"++s++r))
	
sortRelToXmlTrees2::[(String, String)]->(XmlTree->XmlTrees)
sortRelToXmlTrees2 rels =
	foldl (\relsX (s1,s2) ->
		relsX +++ (etag "symbol" += (sattr "name" ("g__inj"++s1++s2) +++ sattr "kind" "sort")) +++ txt "\n") (txt "") rels 
	
-- opMap is a list of token with a set of (kind, [args] and result)
{-
<theory...>
	<symbol kind="object" name="opname">
		<type name="partial/total"> -- FunKind total/partial
			<OMOBJ>
			  <OMATTR>
			  <OMATP>
			     <OMA cd="CASL" name="opname">
			       <OMV name="args1">
			       .
			       .
			       <OMV name "argsn">
			     </OMA>
			     <OMV name="res">
			   </OMATP>
			</OMOBJ>
		</selector>
	</symbol>
</theory>

ATTRIBUTE ((BIND opname ATTRIBUTE(args) ATTRIBUTE(result)) optype)

<symbol kind="object" name="opname">
  <type name="partial/total">
    <OMOBJ>
      <OMBIND>
        <OMS cd=CASL name="opname">
          <OMBVAR>
            <OMATTR><OMS cd=CASL name="typ1"><OMV name="a1"></OMATTR>
            .
            .
            <OMATTR><OMS cd=CASL name="typn"><OMV name="an"></OMATTR>
          </OMBVAR>
        <OMATTR>
          <OMS cd=CASL name="restype">
          <OMV name="result">
        </OMATTR>
      </OMBIND>
    </OMOBJ>
  </type>
</symbol>
-}

getSortSymbols::XmlFilter
getSortSymbols = isTag "symbol" .> withSValue "type" "sort" .> withValue "name" (\s -> (hasSPrefix "g__inj" s) == False)

getSortRelSymbols::XmlFilter
getSortRelSymbols = isTag "symbol" .> withSValue "type" "sort" .> withValue "name" (\s -> (hasSPrefix "g__inj" s) == True)

-- Finding out, wether a symbol is an operator, can be done by checking for 
-- the first OMS in the OMA...
getOpMapSymbols::XmlFilter
getOpMapSymbols t = if (applyXmlFilter (
		isTag "symbol"
		.> withSValue "kind" "object"
		.> getChildren .> isTag "type" .> withSValue "system" caslS
		.> getChildren .> isTag "OMOBJ"
		.> getChildren .> isTag "OMA"
		.> getChildren .> isTag "OMS" .> withSValue "cd" caslS .> withSValue "name" "funtype") [t]) /= [] then [t] else [] 
	
-- same for predication
getPredMapSymbols::XmlFilter
getPredMapSymbols t = if (applyXmlFilter (
		isTag "symbol"
		.> withSValue "kind" "object"
		.> getChildren .> isTag "type" .> withSValue "system" caslS
		.> getChildren .> isTag "OMOBJ"
		.> getChildren .> isTag "OMA"
		.> getChildren .> isTag "OMS" .> withSValue "cd" caslS .> withSValue "name" "predication") [t]) /= [] then [t] else [] 

-- We need to produce symbols for each operator
-- For overloading, new Symbols have to be generated and must be collected later
-- <symbol name="opname_uniqe" kind="object">
-- <type system="casl"> <OMOBJ> <OMA> <OMS cd="casl" name="funtype"> <OMS cd=..theory.. name=SORT> ... <OMS cd=..theory.. name=RES>
opMapWithOverloadingToXmlTrees::String->[(String, [(String, [String], String)])]->(XmlTree->XmlTrees)
opMapWithOverloadingToXmlTrees theory =
	foldl (\opX (name, overloads) ->
		opX +++
		if length(overloads) == 1 then
			createOperatorSymbol theory name (overloads!!0)
			else
			foldl (\ovs o ->
				ovs
				+++  (createOperatorSymbol theory (createOverloadedName name o) o)
				+++ (txt "\n")
				) (txt "") overloads
		) (txt "") 
	--where
	
createOperatorSymbol::String->String->(String, [String], String)->(XmlTree->XmlTrees)
createOperatorSymbol theory name (funtype, args, res) =
		(etag "symbol" += (
			sattr "name" name
			+++ sattr "kind" "object"
			+++ (etag "type" += (
				sattr "system" caslS
				+++ etag "OMOBJ" += (
					etag "OMA" += (
						(etag "OMS" += (sattr "cd" caslS +++ sattr "name" "funtype"))
						+++ foldl (\argsX a ->
							argsX
							+++ (etag "OMS" += (sattr "cd" theory +++ sattr "name" a))
							+++ txt "\n"
						) (txt "") args
						+++ (etag "OMS" += (sattr "cd" theory +++ sattr "name" res))
					)
				)
			)
			)
		))
		+++ txt "\n"
createOverloadedName::String->(String, [String], String)->String
createOverloadedName name (funtype, args, res) =
		name ++ ":" ++ funtype ++ ":" ++ (foldl (\argsS a -> argsS ++ a ++ ":") "" args) ++ res
	

opMapToXmlTrees::[(String, [(String, [String], String)])]->XmlTrees
opMapToXmlTrees (opnames) =
	embedInTheory "signature_OpMap"
	[((foldr (\t f -> t +++ f) (txt "") (map opMapToXmlTrees' opnames)) emptyRoot)] 
	where
	opMapToXmlTrees' ::(String, [(String, [String], String)])->(XmlTree->XmlTrees)
	opMapToXmlTrees' (opName, kinds) =
		(foldr (\t f -> t +++ txt "\n" +++ f) (txt "") (map opMapToXmlTrees'' (map (\x -> (opName, x)) kinds)))
	opMapToXmlTrees'' ::(String, (String, [String], String))->(XmlTree->XmlTrees)
	opMapToXmlTrees'' (opName, (opKind, opArgs, opRes)) =
		etag "type" += (sattr "id" opKind +++ sattr "system" caslS)
		 += (
		   -- type-begin
		       txt "\n"
		   +++ etag "OMOBJ"
		         += (
			   -- OMOBJ-begin
			       txt "\n"
			   +++ etag "OMBIND"
				 += (
				   -- OMBIND-begin
				       txt "\n"
				   +++ (etag "OMS" += sattr "cd" caslS += sattr "name" opName)
				   +++ (txt "\n")
				   +++ (etag "OMBVAR"
				     += (
				       -- OMBVAR-begin
				           txt "\n"
				       +++
				       (if opArgs == [] then 
				          etag "OMV" += sattr "name" "no-args"
					else
					  (opArgsToXmlTrees opArgs 1)
				        )
				       -- OMBVAR-end
				     )
				   )
				   +++ (txt "\n")
{-				   +++ (etag "OMATTR"
				     += (
				       -- OMATTR-begin
				       (etag "OMS" += sattr "cd" "CASL" += sattr "name" opRes)
				       +++ (etag "OMV" += sattr "name" "result")
				       -- OMATTR-end
				     )
				   )-}
				   +++ ( createTypedVar opRes "result" )
				   +++ txt "\n"
				   -- OMBIND-end
				)
			   +++ txt "\n"
			   -- OMOBJ-end
			 )
		   +++ txt "\n"
		   -- type-end
		 )
		    
	opArgsToXmlTrees::[String]->Int->(XmlTree->XmlTrees)
	opArgsToXmlTrees [] _ = txt ""
	opArgsToXmlTrees (s:xs) n =
		(createTypedVar s ("a" ++ (show n)))+++(txt "\n")+++(opArgsToXmlTrees xs (n+1))

opMapToXmlTreesU::String->[(String, [(String, [String], String)])]->XmlTrees
opMapToXmlTreesU u (opnames) =
	embedInTheory ("signature_OpMap"++":"++u)
	[((foldr (\t f -> t +++ f) (txt "") (map opMapToXmlTrees' opnames)) emptyRoot)] 
	where
	opMapToXmlTrees' ::(String, [(String, [String], String)])->(XmlTree->XmlTrees)
	opMapToXmlTrees' (opName, kinds) =
		(foldr (\t f -> t +++ txt "\n" +++ f) (txt "") (map opMapToXmlTrees'' (map (\x -> (opName, x)) kinds)))
	opMapToXmlTrees'' ::(String, (String, [String], String))->(XmlTree->XmlTrees)
	opMapToXmlTrees'' (opName, (opKind, opArgs, opRes)) =
		etag "type" += (sattr "id" opKind +++ sattr "system" caslS)
		 += (
		   -- type-begin
		       txt "\n"
		   +++ etag "OMOBJ"
		         += (
			   -- OMOBJ-begin
			       txt "\n"
			   +++ etag "OMBIND"
				 += (
				   -- OMBIND-begin
				       txt "\n"
				   +++ (etag "OMS" += sattr "cd" caslS += sattr "name" opName)
				   +++ (txt "\n")
				   +++ (etag "OMBVAR"
				     += (
				       -- OMBVAR-begin
				           txt "\n"
				       +++
				       (if opArgs == [] then 
				          etag "OMV" += sattr "name" "no-args"
					else
					  (opArgsToXmlTrees opArgs 1)
				        )
				       -- OMBVAR-end
				     )
				   )
				   +++ (txt "\n")
{-				   +++ (etag "OMATTR"
				     += (
				       -- OMATTR-begin
				       (etag "OMS" += sattr "cd" "CASL" += sattr "name" opRes)
				       +++ (etag "OMV" += sattr "name" "result")
				       -- OMATTR-end
				     )
				   )-}
				   +++ ( createTypedVar opRes "result" )
				   +++ txt "\n"
				   -- OMBIND-end
				)
			   +++ txt "\n"
			   -- OMOBJ-end
			 )
		   +++ txt "\n"
		   -- type-end
		 )
		 
	opArgsToXmlTrees::[String]->Int->(XmlTree->XmlTrees)
	opArgsToXmlTrees [] _ = txt ""
	opArgsToXmlTrees (s:xs) n =
		(createTypedVar s ("a" ++ (show n)))+++(txt "\n")+++(opArgsToXmlTrees xs (n+1))
		
{-
<symbol kind="object" name="predicate">
  <type system="CASL">
    <OMOBJ>
      <OMBIND>
        <OMS cd=CASL name="predname">
          <OMBVAR>
            <OMATTR><OMS cd=CASL name="typ1"><OMV name="a1"></OMATTR>
            .
            .
            <OMATTR><OMS cd=CASL name="typn"><OMV name="an"></OMATTR>
          </OMBVAR>
        <OMATTR>
          <OMS cd=CASL name="restype">
          <OMV name="result">
        </OMATTR>
      </OMBIND>
    </OMOBJ>
  </type>
</symbol>
-}
predMapWithOverloadingToXmlTrees::String->[(String, [[String]])]->(XmlTree->XmlTrees)
predMapWithOverloadingToXmlTrees theory =
	foldl (\predX (name, overloads) ->
		predX +++
		if length(overloads) == 1 then
			createPredicationSymbol theory name (overloads!!0)
			else
			foldl (\ovs o ->
				ovs
				+++  (createPredicationSymbol theory (createOverloadedPredName name o) o)
				+++ (txt "\n")
				) (txt "") overloads
		) (txt "") 
	--where
	
createPredicationSymbol::String->String->[String]->(XmlTree->XmlTrees)
createPredicationSymbol theory name args =
		(etag "symbol" += (
			sattr "name" name
			+++ sattr "kind" "object"
			+++ (etag "type" += (
				sattr "system" caslS
				+++ etag "OMOBJ" += (
					etag "OMA" += (
						(etag "OMS" += (sattr "cd" caslS +++ sattr "name" "predication"))
						+++ foldl (\argsX a ->
							argsX
							+++ (etag "OMS" += (sattr "cd" theory +++ sattr "name" a))
							+++ txt "\n"
						) (txt "") args
					)
				)
			)
			)
		))
		+++ txt "\n"
createOverloadedPredName::String->[String]->String
createOverloadedPredName name args =
		name ++ (foldl (\argsS a -> argsS ++ ":" ++ a) "" args)
	

-- This XML-Conversion is not very good... How to express predicates in OMDoc ?
predMapToXmlTrees::[(String, [[String]])]->XmlTrees
predMapToXmlTrees (prednames) =
	embedInTheory "signature_PredMap"
	[((foldr (\t f -> t +++ f) (txt "") (map predMapToXmlTrees' prednames)) emptyRoot)] 
	where
	predMapToXmlTrees' ::(String, [[String]])->(XmlTree->XmlTrees)
	predMapToXmlTrees' (predName, arglist) =
		(foldr (\t f -> t +++ txt "\n" +++ f) (txt "") (map predMapToXmlTrees'' (map (\x -> (predName, x)) arglist)))
	predMapToXmlTrees'' ::(String, [String])->(XmlTree->XmlTrees)
	predMapToXmlTrees'' (predName, predArgs) =
		etag "type" += (sattr "id" predName +++ sattr "system" caslS)
		 += (
		   -- type-begin
		       txt "\n"
		   +++ etag "OMOBJ"
		         += (
			   -- OMOBJ-begin
			       txt "\n"
			   +++ etag "OMBIND"
				 += (
				   -- OMBIND-begin
				       txt "\n"
				   +++ (etag "OMS" += sattr "cd" caslS += sattr "name" predName)
				   +++ (txt "\n")
				   +++ (etag "OMBVAR"
				     += (
				       -- OMBVAR-begin
				           txt "\n"
				       +++
				       (if predArgs == [] then
				       	  etag "OMV" += sattr "name" "no-args"
					else
					(predArgsToXmlTrees predArgs 1)
				       )
				       -- OMBVAR-end
				     )
				   )
				   +++ (txt "\n")
				   +++ (createTypedVar "Bool" "result")
				   +++ txt "\n"
				   -- OMBIND-end
				)
			   +++ txt "\n"
			   -- OMOBJ-end
			 )
		   +++ txt "\n"
		   -- type-end
		 )
		    
	predArgsToXmlTrees::[String]->Int->(XmlTree->XmlTrees)
	predArgsToXmlTrees [] _ = txt ""
	predArgsToXmlTrees (s:xs) n =
		(createTypedVar s ("a"++(show n)))+++(txt "\n")+++(predArgsToXmlTrees xs (n+1))
		
-- This XML-Conversion is not very good... How to express predicates in OMDoc ?
predMapToXmlTreesU::String->[(String, [[String]])]->XmlTrees
predMapToXmlTreesU u (prednames) =
	embedInTheory ("signature_PredMap"++":"++u)
	[((foldr (\t f -> t +++ f) (txt "") (map predMapToXmlTrees' prednames)) emptyRoot)] 
	where
	predMapToXmlTrees' ::(String, [[String]])->(XmlTree->XmlTrees)
	predMapToXmlTrees' (predName, arglist) =
		(foldr (\t f -> t +++ txt "\n" +++ f) (txt "") (map predMapToXmlTrees'' (map (\x -> (predName, x)) arglist)))
	predMapToXmlTrees'' ::(String, [String])->(XmlTree->XmlTrees)
	predMapToXmlTrees'' (predName, predArgs) =
		etag "type" += (sattr "id" predName +++ sattr "system" caslS)
		 += (
		   -- type-begin
		       txt "\n"
		   +++ etag "OMOBJ"
		         += (
			   -- OMOBJ-begin
			       txt "\n"
			   +++ etag "OMBIND"
				 += (
				   -- OMBIND-begin
				       txt "\n"
				   +++ (etag "OMS" += sattr "cd" caslS += sattr "name" predName)
				   +++ (txt "\n")
				   +++ (etag "OMBVAR"
				     += (
				       -- OMBVAR-begin
				           txt "\n"
				       +++
				       (if predArgs == [] then
				       	  etag "OMV" += sattr "name" "no-args"
					else
					(predArgsToXmlTrees predArgs 1)
				       )
				       -- OMBVAR-end
				     )
				   )
				   +++ (txt "\n")
				   +++ (createTypedVar "Bool" "result")
				   +++ txt "\n"
				   -- OMBIND-end
				)
			   +++ txt "\n"
			   -- OMOBJ-end
			 )
		   +++ txt "\n"
		   -- type-end
		 )

	predArgsToXmlTrees::[String]->Int->(XmlTree->XmlTrees)
	predArgsToXmlTrees [] _ = txt ""
	predArgsToXmlTrees (s:xs) n =
		(createTypedVar s ("a"++(show n)))+++(txt "\n")+++(predArgsToXmlTrees xs (n+1))
		
-- Transformation to XML
caslSignToXmlTrees::Hets.CASLSignStrings->XmlTrees
caslSignToXmlTrees css = embedInTheory "signature"
			[ 	 sortSetToXmlTrees $ Hets.sortSetStrings css
				,sortRelToXmlTrees $ Hets.sortRelStrings css
				,opMapToXmlTrees $ Hets.opMapStrings css
				,predMapToXmlTrees $ Hets.predMapStrings css
			]
			
-- Transformation to XML (unique)
caslSignToXmlTreesU::String->Hets.CASLSignStrings->XmlTrees
caslSignToXmlTreesU u css = embedInTheory ("signature"++":"++u)
			[ 	 sortSetToXmlTreesU u $ Hets.sortSetStrings css
				,sortRelToXmlTreesU u $ Hets.sortRelStrings css
				,opMapToXmlTreesU u $ Hets.opMapStrings css
				,predMapToXmlTreesU u $ Hets.predMapStrings css
			]
			
-- ...and back...

-- xmlTreesToCASLSign::XmlTrees->(Maybe CASLSign)

isAPrefix::String->String->Bool
isAPrefix [] _ = True
isAPrefix _ [] = False
isAPrefix (a:x) (b:y) = (a == b) && isAPrefix x y
-}
-- XMLFilter hasValue only gives back the value, not the tree...
withValue::String->(String -> Bool)->XmlFilter
withValue s f t = if (hasValue s f t) /= [] then [t] else []

withQualValue::String->String->(String->Bool)->XmlFilter
withQualValue "" local test t = withValue local test t
withQualValue prefix local test t =
	if withValue (prefix++":"++local) test t /= []
		then
			[t]
		else
			if withValue local test t /= []
				then
					[t]
				else
					[]

-- shortcut
withSValue::String->String->XmlFilter
withSValue a v = withValue a (==v)

withQualSValue::String->String->String->XmlFilter
withQualSValue prefix local v = withQualValue prefix local (==v)

{-
-- Extract the sort-set from the signature (as XML)
getSortSetTree::XmlTrees->XmlTrees
getSortSetTree t = applyXmlFilter (getChildren .> isTag "theory" .> withValue "id" (isAPrefix "signature_SortSet")) t

-- Build the string-sort-set from XML
getSortSet::XmlTrees->[String]
getSortSet t = map (\s -> xshow (applyXmlFilter (getValue "id") [s]) ) ((applyXmlFilter (getChildren .> isTag "symbol" .> withSValue "kind" typeS) t)::[XmlTree])

-- Just like sort-set
getSortRelTree::XmlTrees->XmlTrees
getSortRelTree t = applyXmlFilter (getChildren .> isTag "theory" .> withValue "id" (isAPrefix "signature_SortRel")) t

hasSPrefix::String->String->Bool
hasSPrefix p s = (take (length p) s) == p

getSortRel::XmlTrees->[(String, String)]
getSortRel t = map (\s -> makeTupel $ drop 6 (xshow (applyXmlFilter (getValue "id") [s])) )
	((applyXmlFilter (getChildren .> isTag "symbol" .> withSValue "kind" "object" .> withValue "id" (hasSPrefix "g__inj")) t)::[XmlTree])
	where
	makeTupel::String->(String, String)
	makeTupel (c:xs) = ([c]++takeWhile Char.isLower xs, dropWhile Char.isLower xs) 
	
getOpMapTree::XmlTrees->XmlTrees
getOpMapTree t = applyXmlFilter (getChildren .> isTag "theory" .> withValue "id" (isAPrefix "signature_OpMap")) t

getOpMap::XmlTrees->[(String, [(String, [String], String)])]
getOpMap t = foldl (\ops x -> insertOp (makeOp [x]) ops) [] $ getOps t where
	insertOp::(String, (String, [String], String))->[(String, [(String, [String], String)])]->[(String, [(String, [String], String)])]
	insertOp (opName, t) [] = [(opName, [t])]
	insertOp (opName, t) ((opName' , l):rest) = if opName == opName' then (opName, l++[t]):rest else (opName' , l):(insertOp (opName, t) rest) 
	makeOp::XmlTrees->(String, (String, [String], String))
	makeOp t = let	
		opTypeS = xshow $ applyXmlFilter (isTag "type" .> getValue "id") t
		opNameS = xshow $ applyXmlFilter (getChildren .> isTag "OMOBJ" .> getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMS" .> withSValue "cd" caslS .> getValue "name") t
		opArgsS = getAttr $ applyXmlFilter (getChildren .> isTag "OMOBJ" .> getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMBVAR") t
		opResS = xshow $ applyXmlFilter (getChildren .> isTag "OMOBJ" .> getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withSValue "cd" caslS .> withValue "name" (/=typeS) .> getValue "name") t
		in (opNameS, (opTypeS, opArgsS, opResS))
	getOps::XmlTrees->XmlTrees
	getOps t = applyXmlFilter (getChildren .> isTag "type") t
	getAttr::XmlTrees->[String]
	getAttr t = map (\x -> xshow ([x]::XmlTrees)) ((applyXmlFilter (getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withSValue "cd" caslS .> withValue "name" (/=typeS) .> getValue "name") t)::[XmlTree])

getPredMapTree::XmlTrees->XmlTrees
getPredMapTree t = applyXmlFilter (getChildren .> isTag "theory" .> withValue "id" (isAPrefix "signature_PredMap")) t

getPredMap::XmlTrees->[(String, [[String]])]
getPredMap t = foldl (\preds x -> insertPred (makePred [x]) preds) [] $ getPreds t where
	insertPred::(String, [String])->[(String, [[String]])]->[(String, [[String]])]
	insertPred (prName, a) [] = [(prName, [a])]
	insertPred (prName, a) ((prName', l):rest) = if prName == prName' then (prName, l++[a]):rest else (prName' , l):(insertPred (prName, a) rest)
	makePred::XmlTrees->(String, [String])
	makePred t = let
		prNameS = xshow $ applyXmlFilter (isTag "type" .> getChildren .> isTag "OMOBJ" .> getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMS"
			.> withSValue "cd" caslS .> getValue "name") t
		prAttrS = getAttr $ applyXmlFilter (getChildren .> isTag "OMOBJ" .> getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMBVAR") t
		in (prNameS, prAttrS)
	getPreds::XmlTrees->XmlTrees
	getPreds t = applyXmlFilter (getChildren .> isTag "type") t
	getAttr::XmlTrees->[String]
	getAttr t = map (\x -> xshow ([x]::XmlTrees)) ((applyXmlFilter (getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withSValue "cd" caslS .> withValue "name" (/=typeS) .> getValue "name") t)::[XmlTree])

{-
data QUANTIFIER = Universal | Existential | Unique_existential
data PRED_SYMB = Pred_name PRED_NAME  -- OmDoc: similar to OP_SYMB
	       | Qual_pred_name PRED_NAME PRED_TYPE [Pos]
data TERM f = Simple_id SIMPLE_ID    -- "Var" might be a better constructor
                      -- OmDoc: not needed
	  | Qual_var VAR SORT [Pos]    -- OmDoc: OMV. Type of var?
	    -- pos: "(", var, colon, ")"
	  | Application OP_SYMB [TERM f] [Pos]  -- OmDoc: OMA
	    -- pos: parens around TERM f if any and seperating commas
	  | Sorted_term (TERM f) SORT [Pos] -- OmDoc: ignore
	    -- pos: colon
	  | Cast (TERM f) SORT [Pos] -- OmDoc: application of special symbol PROJ
	    -- pos: "as"
	  | Conditional (TERM f) (FORMULA f) (TERM f) [Pos]
data FORMULA f = Quantification QUANTIFIER [VAR_DECL] (FORMULA f) [Pos]
	       -- pos: QUANTIFIER, semi colons, dot
	     | Conjunction [FORMULA f] [Pos]
	       -- pos: "/\"s
	     | Disjunction [FORMULA f] [Pos]
	       -- pos: "\/"s
	     | Implication (FORMULA f) (FORMULA f) Bool [Pos]
	       -- pos: "=>" or "if" (True -> "=>")	   
	     | Equivalence (FORMULA f) (FORMULA f) [Pos]
	       -- pos: "<=>"
	     | Negation (FORMULA f) [Pos]
	       -- pos: not
	     | True_atom [Pos]
	       -- pos: true	    
	     | False_atom [Pos]
               -- pos: false
	     | Predication PRED_SYMB [TERM f] [Pos]
               -- pos: opt. "(",commas,")"
	     | Definedness (TERM f) [Pos]
	       -- pos: def
	     | Existl_equation (TERM f) (TERM f) [Pos]
               -- pos: =e=
	     | Strong_equation (TERM f) (TERM f) [Pos]
	       -- pos: =
	     | Membership (TERM f) SORT [Pos]
               -- pos: in
	     | Mixfix_formula (TERM f)  -- Mixfix_ Term/Token/(..)/[..]/{..}
	     -- a formula left original for mixfix analysis  -- OmDoc: not needed
	     | Unparsed_formula String [Pos]
	       -- pos: first Char in String   -- OmDoc: not needed
	     | Sort_gen_ax [Constraint] Bool -- flag: belongs to a free type?
	     | ExtFORMULA f
             -- needed for CASL extensions
-}
-- f@CASL = ()
-- recursive tree generation needed...

-- > integrate.hs

	
{-getSetStringList::(Show a)=>Set.Set a -> [String]
getSetStringList s = map show $ Set.toList s

getMapStringsList::(Show a, Show b)=>Map.Map a b -> [(String, String)]
getMapStringsList s = map (\(a, b) -> (show a, show b)) $ Map.toList s

getRelStringsList::(Show a)=>Rel.Rel a -> [(String, String)]
getRelStringsList s = map (\(a, b) -> (show a, show b)) $ Rel.toList s
		
caslSignSortsToString::CASLSign->String
caslSignSortsToString s = xshow $ sortSimulation $ getSetStringList $ sortSet s-}

{- nodeToOmdoc::DGNodeLab->XmlTrees
nodeToOmdoc DGNode {  dgn_name = dgn_name
		     ,dgn_sign = dgn_sign
		     ,dgn_sens = dgn_sens
		     ,dgn_nf = dgn_nf -- ?
		     ,dgn_sigma = dgn_sigma -- ?
		     ,dgn_origin = dgn_origin -- ?
		   } =
-}

-}
