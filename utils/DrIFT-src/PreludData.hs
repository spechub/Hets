module PreludData where

import DataP
-- data types from prelude, so we can derive things for these
-- as needed without parsing the whole prelude

-- users may want to add commonly-used datatypes to this list, to save
-- repeatedly searching for a type.  The list data is generated using the 
-- 'test' rule on the required datatypes.

preludeData :: [Data]
preludeData = [
	D{name="Bool",constraints=[],vars=[],body=[
		Body{constructor="False",labels=[],types=[]},
		Body{constructor="True",labels=[],types=[]}] 
	,derives=["Eq", "Ord", "Ix", "Enum", "Read", "Show", "Bounded"]
	,statement=DataStmt}, 
	D{name="Maybe",constraints=[],vars=["a"],body=[
		Body{constructor="Just",labels=[],types=[Var "a"]},
		Body{constructor="Nothing",labels=[],types=[]}] ,
	derives=["Eq", "Ord", "Read", "Show"],statement=DataStmt},
	D{name="Either",constraints=[],vars=["a", "b"],body=[
		Body{constructor="Left",labels=[],types=[Var "a"]},
		Body{constructor="Right",labels=[],types=[Var "b"]}],
        derives=["Eq", "Ord", "Read", "Show"],statement=DataStmt}, 
	D{name="Ordering",constraints=[],vars=[],body=[
		Body{constructor="LT",labels=[],types=[]},
		Body{constructor="EQ",labels=[],types=[]}, 
		Body{constructor="GT",labels=[],types=[]}],
	derives=["Eq", "Ord", "Ix", "Enum", "Read", "Show", "Bounded"],
	statement=DataStmt}]
