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
		Body{constructor="False",labels=[],types=[],
		    aterm_constructor=Const "False" Args},
		Body{constructor="True",labels=[],types=[],
		    aterm_constructor=Const "True" Args}] 
	,derives=["Eq", "Ord", "Ix", "Enum", "Read", "Show", "Bounded"]
	,statement=DataStmt}, 
	D{name="Maybe",constraints=[],vars=["a"],body=[
		Body{constructor="Just",labels=[],types=[Var "a"],
		    aterm_constructor=Const "Just" Args},
		Body{constructor="Nothing",labels=[],types=[],
		    aterm_constructor=Const "Nothing" Args}] ,
	derives=["Eq", "Ord", "Read", "Show"],statement=DataStmt},
	D{name="Either",constraints=[],vars=["a", "b"],body=[
		Body{constructor="Left",labels=[],types=[Var "a"],
		    aterm_constructor=Const "Left" Args},
		Body{constructor="Right",labels=[],types=[Var "b"],
		    aterm_constructor=Const "Right" Args}],
        derives=["Eq", "Ord", "Read", "Show"],statement=DataStmt}, 
	D{name="Ordering",constraints=[],vars=[],body=[
		Body{constructor="LT",labels=[],types=[],
		    aterm_constructor=Const "LT" Args},
		Body{constructor="EQ",labels=[],types=[],
		    aterm_constructor=Const "EQ" Args}, 
		Body{constructor="GT",labels=[],types=[],
		    aterm_constructor=Const "GT" Args}],
	derives=["Eq", "Ord", "Ix", "Enum", "Read", "Show", "Bounded"],
	statement=DataStmt}]
