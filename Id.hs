module Id where

-- identifiers, fixed for all logics
{-
data ID = Simple_Id String
        | Compound_Id (String,[ID])

-}
type Pos = (Int, Int) -- line, column
 
nullPos :: Pos
nullPos = (0,0) -- dummy position

type Region = (Pos,Pos)

 
-- tokens as supplied by the scanner
data Token = Token(String, Pos) -- deriving (Show, Eq, Ord)
showTok (Token(t, _)) = t

instance Eq Token where
   Token(s1, _) == Token(s2, _) = s1 == s2
 
instance Ord Token where
   Token(s1, _) <= Token(s2, _) = s1 <= s2
 
instance Show Token where
   showsPrec _ = showString.showTok

-- spezial tokens
type Keyword = Token
type TokenOrPlace = Token
 
-- move to scanner
setPos(Token(t, _), p) = Token(t, p)

place = "__"

isPlace(Token(t, _)) = t == place
 
-- an identifier may be mixfix (though not for a sort) and compound
data Id = Id([TokenOrPlace], [Id]) deriving (Eq, Ord)
 
instance Show Id where
    showsPrec _ (Id(ts, is)) = showString ((foldl (++) "" (map show ts)) ++ 
	(case is of [] -> "" ;  _:_ -> (show is)))

-- simple Id
simpleId :: String -> Id
simpleId(s) = Id([Token(s, nullPos)],[]) 


