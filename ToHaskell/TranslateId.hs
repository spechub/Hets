module ToHaskell.TranslateId where

import Common.Id
import qualified Common.Lib.Map as Map
import Data.Char
import Data.List
------------------------------------------------------------------------
-- Translation of Id's
------------------------------------------------------------------------

-- | Converts an HasCASL identifier to a valid name in haskell 
-- regarding wether it should start with a lower or upper case letter.
translateIdWithType :: IdCase -> Id -> String
translateIdWithType ty (Id tlist idlist _poslist) = 
  let s = translateId (Id tlist idlist _poslist)
  in if ty == UpperId then
        if (isLower $ head $ tokStr $ head tlist) || (head s == '_') then
	  "A_" ++ s
	else firstDigit s
     else -- if ty == LowerId then
        if isUpper $ head $ tokStr $ head tlist then
           "a_" ++ s
        else firstDigit s

-- | To determine, wether an identifier in haskell should start with an 
-- upper case or lower case letter.
data IdCase = UpperId | LowerId deriving (Eq,Show)

-- | Converts an HasCASL identifier to a valid name in haskell.
translateId :: Id -> String
translateId (Id tlist idlist _poslist) = 
    (translateTokens tlist) ++ (translateCompound idlist)


translateTokens :: [Token] -> String
translateTokens [] = ""
translateTokens (t:ts) = 
    let str = tokStr t
        res = translateTokens ts in
    if isPlace t then
      subPlace ++ res
    else (concatMap symbolMapping str) ++ res

startsWithDigit :: String -> Bool
startsWithDigit s = isDigit $ head s

firstDigit :: String -> String
firstDigit s = if startsWithDigit s then
	         "_D" ++ s
	       else s

subPlace :: String
subPlace = "_2"

symbolMapping :: Char -> String
symbolMapping c = Map.findWithDefault [c] c symbolMap

translateCompound :: [Id] -> String
--  [      ,      ]
-- _C     _k     _J
translateCompound [] = ""
translateCompound ids = "_C" ++
                        (concat $ intersperse "_k" $ map translateId ids) ++
                        "_J"

symbolMap :: Map.Map Char String
symbolMap = Map.fromList symbolTable

symbolTable :: [(Char,String)]
symbolTable = 
-- Special / reserved
   [('_' , "_1"),    -- \95
    ('{' , "_b"),    -- \123
    ('}' , "_r"),    -- \125
    ('[' , "_s"),    -- \91
    (']' , "_q"),    -- \93
    ('.' , "_d"),    -- \46
    ('\'', "_p"),
-- Symbols
    ('+' , "_P"),    -- \43
    ('-' , "_M"),    -- \45
    ('*' , "_T"),    -- \42
    ('/' , "_D"),    -- \47
    ('\\', "_B"),    -- \92
    ('&' , "_A"),    -- \38
    ('=' , "_I"),    -- \61
    ('<' , "_L"),    -- \60
    ('>' , "_G"),    -- \62
    ('!' , "_E"),    -- \33
    ('?' , "_Q"),    -- \63
    (':' , "_C"),    -- \58
    ('$' , "_S"),    -- \36
    ('@' , "_O"),    -- \64
    ('#' , "_H"),    -- \35
    ('^' , "_V"),    -- \94
    ('|' , "_I"),    -- \124
    ('~' , "_N"),    -- \126
    ('¡' , "_e"),    -- \161
    ('¢' , "_c"),    -- \162   
    ('£' , "_l"),    -- \163
    ('§' , "_f"),    -- \167
    ('©' , "_a"),    -- \169
    ('¬' , "_n"),    -- \172
    ('°' , "_h"),    -- \176
    ('±' , "_k"),    -- \177
    ('²' , "_w"),    -- \178
    ('³' , "_t"),    -- \179
    ('µ' , "_y"),    -- \181
    ('¶' , "_j"),    -- \182
    ('·' , "_i"),    -- \183
    ('¹' , "_o"),    -- \185
    ('¿' , "_q"),    -- \191
    ('×' , "_m"),    -- \215
    ('÷' , "_g")]    -- \247


