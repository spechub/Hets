----------------------------------------------------------------
-- Daan Leijen (c) 1999-2001, daan@cs.uu.nl
--
-- Textual source positions.
--
-- $Revision$
-- $Author$
-- $Date$
-- $Id$
----------------------------------------------------------------
module ParsecPos  ( SourceName, Line, Column                 
                  , SourcePos
                  , sourceLine, sourceColumn, sourceName
                  , incSourceLine, incSourceColumn
                  , setSourceLine, setSourceColumn, setSourceName
                  , newPos, initialPos
                  , updatePosChar, updatePosString
                  ) where

-----------------------------------------------------------
-- Source Positions, a file name, a line and a column.
-- upper left is (1,1)
-----------------------------------------------------------                         
type SourceName     = String
type Line           = Int
type Column         = Int

data SourcePos      = SourcePos { sourceName :: SourceName 
				, sourceLine :: !Line
				, sourceColumn :: !Column
				}
		     deriving (Eq,Ord)
		

newPos :: SourceName -> Line -> Column -> SourcePos
newPos name line column
    = SourcePos name line column

initialPos :: SourceName -> SourcePos
initialPos name
    = newPos name 1 1

incSourceLine :: SourcePos -> Line -> SourcePos
incSourceLine   s n    = s { sourceLine = sourceLine s + n }
incSourceColumn :: SourcePos -> Column -> SourcePos
incSourceColumn s n    = s { sourceColumn = sourceColumn s + n }

setSourceName :: SourcePos -> SourceName -> SourcePos
setSourceName   s n    = s { sourceName = n }
setSourceLine :: SourcePos -> Line -> SourcePos
setSourceLine   s n    = s { sourceLine = n }
setSourceColumn :: SourcePos -> Column -> SourcePos
setSourceColumn s n    = s { sourceColumn = n }

-----------------------------------------------------------
-- Update source positions on characters
-----------------------------------------------------------                         
updatePosString :: SourcePos -> String -> SourcePos
updatePosString pos string
    = forcePos (foldl updatePosChar pos string)

updatePosChar   :: SourcePos -> Char -> SourcePos
updatePosChar (SourcePos name line column) c   
    = forcePos $
      case c of
        '\n' -> SourcePos name (line+1) 1
        '\t' -> SourcePos name line (column + 8 - ((column-1) `mod` 8))
        _    -> SourcePos name line (column + 1)
        

forcePos :: SourcePos -> SourcePos      
forcePos pos@(SourcePos _ line column)
    = seq line (seq column (pos))

-----------------------------------------------------------
-- Show positions 
-----------------------------------------------------------                                                 
instance Show SourcePos where
  show (SourcePos name line column)
    | null name = showLineColumn
    | otherwise = "\"" ++ name ++ "\" " ++ showLineColumn
    where
      showLineColumn    = "(line " ++ show line ++
                          ", column " ++ show column ++
                          ")" 
