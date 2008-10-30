module Text.Tabular.Latex where

import Data.List (intersperse)
import Text.Tabular


render :: (a -> String) -> Table a -> String
render = renderUsing (repeat "r")

renderUsing :: [String] -- ^ column header specifications including label (l,h,p{3cm},etc)
            -> (a -> String) -> Table a -> String
renderUsing cols f (Table rh ch cells) =
 unlines $ ( "\\begin{tabular}{" ++ hspec ++ "}")
         : [ addTableNl header
           , hline
           , (concatMap (either vAttr addTableNl) $
              flattenHeader $ fmap row $ zipHeader [] cells rh)
           , "\\end{tabular}" ]
 where
  ch2 = Group DoubleLine [(Header ""),ch]
  hspec  = concatMap (either hAttr fst) $ flattenHeader
         $ zipHeader "" cols ch2
  header = texCols . map label . headerStrings $ ch2
  --
  row (cs,h) = texCols $ label h : map f cs
  texCols  = concat . intersperse " & "
  texRows  = map addTableNl
  rhStrings = headerStrings rh


hline :: String
hline = "\\hline"

addTableNl :: String -> String
addTableNl = (++ "\\\\\n")

label :: String -> String
label s = "\\textbf{" ++ s ++ "}"

hAttr :: Properties -> String
hAttr NoLine     = ""
hAttr SingleLine = "|"
hAttr DoubleLine = "||"

vAttr :: Properties -> String
vAttr NoLine     = ""
vAttr SingleLine = hline
vAttr DoubleLine = hline ++ hline
