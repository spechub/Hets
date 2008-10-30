module Text.Tabular.Html where

import Text.Tabular
import Text.Html

-- | for simplicity, we assume that each cell is rendered
--   on a single line
render :: (a -> String) -> Table a -> Html
render f (Table rh ch cells) =
 table $ header +++ body
 where
  header = tr (myTh "" +++ headerCore)
  headerCore = concatHtml $ squish applyVAttr myTh ch
  --
  body = concatHtml $ squish applyHAttr tr
       $ fmap fst
       $ zipHeader noHtml rows ch
  rows = zipWith (\h cs -> myTh h +++ doRow cs)
           rhStrings cells
  doRow cs = concatHtml $ squish applyVAttr myTd $
               fmap fst $ zipHeader "" (map f cs) ch
  --
  myTh  = th . stringToHtml
  myTd  = td . stringToHtml
  rhStrings = headerStrings rh
  applyVAttr p x = x ! vAttr p
  applyHAttr p x = x ! hAttr p

vAttr :: Properties -> [HtmlAttr]
vAttr DoubleLine = [theclass "thickright"]
vAttr SingleLine = [theclass "thinright"]
vAttr _          = []

hAttr :: Properties -> [HtmlAttr]
hAttr DoubleLine = [theclass "thickbottom"]
hAttr SingleLine = [theclass "thinbottom"]
hAttr _          = []


-- | Convenience function to add a CSS string to your
--   HTML document
css :: String -> Html
css c = style (stringToHtml c) ! [ thetype "text/css" ]

-- | You need to incorporate some CSS into your file with
--   the classes @thinbottom@, @thinright@, @thickbottom@
--   and @thickright@.  See 'css'
defaultCss :: String
defaultCss = unlines
  [ "table   { border-collapse: collapse; border: 1px solid; }"
  , "th      { padding:0.2em; background-color: #eeeeee }"
  , "td      { padding:0.2em; }"
  , ".thinbottom  { }"
  , ".thickbottom { border-bottom: 1px solid }"
  , ".thinright  { border-right: 1px solid }"
  , ".thickright { border-right: 3px solid }"
  ]
