import Text.Tabular
import Text.Html

import qualified Text.Tabular.AsciiArt as A
import qualified Text.Tabular.Html     as H
import qualified Text.Tabular.Latex    as L

main =
 do writeFile "sample1.txt"  $ A.render id example2
    writeFile "sample1.html" $ renderHtml $
      H.css H.defaultCss +++ H.render id example2
    writeFile "sample1T.tex"  $ L.render id example2
    putStrLn $ "wrote sample1.txt, sample1.html and sample1T.tex"
    putStrLn $ "(hint: pdflatex sample1)"

-- | an example table showing grouped columns and rows
sample1 = Table
  (Group SingleLine
     [ Group NoLine [Header "A 1", Header "A 2"]
     , Group NoLine [Header "B 1", Header "B 2", Header "B 3"]
     ])
  (Group DoubleLine
     [ Group SingleLine [Header "memtest 1", Header "memtest 2"]
     , Group SingleLine [Header "time test 1", Header "time test 2"]
     ])
  [ ["hog", "terrible", "slow", "slower"]
  , ["pig", "not bad",  "fast", "slowest"]
  , ["good", "awful" ,  "intolerable", "bearable"]
  , ["better", "no chance", "crawling", "amazing"]
  , ["meh",  "well...", "worst ever", "ok"]
  ]

-- | the same example built a slightly different way
example2 =
  empty ^..^ colH "memtest 1" ^|^ colH "memtest 2"
        ^||^ colH "time test" ^|^ colH "time test 2"
  +.+ row "A 1" ["hog", "terrible", "slow", "slower"]
  +.+ row "A 2" ["pig", "not bad", "fast", "slowest"]
  +----+
      row "B 1" ["good", "awful", "intolerable", "bearable"]
  +.+ row "B 2" ["better", "no chance", "crawling", "amazing"]
  +.+ row "B 3" ["meh",  "well...", "worst ever", "ok"]
