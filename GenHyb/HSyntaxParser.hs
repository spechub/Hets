
data HSpecFile = HSpecFile [HSpec]

data HSpec = HSpec {
                name :: String,
                logic :: String,
                dataPart :: String,
                configPart :: String
              }
              deriving Show

parseHSpecFile :: AParser st HSpecFile
parseHSpecFile = do
 file <- many1 parseHSpec
 eof
 return $ HSpec file

parseHSpec :: AParser st HSpec
parseHSpec = do
 _ <- string "spec"
 s <- simpleId
 _ <- string "="
 _ <- string "logic:"
 l <- simpleId
 _ <- string "data:"
 d <- simpleId
 _ <- string "configuration:"
 c <- manyTill anyChar $ string "end"
 return $ HSpec s l d c

writeHSpecFile :: HSpecFile -> String
writeHSpecFile (HSpecFile hspecs) = 
 intercalate "\n" $ map writeHSpec hspecs

writeHSpec :: HSpec -> String
writeHSpec hsp = 
 "logic " ++ logic hsp ++ "\n\n" ++
 "spec " ++ name hsp ++ " =\n" ++ 
 " data " ++ dataPart hsp ++ "\n" ++
 "  {\n" ++ 
 configPart hsp ++ 
 "  }\nend \n" 
  
