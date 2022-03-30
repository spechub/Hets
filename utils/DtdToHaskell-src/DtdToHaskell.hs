{-# LANGUAGE CPP #-}
module Main where

{- This program is provided to convert an XML file containing a DTD
into a Haskell module containing data/newtype definitions which
mirror the DTD.  Once you have used this program to generate your type
definitions, you should import Xml2Haskell wherever you intend
to read and write XML files with your Haskell programs. -}

import System.Environment
import System.Exit
import System.IO
import Data.List (nub, takeWhile, dropWhile)
import Control.Monad

-- import Text.XML.HaXml.Wrappers   (fix2Args)
import Text.XML.HaXml (version)
import Text.XML.HaXml.Types (DocTypeDecl (..))
#ifndef HAXML_COMPAT
import Text.XML.HaXml.Namespaces (localName)
#endif
import Text.XML.HaXml.Parse (dtdParse)
import Text.XML.HaXml.DtdToHaskell.TypeDef (ppTypeDef, mangle)
import Text.XML.HaXml.DtdToHaskell.Convert (dtd2TypeDef)
import Text.XML.HaXml.DtdToHaskell.Instance (mkInstance)
import Text.PrettyPrint.HughesPJ (render, vcat)

-- sucked in from Text.XML.HaXml.Wrappers to avod dependency on T.X.H.Html
fix2Args :: IO (String, String, String)
fix2Args = do
  args <- getArgs
  when ("--version" `elem` args) $ do
      putStrLn $ "part of HaXml-" ++ version
      exitSuccess
  when ("--help" `elem` args) $ do
      putStrLn "See http://haskell.org/HaXml"
      exitSuccess
  case length args of
    0 -> return ("-", "-", "")
    1 -> return (head args, "-", "")
    2 -> return (head args, args !! 1, "")
    3 -> return (head args, args !! 1, args !! 2)
    _ -> do prog <- getProgName
            putStrLn ("Usage: " ++ prog ++ " [xmlfile] [outfile]")
            exitFailure


main :: IO ()
main =
  fix2Args >>= \ (inf, outf, prefix) ->
  ( if inf == "-" then getContents
    else readFile inf ) >>= \ content ->
  ( if outf == "-" then return stdout
    else openFile outf WriteMode ) >>= \ o ->
  let (DTD name _ markup) = (getDtd . dtdParse inf) content
      decls = (nub . dtd2TypeDef) markup
      realname | outf /= "-" = mangle (trim outf)
#ifndef HAXML_COMPAT
               | null (localName name) = mangle (trim inf)
               | otherwise = mangle (localName name)
#else
               | null name = mangle (trim inf)
               | otherwise = mangle name
#endif
  in
  do hPutStrLn o ("module " ++ prefix ++ realname
#ifndef HAXML_COMPAT
                  ++ " where\n\nimport Text.XML.HaXml.XmlContent hiding (Const)"
#else
                  ++ " where\n\nimport Text.XML.HaXml.XmlContent"
#endif
                  ++ "\nimport Text.XML.HaXml.OneOfN"
#ifndef HAXML_COMPAT
                  ++ "\nimport Text.XML.HaXml.Types"
#endif
                  )
    {- ++"\nimport Char (isSpace)"
    ++"\nimport List (isPrefixOf)" -}
     hPutStrLn o "\n\n{-Type decls-}\n"
     (hPutStrLn o . render . vcat . map ppTypeDef) decls
     hPutStrLn o "\n\n{-Instance decls-}\n"
     mapM_ (hPutStrLn o . (++ "\n") . render . mkInstance) decls
     hPutStrLn o "\n\n{-Done-}"
     hFlush o

getDtd :: Maybe t -> t
getDtd (Just dtd) = dtd
getDtd (Nothing) = error "No DTD in this document"

trim :: String -> String
trim name | '/' `elem` name = (trim . tail . dropWhile (/= '/')) name
          | '.' `elem` name = takeWhile (/= '.') name
          | otherwise = name
