{-------------------------------------------------------
 testing file for CSP-CASL semantics
--------------------------------------------------------}
module Main where

import Parse_hugo
import Parsec
import IO

main :: IO ()
main = parseTest cspCaslCSpec 
        "data 
           sort s 
           op c:s
         channel 
           n,m: s; 
           k,l: s 
         process 
           P(c)
        " 

