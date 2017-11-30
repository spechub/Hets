module PGIP.Server.Examples where

dol :: String
dol = "logic CASL" ++ "\n"
        ++ "spec o = sort s" ++ "\n"
        ++ "end"

casl :: String
casl = "spec sp = sort s" ++ "\n"
        ++ "end"

owl :: String
owl = "Ontology: O" ++ "\n"
        ++ "Class: A"

clif :: String
clif = "(forall (x) (p x))"
