module PLpatt.Tools where

import PLpatt.Sign
import PLpatt.AS_BASIC_PLpatt
import qualified MMT.Tools as Generic
import Data.Maybe

bool_from_pt :: (Generic.Tree) -> Maybe(Bool')
bool_from_pt x = case x of
    (Generic.Application n Nothing args ) -> if (n == "equiv")
    then if (length(args) == 2)
      then (Just((Equiv (fromJust (bool_from_pt (args !! 0) ) ) (fromJust (bool_from_pt (args !! 1) ) ) )))
      else Nothing
    else if (n == "impl")
      then if (length(args) == 2)
        then (Just((Impl (fromJust (bool_from_pt (args !! 0) ) ) (fromJust (bool_from_pt (args !! 1) ) ) )))
        else Nothing
      else if (n == "not")
        then if (length(args) == 1)
          then (Just((Not (fromJust (bool_from_pt (args !! 0) ) ) )))
          else Nothing
        else if (n == "or")
          then if (length(args) == 2)
            then (Just((Or (fromJust (bool_from_pt (args !! 0) ) ) (fromJust (bool_from_pt (args !! 1) ) ) )))
            else Nothing
          else if (n == "and")
            then if (length(args) == 2)
              then (Just((And (fromJust (bool_from_pt (args !! 0) ) ) (fromJust (bool_from_pt (args !! 1) ) ) )))
              else Nothing
            else if (n == "false")
              then if (length(args) == 0)
                then (Just((False')))
                else Nothing
              else if (n == "true")
                then if (length(args) == 0)
                  then (Just((True')))
                  else Nothing
                else Nothing
    (Generic.Application n (Just((pat,inst))) args ) -> Nothing
    (Generic.Bind _n _v _s ) -> Nothing
    (Generic.Tbind _n _a _v _s ) -> Nothing
    (Generic.Variable _n ) -> Nothing
  

decl_from_pt :: (Generic.Decl) -> Maybe(Decl)
decl_from_pt d = case d of
    (Generic.Decl pname iname args ) -> if (pname == "prop")
    then if (length(args) == 0)
      then (Just((Prop_decl (Prop iname ) )))
      else Nothing
    else if (pname == "dot")
      then if (length(args) == 1)
        then (Just((Dot_decl (Dot iname (fromJust (bool_from_pt (args !! 0) ) ) ) )))
        else Nothing
      else Nothing
  

sign_from_pt :: (Generic.Sign) -> Sigs
sign_from_pt (Generic.Sign sg) = (Sigs (map (fromJust.decl_from_pt) sg) )

axiom_from_pt :: (Generic.Tree) -> Bool'
axiom_from_pt ax = (fromJust (bool_from_pt ax ) )

theo_from_pt :: (Generic.Theo) -> Theo
theo_from_pt th = Theo{sign = (sign_from_pt (Generic.sign th) ),axioms = (map axiom_from_pt (Generic.axioms th))}
