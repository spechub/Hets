module PLpatt.Tools where

import PLpatt.Sign as Sign
import PLpatt.AS_BASIC_PLpatt
import MMT.Tools as Generic
import Data.Maybe

bool_from_pt :: Generic.Tree -> Maybe(Bool')
bool_from_pt x = case x of
    (Generic.Application n Nothing args ) -> if (n == "false")
    then if (length(args) == 0)
      then Just((False'))
      else Nothing
    else if (n == "true")
      then if (length(args) == 0)
        then Just((True'))
        else Nothing
      else if (n == "not")
        then if (length(args) == 1)
          then Just((Not (fromJust (bool_from_pt (args !! 0) ) ) ))
          else Nothing
        else if (n == "and")
          then if (length(args) == 2)
            then Just((And (fromJust (bool_from_pt (args !! 0) ) ) (fromJust (bool_from_pt (args !! 1) ) ) ))
            else Nothing
          else if (n == "or")
            then if (length(args) == 2)
              then Just((Or (fromJust (bool_from_pt (args !! 0) ) ) (fromJust (bool_from_pt (args !! 1) ) ) ))
              else Nothing
            else Nothing
    (Generic.Application n Just((pat,inst)) args ) -> if ((n == "bool") && (pat == "prop"))
    then if (length(args) == 0)
      then Just((Prop_bool inst ))
      else Nothing
    else Nothing
    (Generic.Bind n v s ) -> Nothing
    (Generic.Tbind n a v s ) -> Nothing
    (Generic.Variable n ) -> Nothing
    _ -> Nothing
  

decl_from_pt :: Generic.Decl -> Maybe(Decl)
decl_from_pt d = case d of
    (Generic.Decl i p args ) -> if (p == "axiom")
    then if (length(args) == 1)
      then (Axiom_decl i [(fromJust (bool_from_pt (args !! 0) ) )] )
      else Nothing
    else if (p == "prop")
      then if (length(args) == 0)
        then (Prop_decl i [] )
        else Nothing
      else Nothing
  

sign_from_pt :: Generic.Sign -> Sigs
sign_from_pt sg = (map decl_from_pt sg)

axiom_from_pt :: Generic.Tree -> Bool'
axiom_from_pt ax = (fromJust (bool_from_pt ax ) )

theo_from_pt :: Generic.Theo -> Theo
theo_from_pt th = theo{sign = (sign_from_pt (sign th) ),axioms = (map axiom_from_pt (axioms th))}


