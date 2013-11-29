module PLpatt.Tools where

import PLpatt.Sign
import PLpatt.AS_BASIC_PLpatt
import qualified MMT.Tools as Generic
import Data.Maybe

bool_from_pt :: Generic.Tree -> Maybe Bool'
bool_from_pt x = case x of
    (Generic.Application n Nothing args )
     | n == "equiv" && length args == 2 ->
       Just (Equiv (fromJust (bool_from_pt (head args)))
                   (fromJust (bool_from_pt (args !! 1))))
     | n == "impl" && length args == 2 ->
       Just (Impl (fromJust (bool_from_pt (head args)))
                  (fromJust (bool_from_pt (args !! 1))))
     | n == "not" && length args == 1 ->
       Just (Not (fromJust (bool_from_pt (head args))))
     | n == "or" && length args == 2 ->
       Just (Or (fromJust (bool_from_pt (head args)))
                (fromJust (bool_from_pt (args !! 1))))
     | n == "and" && length args == 2 ->
       Just (And (fromJust (bool_from_pt (head args)))
                 (fromJust (bool_from_pt (args !! 1))))
     | n == "false" && null args -> Just False'
     | n == "true" && null args -> Just True'
     | otherwise -> Nothing
    (Generic.Application n (Just (pat, inst)) args) -> Nothing
    (Generic.Bind _n _v _s ) -> Nothing
    (Generic.Tbind _n _a _v _s ) -> Nothing
    (Generic.Variable _n ) -> Nothing


decl_from_pt :: Generic.Decl -> Maybe Decl
decl_from_pt d = case d of
    (Generic.Decl pname iname args)
     | pname == "prop" && null args -> Just (Prop_decl (Prop iname))
     | pname == "dot" && length args == 1 ->
       Just (Dot_decl (Dot iname (fromJust (bool_from_pt (head args)))))
     | otherwise -> Nothing


sign_from_pt :: Generic.Sign -> Sigs
sign_from_pt (Generic.Sign sg) = Sigs (map (fromJust . decl_from_pt) sg)

axiom_from_pt :: Generic.Tree -> Bool'
axiom_from_pt ax = fromJust (bool_from_pt ax)

theo_from_pt :: Generic.Theo -> Theo
theo_from_pt th = Theo { sign = sign_from_pt (Generic.sign th),
                         axioms = map axiom_from_pt (Generic.axioms th) }
