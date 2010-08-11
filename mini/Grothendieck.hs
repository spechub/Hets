{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Grothendieck (module Logic, module Grothendieck) where

import Logic

data AnyLogic =
        forall id s m sen b sy .
        Logic id s m sen b sy  =>
        G_logic id

data AnyTranslation =
        forall id1 s1 m1 sen1 b1 sy1 id2 s2 m2 sen2 b2 sy2 .
        (Logic id1 s1 m1 sen1 b1 sy1, Logic id2 s2 m2 sen2 b2 sy2) =>
        G_LTR (Logic_translation id1 s1 m1 sen1 b1 sy1 id2 s2 m2 sen2 b2 sy2)

instance Show AnyTranslation where
  show _ = "<tr>"

type LogicGraph = ([(String,AnyLogic)],[(String,AnyTranslation)])

data G_basic_spec =
        forall id s m sen b sy .
        Logic id s m sen b sy  =>
        G_basic_spec id b

instance Show G_basic_spec where
    show (G_basic_spec id b) = show b

data G_symbol_mapping_list =
        forall id s m sen b sy .
        Logic id s m sen b sy  =>
        G_symbol_mapping_list id sy

instance Show G_symbol_mapping_list where
    show (G_symbol_mapping_list id sy) = show sy

data G_sentence =
        forall id s m sen b sy .
        Logic id s m sen b sy  =>
        G_sentence id sen

data G_theory =
        forall id s m sen b sy .
        Logic id s m sen b sy  =>
        G_theory id (Theory s sen)

data G_morphism =
        forall id s m sen b sy .
        Logic id s m sen b sy  =>
        G_morphism id m

instance Show G_theory where
   show (G_theory _ (sig,ax)) = show sig

-- auxiliary functions for conversion between different logics
coerce :: (Typeable a, Typeable b) => a -> Maybe b
coerce = fromDynamic . toDyn

coerce1 :: (Typeable a, Typeable b) => a -> b
coerce1 = the . coerce

the :: Maybe a -> a
the (Just x) = x
