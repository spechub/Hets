
{- |
Module      :  ./RigidCASL/Print_AS.hs
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  portable

printing rigid declarations
-}

module RigidCASL.Print_AS where

import CASL.ToDoc
import qualified CASL.AS_Basic_CASL as CBasic

import Common.Doc
import Common.DocUtils
import Common.Keywords
import qualified Common.Lib.MapSet as MapSet

import RigidCASL.AS_Rigid
import RigidCASL.Sign
import qualified Data.Set as Set

instance Pretty R_SIG_ITEM where
    pretty (Rigid_sorts ls _) =
        cat [keyword (rigidS ++ sortS ++ pluralS ls)]
    pretty (Rigid_op_items ls _) =
        cat [keyword (rigidS ++ opS ++ pluralS ls),
             space <> semiAnnos pretty ls]
    pretty (Rigid_pred_items ls _) =
        cat [keyword (rigidS ++ predS ++ pluralS ls),
             space <> semiAnnos pretty ls]

instance Pretty RigidExt where
    pretty = printRigidExt

printRigidSorts :: [CBasic.SORT] -> Doc
printRigidSorts xs = case xs of 
   [] -> empty 
   _ -> 
     keyword rigidS <+> 
     keyword (sortS ++ case xs of
     [_] -> ""
     _ -> "s") <+> 
     ppWithCommas xs 

printRigidExt :: RigidExt -> Doc
printRigidExt s = let 
  xs = Set.toList $ rigidSorts s
 in printRigidSorts xs
    $+$
    printSetMap (keyword rigidS <+> keyword opS) empty
                (MapSet.toMap $ rigidOps s)
    $+$ printSetMap (keyword rigidS <+> keyword predS) space
        (MapSet.toMap $ rigidPreds s)
