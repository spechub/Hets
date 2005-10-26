{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (GHC specific, 4 byte ints)

GhcBinary instances for common data types

-}

module Common.BinInsts where

import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.OrderedMap
import Common.Result
import Common.Lib.Binary

{-
import Text.XML.HXT.DOM.XmlTreeTypes

{-! for Cardinality derive : GhcBinary !-}
{-! for Drcomponent derive : GhcBinary !-}
{-! for Ircomponent derive : GhcBinary !-}
{-! for Value derive : GhcBinary !-}
{-! for Individual derive : GhcBinary !-}
{-! for Modality derive : GhcBinary !-}
{-! for Annotation derive : GhcBinary !-}
{-! for Func derive : GhcBinary !-}
{-! for DataLiteral derive : GhcBinary !-}
{-! for Restriction derive : GhcBinary !-}
{-! for Description derive : GhcBinary !-}
{-! for DataRange derive : GhcBinary !-}
{-! for Axiom derive : GhcBinary !-}
{-! for Fact derive : GhcBinary !-}

instance Binary QName where
    put_ bh (QN aa ab ac) = do
            put_ bh aa
            put_ bh ab
            put_ bh ac
    get bh = do
    aa <- get bh
    ab <- get bh
    ac <- get bh
    return (QN aa ab ac)
-}

instance (Binary a) => Binary (Result a) where
    put_ bh (Result aa ab) = do
            put_ bh aa
            put_ bh ab
    get bh = do
    aa <- get bh
    ab <- get bh
    return (Result aa ab)

instance Binary Diagnosis where
    put_ bh (Diag aa ab ac) = do
            put_ bh aa
            put_ bh ab
            put_ bh ac
    get bh = do
    aa <- get bh
    ab <- get bh
    ac <- get bh
    return (Diag aa ab ac)

instance Binary DiagKind where
    put_ bh Error = do
            putByte bh 0
    put_ bh Warning = do
            putByte bh 1
    put_ bh Hint = do
            putByte bh 2
    put_ bh Debug = do
            putByte bh 3
    put_ bh MessageW = do
            putByte bh 4
    get bh = do
            h <- getByte bh
            case h of
              0 -> do
                    return Error
              1 -> do
                    return Warning
              2 -> do
                    return Hint
              3 -> do
                    return Debug
              4 -> do
                    return MessageW

instance (Binary a) => Binary (ElemWOrd a) where
    put_ bh (EWOrd aa ab) = do
            put_ bh aa
            put_ bh ab
    get bh = do
    aa <- get bh
    ab <- get bh
    return (EWOrd aa ab)

instance (Ord k, Binary k,Binary a) => Binary (Map.Map k a) where
    put_ bh = put_ bh . Map.toList
    get = fmap Map.fromList . get

instance (Ord k, Binary k) => Binary (Set.Set k) where
    put_ bh m = put_ bh $ Set.toList m
    get bh = fmap Set.fromList $ get bh

instance (Ord k, Binary k ) => Binary (Rel.Rel k) where
    put_ bh m = put_ bh $ Rel.toList m
    get bh = fmap Rel.fromList $ get bh

instance Binary Id where
    put_ bh (Id aa ab ac) = do
            put_ bh aa
            put_ bh ab
            put_ bh ac
    get bh = do
    aa <- get bh
    ab <- get bh
    ac <- get bh
    return (Id aa ab ac)

instance Binary Token where
    put_ bh (Token aa ab) = do
            put_ bh aa
            put_ bh ab
    get bh = do
    aa <- get bh
    ab <- get bh
    return (Token aa ab)

instance Binary Range where
    put_ bh (Range aa) = do
            put_ bh aa
    get bh = do
    aa <- get bh
    return (Range aa)

instance Binary Pos where
    put_ bh (SourcePos aa ab ac) = do
            put_ bh aa
            put_ bh ab
            put_ bh ac
    get bh = do
    aa <- get bh
    ab <- get bh
    ac <- get bh
    return (SourcePos aa ab ac)
