{-#LANGUAGE DeriveDataTypeable#-}
module EVT.Sign
        ( EVTIsKey
          , EVTDatatype (..)
          , EVTRawSymbol
        , EventNameMap
        , EVTVarMap
        , EVTSen
--	, EVTVarList
        , EVTSign (..)
        , EVTMorphism (..)
        , EVTSymbol (..)
        --, -- EVTTMap (..)
        , emptyEVTSign
    --    , isEVTSubsig
    --    , idMor
    --    , evtInclusion
    --    , uniteSig
        --, -- comp_rst_mor
        )
        where

--import CASL.Sign
import CASL.AS_Basic_CASL
import EVT.AS

import Common.Id

import Data.Data
import qualified Data.Map as Map

type EVTIsKey = Bool

type EventNameMap = Map.Map EVENT_NAME EVENT

type EVTVarMap = Map.Map SIMPLE_ID SORT
--type EVTVarList = [TERM ()]

{-data Sentence = EventEq EVENT_NAME {-EVTVarList-} EVENT
      deriving (Show, Eq, Ord, Typeable, Data)
-}
--type EVTCASLSign = Sign EVTSign
type EVTSen = Sentence
--type EVTCASLSen = FORMULA MACHINE

data EVTSign = EVTSign
    { 
          varSet :: EVTVarMap
        , eventSet :: EventNameMap

    } deriving (Show, Eq, Ord, Typeable, Data)

emptyEVTSign ::EVTSign
emptyEVTSign= EVTSign 
                {
                   varSet = Map.empty 
                 , eventSet = Map.empty 
                }

data EVTMorphism = EVTMorphism
                    { domain :: EVTSign 
                    , codomain :: EVTSign 
                    , event_map :: Map.Map EVTSign EVTSign
                    }
                    deriving (Eq, Ord, Show, Typeable, Data)



data EVTDatatype
  = EVTBoolean | EVTNat 
    deriving (Eq, Ord, Typeable, Data)

type EVTRawSymbol = Id

data EVTSymbol = E Id |     -- id of an event
                 --  Id          -- id of the symbol --guard?
                --   Id          -- id of the table --action?
                   EVTDatatype  -- datatype of the symbol
                   EVTIsKey     -- is it a key?
                deriving (Eq, Ord, Show, Typeable, Data)
 

instance GetRange EVTSymbol

{-
data EVTEvent = EVTEvent
                {
			eid :: Id
			, guards :: Set.Set EVTGuard
			, actions :: Set.Set EVTAction
                }
                deriving (Show, Typeable, Data)
instance GetRange EVTEvent

instance GetRange EVTGuard
instance GetRange EVTAction



data EVTMachine = EVTMachine
                    {
                        events :: Set.Set EVTEvent
                    }
                deriving (Eq, Ord, Show, Typeable, Data)


isEVTSubsig :: EVTMachine -> EVTMachine -> Bool
isEVTSubsig t1 t2 = t1 <= t2

uniteSig :: (Monad m) => EVTMachine -> EVTMachine -> m EVTMachine
uniteSig s1 s2 =
    if s1 `isEVTSubsig` s2 || s2 `isEVTSubsig` s1 || s1 `isDisjoint` s2
    then return $ EVTMachine $ events s1 `Set.union` events s2
    else fail $ "Events " ++ showDoc s1 "\nand "
             ++ showDoc s2 "\ncannot be united."

type Sign = EVTEvent


data EVTMorphism = EVTMorphism
                    { domain :: EVTEvent
                    , codomain :: EVTEvent
                    , event_map :: Map.Map Id Id
          	}
                    deriving (Eq, Ord, Show, Typeable, Data)

{-- I hope that this works right, I do not want to debug this
apply_comp_c_map :: EVTEvent -> Map.Map Id Id -> EVTMorphism -> EVTMorphism
                 -> (Id, EVTTMap)
apply_comp_c_map rst t_map imap imor =
    let i = t_name rst
        c2 = column_map imor
    in case Map.lookup i $ column_map imap of
      Just iM -> case Map.lookup (Map.findWithDefault i i t_map) c2 of
        Just iM2 ->
          let c_set = Map.fromList . map (\ c -> (c_name c, ())) $ columns rst
              oM = composeMap c_set (col_map iM) (col_map iM2)
          in (i, EVTTMap oM)
        Nothing -> (i, iM)
      Nothing -> (i, Map.findWithDefault (EVTTMap Map.empty)
                       (Map.findWithDefault i i t_map) c2)
-}
-- composition of EVT morphisms
{-comp_rst_mor :: EVTMorphism -> EVTMorphism -> Result EVTMorphism
comp_rst_mor mor1 mor2 =
        let d1 = domain mor1
            t1 = Set.toList $ events d1
            e_set = Map.fromList $ map (\ e -> (e_name e, ())) t1
            e_map = composeMap e_set (event_map mor1) (event_map mor2)

        in return EVTMorphism
                { domain = d1
                , codomain = codomain mor2
                , event_map = e_map
                }
-} -}



{-
-- ^ id-morphism for EVT
idMor :: EVTEvent -> EVTMorphism
idMor t = EVTMorphism
            { domain = t
            , codomain = t
            --, event_map = Nothing--foldl (\ y x -> Map.insert (eid x) (eid x) y) Map.empty $ Set.toList $ events t 
            }

{-evtInclusion :: EVTEvent -> EVTEvent -> Result EVTMorphism
evtInclusion t1 t2 = return EVTMorphism
            { domain = t1
            , codomain = t2
            , event_map = foldl (\ y x -> Map.insert (e_name x) (e_name x) y)
                          Map.empty $ Set.toList $ events t1
            }
-}
-- pretty printing stuff

{-instance Pretty RSColumn where
    pretty c = (if c_key c then keyword rsKey else empty) <+>
       pretty (c_name c) <+> colon <+> pretty (c_data c)
-}
instance Pretty EVTEvent where
{-   pretty t = keyword evtName $+$ vcat (map pretty $ Set.toList $ eid t)  -}      


{-instance Pretty EVTEvents where
   -}

{- instance Pretty RSTMap where
    pretty = pretty . col_map


instance Pret, Set.fromList $ events t2ty RSMorphism where
    pretty m = pretty (domain m) $+$ mapsto <+> pretty (codomain m)
                $+$ pretty (table_map m) $+$ pretty (column_map m)
-}
instance Pretty EVTSymbol where

instance Pretty EVTMorphism where
    

instance Show EVTDatatype where
    show dt = case dt of
        EVTBoolean -> evtBool
        EVTNat -> evtNat

instance Pretty EVTDatatype where
  pretty = keyword . show

{- we need an explicit instance declaration of Eq and Ord that
correctly deals with tables -}
instance Ord EVTEvent where
  compare t1 t2 =
    compare (eid t1) (eid t2) 
   
instance Eq EVTEvent where
  a == b = compare a b == EQ


isDisjoint :: EVTMachine -> EVTMachine -> Bool
isDisjoint s1 s2 =
    let
        t1 = Set.map eid $ events s1
        t2 = Set.map eid $ events s2
    in
        Set.fold (\ x y -> y && (x `Set.notMember` t2)) True t1 &&
        Set.fold (\ x y -> y && (x `Set.notMember` t1)) True t2

instance Pretty EVTMachine where
-}
