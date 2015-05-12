module UML.StateMachine where
import           Data.Maybe

data Region = Region {
        states      :: [Entity],
        transitions :: [Transition]} deriving Show

data PseudoState = PseudoState {
    pseudoStateName :: String,
    pseudoStateType :: String} deriving Show

data Entity = State String [Region] | EntryState String | ExitState String | InitialState String | DeepHistory | ShallowHistory | Junction | Choice | Fork | Join deriving Show
{-data State = State {
        region :: [Region],
        stateName :: String
} deriving Show-}

data Transition = Transition {
        source  :: String,
        target  :: String,
        trigger :: Maybe Trigger,
        guard   :: Maybe Guard,
        effect  :: Maybe Event}

instance Show Transition where
    show tran = ((source tran) ++ " --" ++ tr ++ gu ++ ev ++ "--> " ++ (target tran))
         where
            tr = fromMaybe "" (trigger tran)
            gu = case guard tran of
                Nothing -> ""
                Just g -> "[" ++ g ++ "]"
            ev = case effect tran of
                Nothing -> ""
                Just e -> "/" ++ e

type Trigger = String
type Guard = String
type Event = String
