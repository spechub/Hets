module UML.StateMachine where
import           Data.Maybe

data StateMachine = StateMachine {
        regions :: [Region]} deriving Show{-smEntities :: [Entity],
        smTransitions :: [Transition]-}

data Region = Region {
        states      :: [Entity],
        transitions :: [Transition]} deriving Show

data PseudoState = PseudoState {
    pseudoStateName :: String,
    pseudoStateType :: String} deriving Show

data EntityType = State [Region] | EntryState| ExitState | FinalState | InitialState  | DeepHistory | ShallowHistory | Junction | Choice | Fork | Join deriving Show

data Entity = Entity String String EntityType deriving Show
{-data State = State {
        region :: [Region],
        stateName :: String
} deriving Show-}

getEntityId :: Entity -> String
getEntityId (Entity id _ _) = id

getEntityName :: Entity -> String
getEntityName (Entity _ name _) = name


data Transition = Transition {
        source  :: String,
        target  :: String,
        trigger :: Maybe Trigger,
        guard   :: Maybe Guard,
        effect  :: Maybe Event}

instance Show Transition where
    show tran = ((show $ source tran) ++ " --" ++ tr ++ gu ++ ev ++ "--> " ++ (show $ target tran))
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
