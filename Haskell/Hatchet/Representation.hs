{-------------------------------------------------------------------------------

        Copyright:              Mark Jones and The Hatchet Team 
                                (see file Contributors)

        Module:                 Representation

        Primary Authors:        Mark Jones and Bernie Pope

        Description:            The basic data types for representing objects 
                                in the type inference algorithm.  

        Notes:                  See the file License for license information

                                Large parts of this module were derived from
                                the work of Mark Jones' "Typing Haskell in
                                Haskell", (http://www.cse.ogi.edu/~mpj/thih/)

-------------------------------------------------------------------------------}
module Representation where


import AnnotatedHsSyn           (AHsName (..), AModule (..), AHsIdentifier(..))
import Env                      (listToEnv)
import PPrint
import Utils                    (fromAHsName,
                                 fst3,
                                 nameSupply)
import FiniteMaps               (FiniteMap)

--------------------------------------------------------------------------------

-- Types

data Type  = TVar Tyvar
           | TCon Tycon
           | TAp  Type Type
           | TGen Int
           | TArrow Type Type
           | TTuple [Type]
             deriving (Eq, Show)

-- Unquantified type variables

data Tyvar = Tyvar AHsName Kind
             deriving (Ord, Eq, Show)

-- Type constructors

data Tycon = Tycon AHsName Kind
             deriving (Eq, Show)

-- pretty printing for types etc:

instance PPrint Type where
  pprint t = fst $ runVarName [] Utils.nameSupply $ prettyPrintTypeM t

-- the trickery is to map TVars and TGens into nice 
-- variable names: a, b, c, d, and so on when we print them

prettyPrintTypeM :: Type -> VarName Doc
prettyPrintTypeM t
   = case t of
           TVar tyvar -> do findResult <- lookupInMap t 
                            case findResult of
                               Nothing -> do nm <- nextName
                                             updateVMap (t, nm)
                                             return (text nm)
                               Just v  -> return $ text v 
           TCon tycon -> return $ pprint tycon
           -- check for the Prelude.[] special case
           TAp t1 t2  -> do case isListCon t1 of
                               True  -> do doc  <- prettyPrintTypeM t2
                                           return $ brackets doc
                               False -> do doc1 <- prettyPrintTypeM t1
                                           doc2 <- maybeParensAp t2 
                                           return $ doc1 <+> doc2
           TGen i     -> do findResult <- lookupInMap t 
                            case findResult of
                               Nothing -> do nm <- nextName
                                             updateVMap (t, nm)
                                             return (text nm)
                               Just v  -> return $ text v 
           TArrow t1 t2 -> do doc1 <- maybeParensArrow t1
                              doc2 <- prettyPrintTypeM t2
                              return $ doc1 <> text " -> " <> doc2
           TTuple ts    -> do tsDocs <- mapM prettyPrintTypeM ts
                              return $ parens $ hcat $ punctuate comma tsDocs
    where
    -- XXX this is a bit ugly (below)
    isListCon :: Type -> Bool
    isListCon t = t == TCon (Tycon (AQual (AModule "Prelude") 
                                   (AHsIdent "[]")) (Kfun Star Star))
    -- puts parentheses around the doc for a type if needed
    maybeParensAp :: Type -> VarName Doc
    maybeParensAp t
       = do case t of
               TAp t1 _   -> do case isListCon t1 of
                                   True  -> prettyPrintTypeM t
                                   False -> do doc <- prettyPrintTypeM t
                                               return $ parens doc
               _anything  -> maybeParensArrow t
    maybeParensArrow :: Type -> VarName Doc
    maybeParensArrow t
       = do case t of
               TArrow _ _ -> do doc <- prettyPrintTypeM t
                                return $ parens doc
               _anything  -> prettyPrintTypeM t


instance PPrint Tycon where
   pprint (Tycon i k) = pprint i 

--------------------------------------------------------------------------------

-- Kinds

data Kind  = Star
           | Kfun Kind Kind
           | KVar Kindvar               -- variables aren't really allowed in haskell in kinds
             deriving (Ord, Eq, Show)   -- but we need them for kind inference

newtype Kindvar = Kindvar String deriving (Ord, Eq, Show)

instance PPrint Kind where
   pprint Star = text "*"
   pprint (Kfun Star Star) = text "*->*"
   pprint (Kfun k1   Star) = text "(" <> pprint k1 <> text ")" <> text "->*"
   pprint (Kfun Star k2)   = text "*->" <> text "(" <> pprint k2 <> text ")"
   pprint (Kfun k1   k2)   = text "(" <> pprint k1 <> text ")->(" <> pprint k2 <> text ")"
   pprint (KVar kindVar)   = pprint kindVar

instance PPrint Kindvar where
   pprint (Kindvar s) = text s 

-- * -> * == [*,*]
-- (*->*->*) -> * -> * == [(*->*->*), *, *]
unfoldKind :: Kind -> [Kind]
unfoldKind Star = [Star]
unfoldKind (KVar v) = [KVar v]
unfoldKind (Kfun k1 k2) = k1 : unfoldKind k2

--------------------------------------------------------------------------------

-- Predicates
data Pred   = IsIn Class Type
              deriving (Show, Eq)

instance PPrint Pred where
  -- pprint (IsIn c t) = pprint c <+> pprint t 
  pprint pred 
     = fst $ runVarName [] Utils.nameSupply $ prettyPrintPredM pred

prettyPrintPredM :: Pred -> VarName Doc
prettyPrintPredM (IsIn c t)
   = do typeDoc <- prettyPrintTypeM t
        return $ pprint c <+> typeDoc

-- Qualified entities  
data Qual t = [Pred] :=> t
              deriving (Show, Eq)

prettyPrintQualPredM :: Qual Pred -> VarName Doc
prettyPrintQualPredM (preds :=> pred)
   = do case preds of
           []            -> prettyPrintPredM pred 
           [p]           -> do leftPredDoc  <- prettyPrintPredM p
                               rightPredDoc <- prettyPrintPredM pred 
                               return $ hsep [leftPredDoc, text "=>", rightPredDoc]
           preds@(_:_:_) -> do docs <- mapM prettyPrintPredM preds 
                               let predsDoc = parens (hcat (punctuate comma docs)) 
                               rightPredDoc <- prettyPrintPredM pred
                               return $ hsep [predsDoc, text "=>", rightPredDoc] 

prettyPrintInst :: Inst -> Doc
prettyPrintInst inst 
   = fst $ runVarName [] Utils.nameSupply $ prettyPrintQualPredM inst

instance PPrint t => PPrint (Qual t) where
  pprint (ps :=> t) = pptuple ps <+> text "=>" <+> pprint t

-- special case for qualified types
prettyPrintQualTypeM :: Qual Type -> VarName Doc
prettyPrintQualTypeM (preds :=> t)
   = do case preds of
           []            -> prettyPrintTypeM t
           [p]           -> do predDoc <- prettyPrintPredM p 
                               typeDoc <- prettyPrintTypeM t
                               return $ hsep [predDoc, text "=>", typeDoc]
           preds@(_:_:_) -> do docs <- mapM prettyPrintPredM preds 
                               let predsDoc = parens (hcat (punctuate comma docs))
                               typeDoc <- prettyPrintTypeM t
                               return $ hsep [predsDoc, text "=>", typeDoc]
 
-- Class
type Class = AHsName

-- Instance
type Inst  = Qual Pred

--------------------------------------------------------------------------------

-- substitutions

type Subst  = FiniteMap Tyvar Type

--------------------------------------------------------------------------------

-- schemes

data Scheme = Forall [Kind] (Qual Type)
              deriving (Eq, Show)

instance PPrint Scheme where
  pprint scheme 
    = fst $ runVarName [] Utils.nameSupply $ prettyPrintSchemeM scheme

prettyPrintSchemeM :: Scheme -> VarName Doc
prettyPrintSchemeM (Forall _kinds qType)
   = prettyPrintQualTypeM qType

--------------------------------------------------------------------------------

-- assumptions

data Assump = AHsName :>: Scheme

instance PPrint Assump where
  pprint (i :>: s) = (text (show i) <+> text ":>:") $$ nest 2 (pprint s)


--------------------------------------------------------------------------------

-- a monad for matching type variables with nice names for pretty printing

newtype VarName a = VarName (State -> (a, State))

type VMap = [(Type, String)]  -- maps type (vars) to strings
type NameSupply = [String]    -- a fresh name supply 

data State =
   State {
      vmap  :: VMap,       -- the map of variables to names 
      names :: NameSupply  -- a fresh name Supply 
   }

instance Monad VarName where
    return a 
        = VarName (\state -> (a, state))
    VarName comp >>= fun   
        = VarName (\state -> let (result, newState) = comp state
                                 VarName comp' = fun result
                             in comp' newState)

runVarName :: VMap -> NameSupply -> VarName a -> (a, State)
runVarName varMap nameSupp (VarName comp)
   = (result, newState)
   where
   (result,newState)
      = comp (State {vmap  = varMap,
                     names = nameSupp})

select :: (State -> a) -> VarName a
select selector = VarName (\state -> (selector state, state))

getVMap :: VarName VMap
getVMap = select vmap 

updateVMap :: (Type, String) -> VarName ()
updateVMap newEntry
   = VarName (\state -> let oldmap = vmap state
                        in ((), state {vmap = newEntry : oldmap}))  

nextName :: VarName String
nextName 
   = VarName (\state -> let oldNames = names state
                        in (head oldNames, state {names = tail oldNames}))

lookupInMap :: Type -> VarName (Maybe String)
lookupInMap t 
   = do m <- getVMap
        return $ lookup t m 
