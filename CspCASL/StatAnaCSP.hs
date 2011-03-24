{- |
Module      :  $Header$
Description :  Static analysis of CspCASL
Copyright   :  (c) Andy Gimblett, Liam O'Reilly, Markus Roggenbach,
                   Swansea University 2008, C. Maeder, DFKI 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Static analysis of CSP-CASL specifications, following "Tool Support
for CSP-CASL", MPhil thesis by Andy Gimblett, 2008.
<http://www.cs.swan.ac.uk/~csandy/mphil/>

-}

module CspCASL.StatAnaCSP where

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.MixfixParser
import CASL.Overload (minExpFORMULA, oneExpTerm)
import CASL.Sign
import CASL.StaticAna (allConstIds, allOpIds, allPredIds)

import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Common.ConvertGlobalAnnos
import Common.Id (getRange, Id, nullRange, simpleIdToId)
import Common.Lib.State
import Common.ExtSign

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import qualified CspCASL.LocalTop as LocalTop
import CspCASL.Print_CspCASL
import CspCASL.SignCSP
import CspCASL.Symbol

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe

import Control.Monad

{- | The first element of the returned pair (CspBasicSpec) is the same
as the inputted version just with some very minor optimisations -
none in our case, but for CASL - brackets are otimized. This all
that happens, the mixfixed terms are still mixed fixed terms in
the returned version. -}
basicAnalysisCspCASL :: (CspBasicSpec, CspCASLSign, GlobalAnnos)
  -> Result (CspBasicSpec, ExtSign CspCASLSign CspSymbol, [Named CspCASLSen])
basicAnalysisCspCASL (cc, sigma, ga) =
    let Result es mga = mergeGlobalAnnos ga $ globAnnos sigma
        (_, accSig) = runState (ana_BASIC_CSP cc) $ case mga of
              Nothing -> sigma
              Just nga -> sigma { globAnnos = nga }
        ds = reverse $ envDiags accSig
        -- Extract process equations only.
        ext = extendedInfo accSig
        ccsents = reverse $ ccSentences ext
        -- Clean signature here
        cleanSig = accSig
                   { extendedInfo = ext { ccSentences = []}}
    in Result (es ++ ds) $ Just (cc
           , ExtSign cleanSig
              $ Set.unions
              $ Set.map caslToCspSymbol (declaredSymbols accSig)
              : toSymbolSet (diffCspSig ext $ extendedInfo sigma)
           , ccsents)

ana_BASIC_CSP :: CspBasicSpec -> State CspCASLSign ()
ana_BASIC_CSP cc = do
  checkLocalTops
  mapM_ anaChanDecl (channels cc)
  mapM_ anaProcItem (proc_items cc)

-- Analysis of local top elements

{- | Check a CspCASL signature for local top elements in its subsort
relation. -}
checkLocalTops :: State CspCASLSign ()
checkLocalTops = do
    sr <- gets sortRel
    {- Only error will be added if there are any probelms. If there are no
    problems no errors will be added and hets will continue as normal. -}
    addDiags $ LocalTop.checkLocalTops sr

-- Static analysis of channel declarations

-- | Statically analyse a CspCASL channel declaration.
anaChanDecl :: CHANNEL_DECL -> State CspCASLSign ()
anaChanDecl (ChannelDecl chanNames chanSort) = do
    checkSorts [chanSort] -- check channel sort is known
    sig <- get
    let ext = extendedInfo sig
        oldChanMap = chans ext
    newChanMap <- foldM (anaChannelName chanSort) oldChanMap chanNames
    sig2 <- get
    put sig2 { extendedInfo = ext { chans = newChanMap }}

-- | Statically analyse a CspCASL channel name.
anaChannelName :: SORT -> ChanNameMap -> CHANNEL_NAME
  -> State CspCASLSign ChanNameMap
anaChannelName s m chanName = do
    sig <- get
    if Set.member (simpleIdToId chanName) (sortSet sig)
      then do
        let err = "channel name already in use as a sort name"
        addDiags [mkDiag Error err chanName]
        return m
      else do
        let ts = Map.findWithDefault Set.empty chanName m
        when (Set.member s ts) $
          addDiags [mkDiag Warning "redeclared channel" chanName]
        return $ Map.insert chanName (Set.insert s ts) m

-- Static analysis of process items

-- | Statically analyse a CspCASL process item.
anaProcItem :: Annoted PROC_ITEM -> State CspCASLSign ()
anaProcItem annotedProcItem = case item annotedProcItem of
    Proc_Decl name argSorts alpha -> anaProcDecl name argSorts alpha
    Proc_Eq parmProcName procTerm ->
      anaProcEq annotedProcItem parmProcName procTerm

-- Static analysis of process declarations

-- | Statically analyse a CspCASL process declaration.
anaProcDecl :: SIMPLE_PROCESS_NAME -> PROC_ARGS -> PROC_ALPHABET
            -> State CspCASLSign ()
anaProcDecl name argSorts comms = do
    sig <- get
    let ext = extendedInfo sig
        oldProcDecls = procSet ext
    newProcDecls <- do
      -- new process declation
      profile <- anaProcAlphabet argSorts comms
      -- we no longer add (channel and) proc symbols to the CASL signature
      if isNameInProcNameMap name profile oldProcDecls
      -- Check the name (with profile) is new (for warning only)
         then -- name with profile already in signature
              do let warn = "process name redeclared with same profile '" ++
                            show (printProcProfile profile) ++ "':"
                 addDiags [mkDiag Warning warn name]
                 return oldProcDecls
         else {- New name with profile - add the name to the signature in the
              state -}
              return $ addProcNameToProcNameMap name profile oldProcDecls
    sig2 <- get
    put sig2 { extendedInfo = ext {procSet = newProcDecls }}

-- Static analysis of process equations

{- | Find a profile for a process name. Either the profile is given via a parsed
fully qualified process name, in which case we check everything is valid and
the process name with the profile is known. Or its a plain process name where
we must deduce a unique profile is possible. We also know how many variables
/ parameters the process name has. -}
findProfileForProcName :: FQ_PROCESS_NAME -> Int -> ProcNameMap ->
                          State CspCASLSign (Maybe ProcProfile)
findProfileForProcName pn numParams procNameMap =
  case pn of
    FQ_PROCESS_NAME _ _ ->
      -- We should not try to find a profile for a fully qualified process name
      error $ "CspCASL.StatAnaCsp.findProfileForProcName: Process name"
              ++ " already fully qualified: " ++ show pn
    PARSED_FQ_PROCESS_NAME pn' argSorts comms -> do
      profile <- anaProcAlphabet argSorts comms
      let profiles = Map.findWithDefault Set.empty pn' procNameMap
      if profile `Set.member` profiles
        then return $ Just profile
        else do
          addDiags [mkDiag Error
                    "Fully qualified process name not in signature" pn]
          return Nothing
    PROCESS_NAME pn' ->
      let resProfile = getUniqueProfileInProcNameMap pn' numParams procNameMap
      in case resultToMaybe resProfile of
        Nothing ->
          do addDiags $ diags resProfile
             return Nothing
        Just profile' ->
          return $ Just profile'

{- | Analyse a process name an return a fully qualified one if possible. We also
know how many variables / parameters the process name has. -}
anaProcName :: FQ_PROCESS_NAME -> Int
  -> State CspCASLSign (Maybe FQ_PROCESS_NAME)
anaProcName pn numParams = do
  sig <- get
  let ext = extendedInfo sig
      procDecls = procSet ext
      simpPn = procNameToSimpProcName pn
  maybeProf <- findProfileForProcName pn numParams procDecls
  case maybeProf of
    Nothing -> return Nothing
    Just profile ->
      -- We now construct the real fully qualified process name
      return $ Just $ FQ_PROCESS_NAME simpPn profile

-- | Statically analyse a CspCASL process equation.
anaProcEq :: Annoted a -> PARM_PROCNAME -> PROCESS -> State CspCASLSign ()
anaProcEq a (ParmProcname pn vs) proc =
  {- the 'annoted a' contains the annotation of the process equation. We do not
  care what the underlying item is in the annotation (but it probably will be
  the proc eq) -}
  do
    sig <- get
    let ext = extendedInfo sig
        ccsens = ccSentences ext
        -- procDecls = procSet ext
    maybeFqPn <- anaProcName pn (length vs)
    case maybeFqPn of
      -- Only analyse a process if its name and profile is known
      Nothing -> return ()
      Just fqPn ->
        case fqPn of
          PROCESS_NAME _ ->
            error "CspCasl.StatAnaCSP.anaProcEq: Impossible case"
          PARSED_FQ_PROCESS_NAME _ _ _ ->
            error "CspCasl.StatAnaCSP.anaProcEq: Impossible case"
          FQ_PROCESS_NAME _ prof ->
            case prof of
              ProcProfile procArgs procAlpha -> do
                gVars <- anaProcVars pn
                         procArgs vs {- compute global
                vars Change a procVarList to a FQProcVarList We do
                not care about the range as we are building fully
                qualified variables and they have already been
                checked to be ok. -}
                let mkFQProcVar (v, s) = Qual_var v s nullRange
                let fqGVars = map mkFQProcVar gVars
                (termAlpha, fqProc) <-
                  anaProcTerm proc (Map.fromList gVars) Map.empty
                checkCommAlphaSub termAlpha procAlpha proc "process equation"
                -- Save the diags from the checkCommAlphaSub
                vds <- gets envDiags
                {- put CspCASL Sentences back in to the state with new sentence
                BUG - What should the constituent alphabet be for this
                process?  probably the same as the inner one! -}
                let namedSen = makeNamedSen $
                              {- We take the annotated item and replace the
                              inner item, thus preserving the annotations. We
                              then take this annotated sentence and make it a
                              named sentence in accordance to the (if
                              existing) name in the annotations. -}
                               a {item =
                                     ProcessEq fqPn fqGVars procAlpha fqProc}
                put sig {envDiags = vds, extendedInfo =
                            ext {ccSentences = namedSen : ccsens}
                        }
                return ()
    return ()

-- | Statically analyse a CspCASL process equation's global variable names.
anaProcVars :: FQ_PROCESS_NAME -> [SORT] -> [VAR] ->
               State CspCASLSign ProcVarList
anaProcVars pn ss vs =
  let msg str = addDiags [mkDiag Error ("process name applied to " ++ str) pn]
        >> return []
  in fmap reverse $ case compare (length ss) $ length vs of
    LT -> msg "too many arguments"
    GT -> msg "not enough arguments"
    EQ -> foldM anaProcVar [] (zip vs ss)

-- | Statically analyse a CspCASL process-global variable name.
anaProcVar :: ProcVarList -> (VAR, SORT) -> State CspCASLSign ProcVarList
anaProcVar old (v, s) =
    if v `elem` map fst old
       then do
         addDiags [mkDiag Error "Process argument declared more than once" v]
         return old
       else return ((v, s) : old)

-- Static analysis of process terms

{- BUG in fucntion below
not returing FQProcesses
Statically analyse a CspCASL process term.
The process that is returned is a fully qualified process. -}
anaProcTerm :: PROCESS -> ProcVarMap -> ProcVarMap ->
               State CspCASLSign (CommAlpha, PROCESS)
anaProcTerm proc gVars lVars = case proc of
    NamedProcess name args r ->
        do addDiags [mkDiag Debug "Named process" proc]
           (fqName, al, fqArgs) <-
             anaNamedProc proc name args (lVars `Map.union` gVars)
           let fqProc = FQProcess (NamedProcess fqName fqArgs r) al r
           return (al, fqProc)
    Skip r ->
        do addDiags [mkDiag Debug "Skip" proc]
           let fqProc = FQProcess (Skip r) Set.empty r
           return (Set.empty, fqProc)
    Stop r ->
        do addDiags [mkDiag Debug "Stop" proc]
           let fqProc = FQProcess (Stop r) Set.empty r
           return (Set.empty, fqProc)
    Div r ->
        do addDiags [mkDiag Debug "Div" proc]
           let fqProc = FQProcess (Div r) Set.empty r
           return (Set.empty, fqProc)
    Run es r ->
        do addDiags [mkDiag Debug "Run" proc]
           (comms, fqEs) <- anaEventSet es
           let fqProc = FQProcess (Run fqEs r) comms r
           return (comms, fqProc)
    Chaos es r ->
        do addDiags [mkDiag Debug "Chaos" proc]
           (comms, fqEs) <- anaEventSet es
           let fqProc = FQProcess (Chaos fqEs r) comms r
           return (comms, fqProc)
    PrefixProcess e p r ->
        do addDiags [mkDiag Debug "Prefix" proc]
           (evComms, rcvMap, fqEvent) <- anaEvent e (lVars `Map.union` gVars)
           (comms, pFQTerm) <- anaProcTerm p gVars (rcvMap `Map.union` lVars)
           let newAlpha = comms `Set.union` evComms
               fqProc = FQProcess (PrefixProcess fqEvent pFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    Sequential p q r ->
        do addDiags [mkDiag Debug "Sequential" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars Map.empty
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (Sequential pFQTerm qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    InternalChoice p q r ->
        do addDiags [mkDiag Debug "InternalChoice" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (InternalChoice pFQTerm qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    ExternalChoice p q r ->
        do addDiags [mkDiag Debug "ExternalChoice" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (ExternalChoice pFQTerm qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    Interleaving p q r ->
        do addDiags [mkDiag Debug "Interleaving" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (Interleaving pFQTerm qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    SynchronousParallel p q r ->
        do addDiags [mkDiag Debug "Synchronous" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (SynchronousParallel pFQTerm
                                                       qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    GeneralisedParallel p es q r ->
        do addDiags [mkDiag Debug "Generalised parallel" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (synComms, fqEs) <- anaEventSet es
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           let newAlpha = Set.unions [pComms, qComms, synComms]
               fqProc = FQProcess (GeneralisedParallel pFQTerm fqEs qFQTerm r)
                                         newAlpha r
           return (newAlpha, fqProc)
    AlphabetisedParallel p esp esq q r ->
        do addDiags [mkDiag Debug "Alphabetised parallel" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (pSynComms, fqEsp) <- anaEventSet esp
           checkCommAlphaSub pSynComms pComms proc "alphabetised parallel, left"
           (qSynComms, fqEsq) <- anaEventSet esq
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           checkCommAlphaSub qSynComms qComms proc
                                 "alphabetised parallel, right"
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (AlphabetisedParallel pFQTerm fqEsp fqEsq
                                                        qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    Hiding p es r ->
        do addDiags [mkDiag Debug "Hiding" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (hidComms, fqEs) <- anaEventSet es
           return (pComms `Set.union` hidComms
                  , FQProcess (Hiding pFQTerm fqEs r)
                                  (pComms `Set.union` hidComms) r)
    RenamingProcess p renaming r ->
        do addDiags [mkDiag Debug "Renaming" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (renAlpha, fqRenaming) <- anaRenaming renaming
           let newAlpha = pComms `Set.union` renAlpha
               fqProc = FQProcess (RenamingProcess pFQTerm fqRenaming r)
                                         (pComms `Set.union` renAlpha) r
           return (newAlpha, fqProc)
    ConditionalProcess f p q r ->
        do addDiags [mkDiag Debug "Conditional" proc]
           (pComms, pFQTerm) <- anaProcTerm p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm q gVars lVars
           -- mfs is the fully qualified formula version of f
           mfs <- anaFormulaCspCASL (gVars `Map.union` lVars) f
           let fFQ = fromMaybe f mfs
               fComms = maybe Set.empty formulaComms mfs
               newAlpha = Set.unions [pComms, qComms, fComms]
               fqProc = FQProcess (ConditionalProcess fFQ pFQTerm qFQTerm r)
                        newAlpha r
           return (newAlpha, fqProc)
    FQProcess _ _ _ ->
        error "CspCASL.StatAnaCSP.anaProcTerm: Unexpected FQProcess"

{- | Statically analyse a CspCASL "named process" term. Return the
permitted alphabet of the process and also a list of the fully qualified
version of the inputted terms.
BUG !!! the FQ_PROCESS_NAME may actually need to be a simple process name -}
anaNamedProc :: PROCESS -> FQ_PROCESS_NAME -> [TERM ()] -> ProcVarMap ->
                State CspCASLSign (FQ_PROCESS_NAME, CommAlpha, [TERM ()])
anaNamedProc proc pn terms procVars = do
  maybeFqPn <- anaProcName pn (length terms)
  case maybeFqPn of
    Nothing ->
      {- Return the empty alphabet and the original
      terms. There is an error in the spec. -}
      return (pn, Set.empty, terms)
    Just fqPn ->
      case fqPn of
        PROCESS_NAME _ ->
          error "CspCasl.StatAnaCSP.anaNamedProc: Impossible case"
        PARSED_FQ_PROCESS_NAME _ _ _ ->
          error "CspCasl.StatAnaCSP.anaNamedProc: Impossible case"
        FQ_PROCESS_NAME _ (ProcProfile varSorts permAlpha) ->
          if length terms == length varSorts
          then do
            fqTerms <-
                    mapM (anaNamedProcTerm procVars) (zip terms varSorts)
                  {- Return the permitted alphabet of the process and
                  the fully qualifed terms -}
            return (fqPn, permAlpha, fqTerms)
          else do
            let err = "Wrong number of arguments in named process"
            addDiags [mkDiag Error err proc]
                  {- Return the empty alphabet and the original
                  terms. There is an error in the spec. -}
            return (pn, Set.empty, terms)

{- | Statically analysis a CASL term occurring in a CspCASL "named
process" term. -}
anaNamedProcTerm :: ProcVarMap -> (TERM (), SORT) -> State CspCASLSign (TERM ())
anaNamedProcTerm pm (t, expSort) = do
    mt <- anaTermCspCASL pm t
    sig <- get
    case mt of
      Nothing -> return t {- CASL term analysis failed. Use old term
                          as the fully qualified term, there is a
                          error in the spec anyway. -}
      Just at -> do
        let Result ds at' = ccTermCast at expSort sig -- attempt cast;
        addDiags ds
        case at' of
          Nothing -> {- Use old term as the fully
                     qualified term, there is a error
                     in the spec anyway. -}
                               return t
          Just at'' -> return at'' {- Use the fully
                                   qualified
                                   (possibly cast)
                                   term -}

-- Static analysis of event sets and communication types

{- | Statically analyse a CspCASL event set. Returns the alphabet of
the event set and a fully qualified version of the event set. -}
anaEventSet :: EVENT_SET -> State CspCASLSign (CommAlpha, EVENT_SET)
anaEventSet eventSet =
    case eventSet of
      EventSet es r ->
          do sig <- get
             -- fqEsElems is built the reversed order for efficiency.
             (comms, fqEsElems) <- foldM (anaCommType sig)
                                   (Set.empty, []) es
             vds <- gets envDiags
             put sig { envDiags = vds }
             -- reverse the list inside the event set
             return (comms, FQEventSet (reverse fqEsElems) r)
      FQEventSet _ _ ->
          error "CspCASL.StatAnaCSP.anaEventSet: Unexpected FQEventSet"


{- | Statically analyse a proc alphabet (i.e., a list of channel and sort
identifiers) to yeild a list of sorts and typed channel names. We also check
the parameter sorts and actually construct a process profile. -}
anaProcAlphabet :: PROC_ARGS -> PROC_ALPHABET ->
                   State CspCASLSign ProcProfile
anaProcAlphabet argSorts (ProcAlphabet commTypes _) = do
  sig <- get
  checkSorts argSorts {- check argument sorts are known build alphabet: set of
      CommType values. We do not need the fully qualfied commTypes that are
      returned (these area used for analysing Event Sets) -}
  (alpha, _ ) <- foldM (anaCommType sig) (Set.empty, []) commTypes
  let profile =
        closeProcProfileSortRel (sortRel sig) (ProcProfile argSorts alpha)
  return profile

{- | Statically analyse a CspCASL communication type. Returns the
extended alphabet and the extended list of fully qualified event
set elements - [CommType]. -}
anaCommType :: CspCASLSign -> (CommAlpha, [CommType]) -> COMM_TYPE ->
               State CspCASLSign (CommAlpha, [CommType])
anaCommType sig (alpha, fqEsElems) ct = let ctSort = simpleIdToId ct in
    if Set.member ctSort (sortSet sig)
      then {- ct is a sort name; insert sort into alpha and add a sort
           to the fully qualified event set elements. -}
        let newAlpha = Set.insert (CommTypeSort ctSort) alpha
            newFqEsElems = CommTypeSort ctSort : fqEsElems
        in return (newAlpha, newFqEsElems)
      else -- ct not a sort name, so should be a channel name
        case Set.toList $ Map.findWithDefault Set.empty ct $ chans
               $ extendedInfo sig of
        [] -> do
           let err = "not a sort or channel name"
           addDiags [mkDiag Error err ct]
                        {- failed, thus error in spec, return the
                        unmodified alphabet and the unmodifled
                        fully qualified event set elements. -}
           return (alpha, fqEsElems)
        ts -> let tcs = map (CommTypeChan . TypedChanName ct) ts
                    {- ct is a channel name; insert typed chan name
                    into alpha and add typed channel to the fully
                    qualified event set elemenets. -}
              in return (Set.union alpha $ Set.fromList tcs, tcs ++ fqEsElems)

-- Static analysis of events

{- | Statically analyse a CspCASL event. Returns a constituent
communication alphabet of the event, mapping for any new
locally bound variables and a fully qualified version of the event. -}
anaEvent :: EVENT -> ProcVarMap ->
            State CspCASLSign (CommAlpha, ProcVarMap, EVENT)
anaEvent e vars =
    case e of
      TermEvent t range ->
          do addDiags [mkDiag Debug "Term event" e]
             (alpha, newVars, fqTerm) <- anaTermEvent t vars
             let fqEvent = FQEvent e Nothing fqTerm range
             return (alpha, newVars, fqEvent)
      InternalPrefixChoice v s range ->
          do addDiags [mkDiag Debug "Internal prefix event" e]
             (alpha, newVars, fqVar) <- anaPrefixChoice v s
             let fqEvent = FQEvent e Nothing fqVar range
             return (alpha, newVars, fqEvent)
      ExternalPrefixChoice v s range ->
          do addDiags [mkDiag Debug "External prefix event" e]
             (alpha, newVars, fqVar) <- anaPrefixChoice v s
             let fqEvent = FQEvent e Nothing fqVar range
             return (alpha, newVars, fqEvent)
      ChanSend c t range ->
          do addDiags [mkDiag Debug "Channel send event" e]
             {- mfqChan is a maybe fully qualified
             channel. It will be Nothing if
             annChanSend failed - i.e. we forget
             about the channel. -}
             (alpha, newVars, mfqChan, fqTerm) <- anaChanSend c t vars
             let fqEvent = FQEvent e mfqChan fqTerm range
             return (alpha, newVars, fqEvent)
      ChanNonDetSend c v s range ->
          do addDiags [mkDiag Debug "Channel nondeterministic send event" e]
             {- mfqChan is the same as in chanSend case.
             fqVar is the fully qualfied version of the variable. -}
             (alpha, newVars, mfqChan, fqVar) <- anaChanBinding c v s
             let fqEvent = FQEvent e mfqChan fqVar range
             return (alpha, newVars, fqEvent)
      ChanRecv c v s range ->
          do addDiags [mkDiag Debug "Channel receive event" e]
             {- mfqChan is the same as in chanSend case.
             fqVar is the fully qualfied version of the variable. -}
             (alpha, newVars, mfqChan, fqVar) <- anaChanBinding c v s
             let fqEvent = FQEvent e mfqChan fqVar range
             return (alpha, newVars, fqEvent)
      FQEvent _ _ _ _ ->
          error "CspCASL.StatAnaCSP.anaEvent: Unexpected FQEvent"

{- | Statically analyse a CspCASL term event. Returns a constituent
communication alphabet of the event and a mapping for any new
locally bound variables and the fully qualified version of the
term. -}
anaTermEvent :: TERM () -> ProcVarMap
  -> State CspCASLSign (CommAlpha, ProcVarMap, TERM ())
anaTermEvent t vars = do
  mt <- anaTermCspCASL vars t
  let (alpha, t') = case mt of
                      -- return the alphabet and the fully qualified term
                      Just at -> ([CommTypeSort (sortOfTerm at)], at)
                      -- return the empty alphabet and the original term
                      Nothing -> ([], t)
  return (Set.fromList alpha, Map.empty, t')


{- | Statically analyse a CspCASL internal or external prefix choice
event. Returns a constituent communication alphabet of the event
and a mapping for any new locally bound variables and the fully
qualified version of the variable. -}
anaPrefixChoice :: VAR -> SORT ->
                   State CspCASLSign (CommAlpha, ProcVarMap, TERM ())
anaPrefixChoice v s = do
  checkSorts [s] -- check sort is known
  let alpha = Set.singleton $ CommTypeSort s
  let binding = Map.singleton v s
  let fqVar = Qual_var v s nullRange
  return (alpha, binding, fqVar)

{- | Statically analyse a CspCASL channel send event. Returns a
constituent communication alphabet of the event, a mapping for
any new locally bound variables, a fully qualified channel (if
possible) and the fully qualified version of the term. -}
anaChanSend :: CHANNEL_NAME -> TERM () -> ProcVarMap
  -> State CspCASLSign
     (CommAlpha, ProcVarMap, Maybe (CHANNEL_NAME, SORT), TERM ())
anaChanSend c t vars = do
  sig <- get
  let ext = extendedInfo sig
  case Set.toList $ Map.findWithDefault Set.empty c $ chans ext of
    [] -> do
      addDiags [mkDiag Error "unknown channel" c]
      {- Use old term as the fully qualified term and forget about the
      channel, there is an error in the spec -}
      return (Set.empty, Map.empty, Nothing, t)
    chanSorts -> do
      mt <- anaTermCspCASL vars t
      case mt of
        Nothing ->
          {- CASL analysis failed. Use old term as the fully
          qualified term and forget about the channel,
          there is an error in the spec. -}
          return (Set.empty, Map.empty, Nothing, t)
        Just at -> do
          let rs = map (\ s -> ccTermCast at s sig) chanSorts
          addDiags $ concatMap diags rs
          case filter (isJust . maybeResult . fst) $ zip rs chanSorts of
            [] ->
              {- cast failed. Use old term as the fully
              qualified term, and forget about the
              channel there is an error in the spec. -}
              return (Set.empty, Map.empty, Nothing, t)
            [(_, castSort)] ->
              let alpha = [ CommTypeSort castSort
                          , CommTypeChan $ TypedChanName c castSort]
                        {- Use the real fully qualified term. We do
                        not want to use a cast term here. A cast
                        must be possible, but we do not want to
                        force it! -}
              in return (Set.fromList alpha, Map.empty, Just (c, castSort), at)
            cts -> do -- fail due to an ambiguous chan sort
              addDiags [mkDiag Error
                   ("ambiguous channel sorts " ++ show (map snd cts)) t]
              return (Set.empty, Map.empty, Nothing, t)

getDeclaredChanSort :: Maybe (CHANNEL_NAME, SORT) -> CspCASLSign
  -> Result SORT
getDeclaredChanSort mc sig = let cm = chans $ extendedInfo sig in case mc of
  Nothing -> fail "no channel data"
  Just (c, s) -> case Set.toList $ Map.findWithDefault Set.empty c cm of
    [] -> mkError "unknown channel" c
    css -> case filter (\ cs -> cs == s || Set.member s (subsortsOf cs sig))
           css of
     [] -> mkError "sort not a subsort of channel's sort" s
     [cs] -> return cs
     fcs -> mkError ("ambiguous channel sorts " ++ show fcs) s

{- | Statically analyse a CspCASL "binding" channel event (which is
either a channel nondeterministic send event or a channel receive
event). Returns a constituent communication alphabet of the event,
a mapping for any new locally bound variables, a fully qualified
channel (if possible) and the fully qualified version of the
variable. -}
anaChanBinding :: CHANNEL_NAME -> VAR -> SORT
  -> State CspCASLSign
     (CommAlpha, ProcVarMap, Maybe (CHANNEL_NAME, SORT), TERM ())
anaChanBinding c v s = do
  checkSorts [s] -- check sort is known
  sig <- get
  let qv = Qual_var v s nullRange
      jcs = Just (c, s)
      Result ds ms = getDeclaredChanSort jcs sig
  addDiags ds
  case ms of
    Nothing -> return (Set.empty, Map.empty, jcs, qv)
    Just _ ->
        let alpha = [CommTypeSort s, CommTypeChan (TypedChanName c s)]
            binding = [(v, s)]
                              {- Return the alphabet, var mapping, the fully
                              qualfied channel and fully qualfied
                              variable. Notice that the fully qualified
                              channel's sort should be the lowest sort we can
                              communicate in i.e. the sort of the variable. -}
        in return (Set.fromList alpha, Map.fromList binding, jcs, qv)

-- Static analysis of renaming and renaming items

{- | Statically analyse a CspCASL renaming. Returns the alphabet and
the fully qualified renaming. -}
anaRenaming :: RENAMING -> State CspCASLSign (CommAlpha, RENAMING)
anaRenaming renaming = case renaming of
  Renaming r -> do
    (al, fqRenamingTermsMaybes) <- foldM anaRenamingItem (Set.empty, []) r
    return (al, FQRenaming fqRenamingTermsMaybes)
  FQRenaming _ ->
      error "CspCASL.StatAnaCSP.anaRenaming: Unexpected FQRenaming"

{- | Statically analyse a CspCASL renaming item. Return the alphabet
and the fully qualified list of renaming functions and predicates. -}
anaRenamingItem :: (CommAlpha, [TERM ()]) -> Id ->
                   State CspCASLSign (CommAlpha, [TERM ()])
anaRenamingItem (inAl, fqRenamingTerms) ri = do
-- BUG -- too many nothings - should only be one
  totOps <- getUnaryOpsById ri Total
  if not (Set.null totOps)
    then return (inAl `Set.union` totOps, fqRenamingTerms)
    else do
      parOps <- getUnaryOpsById ri Partial
      if not (Set.null parOps)
        then return (inAl `Set.union` parOps, fqRenamingTerms)
        else do
          preds <- getBinPredsById ri
          if not (Set.null preds)
            then return (inAl `Set.union` preds, fqRenamingTerms)
            else do
              let err = "renaming item not a binary "
                        ++ "operation or predicate name"
              addDiags [mkDiag Error err ri]
              {- return the original alphabet and the original fully
              qualified terms (renamings) with out any modification
              as there is an error in the spec. -}
              return (inAl, fqRenamingTerms)

{- | Given a CASL identifier and a `function kind' (total or partial),
find all unary operations of that kind with that name in the CASL
signature, and return a set of corresponding communication types
for those operations. -}
getUnaryOpsById :: Id -> OpKind -> State CspCASLSign (Set.Set CommType)
getUnaryOpsById ri kind = do
    sig <- get
    let opsWithId = Map.findWithDefault Set.empty ri (opMap sig)
        binOpsKind = Set.filter (isBin kind) opsWithId
        cts = Set.map CommTypeSort $ Set.fold opSorts Set.empty binOpsKind
    return cts
      where isBin k ot = k == opKind ot && 1 == length (opArgs ot)
            opSorts o inS = Set.union inS $ Set.fromList $ opRes o : opArgs o

{- | Given a CASL identifier find all binary predicates with that name
in the CASL signature, and return a set of corresponding
communication types for those predicates. -}
getBinPredsById :: Id -> State CspCASLSign (Set.Set CommType)
getBinPredsById ri = do
    sig <- get
    let predsWithId = Map.findWithDefault Set.empty ri (predMap sig)
        binPreds = Set.filter isBin predsWithId
        cts = Set.map CommTypeSort $ Set.fold predSorts Set.empty binPreds
    return cts
      where isBin ot = 2 == length (predArgs ot)
            predSorts p inS = inS `Set.union` Set.fromList (predArgs p)

{- | Given two CspCASL communication alphabets, check that the first's
subsort closure is a subset of the second's subsort closure. -}
checkCommAlphaSub :: CommAlpha -> CommAlpha -> PROCESS -> String
  -> State CspCASLSign ()
checkCommAlphaSub sub super proc context = do
  sr <- gets sortRel
  let extras = closeCspCommAlpha sr sub
        `Set.difference` closeCspCommAlpha sr super
  unless (Set.null extras) $
            let err = "Communication alphabet subset violations (" ++
                       context ++ "): " ++ show (Set.toList extras)
            in addDiags [mkDiag Error err proc]

-- Static analysis of CASL terms occurring in CspCASL process terms.

{- | Statically analyse a CASL term appearing in a CspCASL process;
any in-scope process variables are added to the signature before
performing the analysis. -}
anaTermCspCASL :: ProcVarMap -> TERM () -> State CspCASLSign (Maybe (TERM ()))
anaTermCspCASL pm t = do
    sig <- get
    let newVars = Map.union pm (varMap sig)
        sigext = sig { varMap = newVars }
        Result ds mt = anaTermCspCASL' sigext t
    addDiags ds
    return mt

idSetOfSig :: CspCASLSign -> IdSets
idSetOfSig sig =
  unite [mkIdSets (allConstIds sig) (allOpIds sig) $ allPredIds sig]

{- | Statically analyse a CASL term in the context of a CspCASL
signature.  If successful, returns a fully-qualified term. -}
anaTermCspCASL' :: CspCASLSign -> TERM () -> Result (TERM ())
anaTermCspCASL' sig trm = do
    let ga = globAnnos sig
        mix = extendMix (Map.keysSet $ varMap sig)
              emptyMix { mixRules = makeRules ga $ idSetOfSig sig }
    resT <- resolveMixfix (putParen mix) (mixResolve mix)
                 ga (mixRules mix) trm
    oneExpTerm (const return) sig resT

-- | Attempt to cast a CASL term to a particular CASL sort.
ccTermCast :: TERM () -> SORT -> CspCASLSign -> Result (TERM ())
ccTermCast t cSort sig = let
  pos = getRange t
  msg = (++ "cast term to sort " ++ show cSort)
  in case optTermSort t of
  Nothing -> mkError "term without type" t
  Just termSort
    | termSort == cSort -> return t
    | Set.member termSort $ subsortsOf cSort sig ->
        hint (Sorted_term t cSort pos) (msg "up") pos
    | Set.member termSort $ supersortsOf cSort sig ->
        hint (Cast t cSort pos) (msg "down") pos
    | otherwise -> fatal_error (msg "cannot ") pos

{- Static analysis of CASL formulae occurring in CspCASL process
terms. -}

{- | Statically analyse a CASL formula appearing in a CspCASL process;
any in-scope process variables are added to the signature before
performing the analysis. -}
anaFormulaCspCASL :: ProcVarMap -> FORMULA ()
  -> State CspCASLSign (Maybe (FORMULA ()))
anaFormulaCspCASL pm f = do
    addDiags [mkDiag Debug "anaFormulaCspCASL" f]
    sig <- get
    let newVars = Map.union pm (varMap sig)
        sigext = sig { varMap = newVars }
        Result ds mt = anaFormulaCspCASL' sigext f
    addDiags ds
    return mt

{- | Statically analyse a CASL formula in the context of a CspCASL
signature.  If successful, returns a fully-qualified formula. -}
anaFormulaCspCASL' :: CspCASLSign -> FORMULA () -> Result (FORMULA ())
anaFormulaCspCASL' sig frm = do
    let ga = globAnnos sig
        mix = extendMix (Map.keysSet $ varMap sig)
              emptyMix { mixRules = makeRules ga $ idSetOfSig sig }
    resF <- resolveFormula (putParen mix) (mixResolve mix) ga (mixRules mix) frm
    minExpFORMULA (const return) sig resF

{- | Compute the communication alphabet arising from a formula
occurring in a CspCASL process term. -}
formulaComms :: FORMULA () -> CommAlpha
formulaComms = Set.map CommTypeSort . foldFormula
  (constRecord (const Set.empty) Set.unions Set.empty)
  { foldQuantification = \ _ _ varDecls f _ ->
      let vdSort (Var_decl _ s _) = s in
      Set.union f $ Set.fromList (map vdSort varDecls)
  , foldQual_var = \ _ _ s _ -> Set.singleton s
  , foldApplication = \ _ o _ _ -> case o of
       Op_name _ -> Set.empty
       Qual_op_name _ ty _ -> Set.singleton $ res_OP_TYPE ty
  , foldSorted_term = \ _ _ s _ -> Set.singleton s
  , foldCast = \ _ _ s _ -> Set.singleton s }
