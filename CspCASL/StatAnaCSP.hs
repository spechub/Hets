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
import CASL.Quantification
import CASL.Sign
import CASL.StaticAna
import CASL.ToDoc ()

import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Common.Id
import Common.Lib.State
import Common.ExtSign
import qualified Common.Lib.MapSet as MapSet

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

type CspBasicSpec = BASIC_SPEC CspBasicExt () CspSen

{- | The first element of the returned pair (CspBasicSpec) is the same
as the inputted version just with some very minor optimisations -
none in our case, but for CASL - brackets are otimized. This all
that happens, the mixfixed terms are still mixed fixed terms in
the returned version. -}
basicAnalysisCspCASL :: (CspBasicSpec, CspCASLSign, GlobalAnnos)
  -> Result (CspBasicSpec, ExtSign CspCASLSign CspSymbol, [Named CspCASLSen])
basicAnalysisCspCASL inp@(_, insig, _) = do
  (bs, ExtSign sig syms, sens) <- basicAnaAux inp
  -- check for local top elements in the subsort relation
  appendDiags $ LocalTop.checkLocalTops $ sortRel sig
  let ext = extendedInfo sig
  return (bs, ExtSign sig $ Set.unions
             $ Set.map caslToCspSymbol syms
             : toSymbolSet (diffCspSig ext $ extendedInfo insig), sens)

basicAnaAux :: (CspBasicSpec, CspCASLSign, GlobalAnnos)
  -> Result (CspBasicSpec, ExtSign CspCASLSign Symbol, [Named CspCASLSen])
basicAnaAux =
  basicAnalysis (const return) ana_BASIC_CSP (const return) emptyMix

ana_BASIC_CSP :: Ana CspBasicExt CspBasicExt () CspSen CspSign
ana_BASIC_CSP mix bs = do
  let caslMix = emptyMix
        { mixRules = mixRules mix }
  case bs of
    Channels cs _ -> mapM_ (anaChanDecl . item) cs
    ProcItems ps _ -> mapM_ (anaProcItem caslMix) ps
  return bs

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
    if Set.member chanName (sortSet sig)
      then do
        let err = "channel name already in use as a sort name"
        addDiags [mkDiag Error err chanName]
        return m
      else do
        when (MapSet.member chanName s m) $
          addDiags [mkDiag Warning "redeclared channel" chanName]
        return $ MapSet.insert chanName s m

-- Static analysis of process items

-- | Statically analyse a CspCASL process item.
anaProcItem :: Mix b s () () -> Annoted PROC_ITEM -> State CspCASLSign ()
anaProcItem mix annotedProcItem = case item annotedProcItem of
    Proc_Decl name argSorts alpha -> anaProcDecl name argSorts alpha
    Proc_Defn name args alpha procTerm -> do
      let vs = flatVAR_DECLs args
          argSorts = map snd vs
          alpha' = case alpha of
            ProcAlphabet alpha'' -> Set.fromList alpha''
          procProfile = ProcProfile argSorts alpha'
          pn = ParmProcname (FQ_PROCESS_NAME name procProfile) $ map fst vs
      anaProcDecl name argSorts alpha
      anaProcEq mix annotedProcItem pn procTerm
    Proc_Eq parmProcName procTerm ->
      anaProcEq mix annotedProcItem parmProcName procTerm

-- Static analysis of process declarations

-- | Statically analyse a CspCASL process declaration.
anaProcDecl :: PROCESS_NAME -> PROC_ARGS -> PROC_ALPHABET
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
we must deduce a unique profile if possible. We also know how many variables
/ parameters the process name has. -}
findProfileForProcName :: FQ_PROCESS_NAME -> Int -> ProcNameMap ->
                          State CspCASLSign (Maybe ProcProfile)
findProfileForProcName pn numParams procNameMap =
  case pn of
    FQ_PROCESS_NAME pn' (ProcProfile argSorts comms) -> do
      procProfile <- anaProcAlphabet argSorts $ ProcAlphabet $ Set.toList comms
      if MapSet.member pn' procProfile procNameMap
        then return $ Just procProfile
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
    Just procProfile ->
      -- We now construct the real fully qualified process name
      return $ Just $ FQ_PROCESS_NAME simpPn procProfile

-- | Statically analyse a CspCASL process equation.
anaProcEq :: Mix b s () () -> Annoted a -> PARM_PROCNAME -> PROCESS
  -> State CspCASLSign ()
anaProcEq mix a (ParmProcname pn vs) proc =
  {- the 'annoted a' contains the annotation of the process equation. We do not
  care what the underlying item is in the annotation (but it probably will be
  the proc eq) -}
  do
    maybeFqPn <- anaProcName pn (length vs)
    case maybeFqPn of
      -- Only analyse a process if its name and profile is known
      Nothing -> return ()
      Just fqPn ->
        case fqPn of
          PROCESS_NAME _ ->
            error "CspCasl.StatAnaCSP.anaProcEq: Impossible case"
          FQ_PROCESS_NAME _ (ProcProfile argSorts commAlpha) -> do
                gVars <- anaProcVars pn
                         argSorts vs {- compute global
                vars Change a procVarList to a FQProcVarList We do
                not care about the range as we are building fully
                qualified variables and they have already been
                checked to be ok. -}
                let mkFQProcVar (v, s) = Qual_var v s nullRange
                    fqGVars = map mkFQProcVar gVars
                (termAlpha, fqProc) <-
                  anaProcTerm mix proc (Map.fromList gVars) Map.empty
                checkCommAlphaSub termAlpha commAlpha proc "process equation"
                {- put CspCASL Sentences back in to the state with new sentence
                BUG - What should the constituent alphabet be for this
                process?  probably the same as the inner one! -}
                addSentences [makeNamedSen $
                              {- We take the annotated item and replace the
                              inner item, thus preserving the annotations. We
                              then take this annotated sentence and make it a
                              named sentence in accordance to the (if
                              existing) name in the annotations. -}
                               a {item = ExtFORMULA
                                   $ ProcessEq fqPn fqGVars commAlpha fqProc}]

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
anaProcTerm :: Mix b s () () -> PROCESS -> ProcVarMap -> ProcVarMap
  -> State CspCASLSign (CommAlpha, PROCESS)
anaProcTerm mix proc gVars lVars = case proc of
    NamedProcess name args r ->
        do addDiags [mkDiag Debug "Named process" proc]
           (fqName, al, fqArgs) <-
             anaNamedProc mix proc name args (lVars `Map.union` gVars)
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
           (evComms, rcvMap, fqEvent) <-
               anaEvent mix e (lVars `Map.union` gVars)
           (comms, pFQTerm) <-
               anaProcTerm mix p gVars (rcvMap `Map.union` lVars)
           let newAlpha = comms `Set.union` evComms
               fqProc = FQProcess (PrefixProcess fqEvent pFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    Sequential p q r ->
        do addDiags [mkDiag Debug "Sequential" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm mix q gVars Map.empty
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (Sequential pFQTerm qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    InternalChoice p q r ->
        do addDiags [mkDiag Debug "InternalChoice" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm mix q gVars lVars
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (InternalChoice pFQTerm qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    ExternalChoice p q r ->
        do addDiags [mkDiag Debug "ExternalChoice" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm mix q gVars lVars
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (ExternalChoice pFQTerm qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    Interleaving p q r ->
        do addDiags [mkDiag Debug "Interleaving" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm mix q gVars lVars
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (Interleaving pFQTerm qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    SynchronousParallel p q r ->
        do addDiags [mkDiag Debug "Synchronous" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm mix q gVars lVars
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (SynchronousParallel pFQTerm
                                                       qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    GeneralisedParallel p es q r ->
        do addDiags [mkDiag Debug "Generalised parallel" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (synComms, fqEs) <- anaEventSet es
           (qComms, qFQTerm) <- anaProcTerm mix q gVars lVars
           let newAlpha = Set.unions [pComms, qComms, synComms]
               fqProc = FQProcess (GeneralisedParallel pFQTerm fqEs qFQTerm r)
                                         newAlpha r
           return (newAlpha, fqProc)
    AlphabetisedParallel p esp esq q r ->
        do addDiags [mkDiag Debug "Alphabetised parallel" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (pSynComms, fqEsp) <- anaEventSet esp
           checkCommAlphaSub pSynComms pComms proc "alphabetised parallel, left"
           (qSynComms, fqEsq) <- anaEventSet esq
           (qComms, qFQTerm) <- anaProcTerm mix q gVars lVars
           checkCommAlphaSub qSynComms qComms proc
                                 "alphabetised parallel, right"
           let newAlpha = pComms `Set.union` qComms
               fqProc = FQProcess (AlphabetisedParallel pFQTerm fqEsp fqEsq
                                                        qFQTerm r) newAlpha r
           return (newAlpha, fqProc)
    Hiding p es r ->
        do addDiags [mkDiag Debug "Hiding" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (hidComms, fqEs) <- anaEventSet es
           return (pComms `Set.union` hidComms
                  , FQProcess (Hiding pFQTerm fqEs r)
                                  (pComms `Set.union` hidComms) r)
    RenamingProcess p renaming r ->
        do addDiags [mkDiag Debug "Renaming" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (renAlpha, fqRenaming) <- anaRenaming renaming
           let newAlpha = pComms `Set.union` renAlpha
               fqProc = FQProcess (RenamingProcess pFQTerm fqRenaming r)
                                         (pComms `Set.union` renAlpha) r
           return (newAlpha, fqProc)
    ConditionalProcess f p q r ->
        do addDiags [mkDiag Debug "Conditional" proc]
           (pComms, pFQTerm) <- anaProcTerm mix p gVars lVars
           (qComms, qFQTerm) <- anaProcTerm mix q gVars lVars
           -- mfs is the fully qualified formula version of f
           mfs <- anaFormulaCspCASL mix (gVars `Map.union` lVars) f
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
anaNamedProc :: Mix b s () () -> PROCESS -> FQ_PROCESS_NAME -> [TERM ()]
  -> ProcVarMap -> State CspCASLSign (FQ_PROCESS_NAME, CommAlpha, [TERM ()])
anaNamedProc mix proc pn terms procVars = do
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
        FQ_PROCESS_NAME _ (ProcProfile argSorts permAlpha) ->
          if length terms == length argSorts
          then do
            fqTerms <-
                    mapM (anaNamedProcTerm mix procVars) (zip terms argSorts)
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
anaNamedProcTerm :: Mix b s () () -> ProcVarMap -> (TERM (), SORT)
  -> State CspCASLSign (TERM ())
anaNamedProcTerm mix pm (t, expSort) = do
    mt <- anaTermCspCASL mix pm t
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
             return (comms, EventSet (reverse fqEsElems) r)

{- | Statically analyse a proc alphabet (i.e., a list of channel and sort
identifiers) to yeild a list of sorts and typed channel names. We also check
the parameter sorts and actually construct a process profile. -}
anaProcAlphabet :: PROC_ARGS -> PROC_ALPHABET ->
                   State CspCASLSign ProcProfile
anaProcAlphabet argSorts (ProcAlphabet commTypes) = do
  sig <- get
  checkSorts argSorts {- check argument sorts are known build alphabet: set of
      CommType values. We do not need the fully qualfied commTypes that are
      returned (these area used for analysing Event Sets) -}
  (alpha, _ ) <- foldM (anaCommType sig) (Set.empty, []) commTypes
  let profile = reduceProcProfile (sortRel sig) (ProcProfile argSorts alpha)
  return profile

{- | Statically analyse a CspCASL communication type. Returns the
extended alphabet and the extended list of fully qualified event
set elements - [CommType]. -}
anaCommType :: CspCASLSign -> (CommAlpha, [CommType]) -> CommType ->
               State CspCASLSign (CommAlpha, [CommType])
anaCommType sig (alpha, fqEsElems) ct =
  let res = return (Set.insert ct alpha, ct : fqEsElems)
      old = return (alpha, fqEsElems)
      getChSrts ch = Set.toList $ MapSet.lookup ch $ chans
        $ extendedInfo sig
      chRes ch rs = let tcs = map (CommTypeChan . TypedChanName ch) rs
        in return (Set.union alpha $ Set.fromList tcs, tcs ++ fqEsElems)
  in case ct of
  CommTypeSort sid -> if Set.member sid (sortSet sig) then res else
    case getChSrts sid of
      [] -> do
        addDiags [mkDiag Error "unknown sort or channel" sid]
        old
      cs -> chRes sid cs
  CommTypeChan (TypedChanName ch sid) ->
    if Set.member sid (sortSet sig) then
    case getChSrts ch of
      [] -> do
        addDiags [mkDiag Error "unknown channel" ch]
        old
      ts -> case filter (\ s -> s == sid || Set.member sid
              (subsortsOf s sig) || Set.member s (subsortsOf sid sig)) ts of
        [] -> do
          let mess = "found no suitably sort '"
                ++ shows sid "' for channel"
          addDiags [mkDiag Error mess ch]
          old
        rs -> chRes ch rs
    else do
      let mess = "unknow sort '" ++ shows sid "' for channel"
      addDiags [mkDiag Error mess ch]
      old

-- Static analysis of events

{- | Statically analyse a CspCASL event. Returns a constituent
communication alphabet of the event, mapping for any new
locally bound variables and a fully qualified version of the event. -}
anaEvent :: Mix b s () () -> EVENT -> ProcVarMap
  -> State CspCASLSign (CommAlpha, ProcVarMap, EVENT)
anaEvent mix e vars =
    case e of
      TermEvent t range ->
          do addDiags [mkDiag Debug "Term event" e]
             (alpha, newVars, fqTerm) <- anaTermEvent mix t vars
             let fqEvent = FQTermEvent fqTerm range
             return (alpha, newVars, fqEvent)
      InternalPrefixChoice v s range ->
          do addDiags [mkDiag Debug "Internal prefix event" e]
             (alpha, newVars, fqVar) <- anaPrefixChoice v s
             let fqEvent = FQInternalPrefixChoice fqVar range
             return (alpha, newVars, fqEvent)
      ExternalPrefixChoice v s range ->
          do addDiags [mkDiag Debug "External prefix event" e]
             (alpha, newVars, fqVar) <- anaPrefixChoice v s
             let fqEvent = FQExternalPrefixChoice fqVar range
             return (alpha, newVars, fqEvent)
      ChanSend c t range ->
          do addDiags [mkDiag Debug "Channel send event" e]
             {- mfqChan is a maybe fully qualified
             channel. It will be Nothing if
             annChanSend failed - i.e. we forget
             about the channel. -}
             (alpha, newVars, mfqChan, fqTerm) <- anaChanSend mix c t vars
             let fqEvent = FQChanSend mfqChan fqTerm range
             return (alpha, newVars, fqEvent)
      ChanNonDetSend c v s range ->
          do addDiags [mkDiag Debug "Channel nondeterministic send event" e]
             {- mfqChan is the same as in chanSend case.
             fqVar is the fully qualfied version of the variable. -}
             (alpha, newVars, mfqChan, fqVar) <- anaChanBinding c v s
             let fqEvent = FQChanNonDetSend mfqChan fqVar range
             return (alpha, newVars, fqEvent)
      ChanRecv c v s range ->
          do addDiags [mkDiag Debug "Channel receive event" e]
             {- mfqChan is the same as in chanSend case.
             fqVar is the fully qualfied version of the variable. -}
             (alpha, newVars, mfqChan, fqVar) <- anaChanBinding c v s
             let fqEvent = FQChanRecv mfqChan fqVar range
             return (alpha, newVars, fqEvent)
      _ -> error
           "CspCASL.StatAnaCSP.anaEvent: Unexpected Fully qualified event"

{- | Statically analyse a CspCASL term event. Returns a constituent
communication alphabet of the event and a mapping for any new
locally bound variables and the fully qualified version of the
term. -}
anaTermEvent :: Mix b s () () -> TERM () -> ProcVarMap
  -> State CspCASLSign (CommAlpha, ProcVarMap, TERM ())
anaTermEvent mix t vars = do
  mt <- anaTermCspCASL mix vars t
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
anaChanSend :: Mix b s () () -> CHANNEL_NAME -> TERM () -> ProcVarMap
  -> State CspCASLSign
     (CommAlpha, ProcVarMap, (CHANNEL_NAME, SORT), TERM ())
anaChanSend mix c t vars = do
  sig <- get
  let ext = extendedInfo sig
      msg = "CspCASL.StatAnaCSP.anaChanSend: Channel Error"
  case Set.toList $ MapSet.lookup c $ chans ext of
    [] -> do
      addDiags [mkDiag Error "unknown channel" c]
      {- Use old term as the fully qualified term and forget about the
      channel, there is an error in the spec -}
      return (Set.empty, Map.empty, error msg, t)
    chanSorts -> do
      mt <- anaTermCspCASL mix vars t
      case mt of
        Nothing ->
          {- CASL analysis failed. Use old term as the fully
          qualified term and forget about the channel,
          there is an error in the spec. -}
          return (Set.empty, Map.empty, error msg, t)
        Just at -> do
          let rs = map (\ s -> ccTermCast at s sig) chanSorts
          addDiags $ concatMap diags rs
          case filter (isJust . maybeResult . fst) $ zip rs chanSorts of
            [] ->
              {- cast failed. Use old term as the fully
              qualified term, and forget about the
              channel there is an error in the spec. -}
              return (Set.empty, Map.empty, error msg, t)
            [(_, castSort)] ->
              let alpha = [ CommTypeSort castSort
                          , CommTypeChan $ TypedChanName c castSort]
                        {- Use the real fully qualified term. We do
                        not want to use a cast term here. A cast
                        must be possible, but we do not want to
                        force it! -}
              in return (Set.fromList alpha, Map.empty, (c, castSort), at)
            cts -> do -- fail due to an ambiguous chan sort
              addDiags [mkDiag Error
                   ("ambiguous channel sorts " ++ show (map snd cts)) t]
              {- Use old term as the fully qualified term and forget about the
              channel, there is an error in the spec. -}
              return (Set.empty, Map.empty, error msg, t)

getDeclaredChanSort :: (CHANNEL_NAME, SORT) -> CspCASLSign -> Result SORT
getDeclaredChanSort (c, s) sig =
  let cm = chans $ extendedInfo sig
  in case Set.toList $ MapSet.lookup c cm of
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
channel and the fully qualified version of the
variable. -}
anaChanBinding :: CHANNEL_NAME -> VAR -> SORT
  -> State CspCASLSign
     (CommAlpha, ProcVarMap, (CHANNEL_NAME, SORT), TERM ())
anaChanBinding c v s = do
  checkSorts [s] -- check sort is known
  sig <- get
  let qv = Qual_var v s nullRange
      fqChan = (c, s)
      Result ds ms = getDeclaredChanSort fqChan sig
  addDiags ds
  case ms of
    Nothing -> return (Set.empty, Map.empty, fqChan, qv)
    Just _ ->
        let alpha = [CommTypeSort s, CommTypeChan (TypedChanName c s)]
            binding = [(v, s)]
            {- Return the alphabet, var mapping, the fully qualfied channel and
            fully qualfied variable. Notice that the fully qualified
            channel's sort should be the lowest sort we can communicate in
            i.e. the sort of the variable. -}
        in return (Set.fromList alpha, Map.fromList binding, fqChan, qv)

-- Static analysis of renaming and renaming items

{- | Statically analyse a CspCASL renaming. Returns the alphabet and
the fully qualified renaming. -}
anaRenaming :: RENAMING -> State CspCASLSign (CommAlpha, RENAMING)
anaRenaming renaming = case renaming of
  Renaming r -> do
    fqRenamingTerms <- mapM anaRenamingItem r
    let rs = concat fqRenamingTerms
    return ( Set.map CommTypeSort $ Set.unions $ map alphaOfRename rs
           , Renaming rs)

alphaOfRename :: Rename -> Set.Set SORT
alphaOfRename (Rename _ cm) = case cm of
  Just (_, Just (s1, s2)) -> Set.fromList [s1, s2]
  _ -> Set.empty

{- | Statically analyse a CspCASL renaming item. Return the alphabet
and the fully qualified list of renaming functions and predicates. -}
anaRenamingItem :: Rename -> State CspCASLSign [Rename]
anaRenamingItem r@(Rename ri cm) = let
  predToRen p = Rename ri $ Just (BinPred, Just p)
  opToRen (o, p) = Rename ri
    $ Just (if o == Total then TotOp else PartOp, Just p)
  in case cm of
  Just (k, ms) -> case k of
    BinPred -> do
      ps <- getBinPredsById ri
      let realPs = case ms of
                     Nothing -> ps
                     Just p -> filter (== p) ps
      when (null realPs)
        $ addDiags [mkDiag Error "renaming predicate not found" r]
      unless (isSingle realPs)
        $ addDiags [mkDiag Warning "multiple predicates found" r]
      return $ map predToRen realPs
    _ -> do
      os <- getUnaryOpsById ri
      -- we ignore the user given op kind here!
      let realOs = case ms of
                     Nothing -> os
                     Just p -> filter ((== p) . snd) os
      when (null realOs)
        $ addDiags [mkDiag Error "renaming operation not found" r]
      unless (isSingle realOs)
        $ addDiags [mkDiag Warning "multiple operations found" r]
      when (k == TotOp) $
        mapM_ (\ (o, (s1, s2)) -> when (o == Partial)
          $ addDiags [mkDiag Error
                     ("operation of type '"
                      ++ shows s1 " -> "
                      ++ shows s2 "' is not total") r]) realOs
      return $ map opToRen realOs
  Nothing -> do
    ps <- getBinPredsById ri
    os <- getUnaryOpsById ri
    let rs = map predToRen ps ++ map opToRen os
    when (null rs)
      $ addDiags [mkDiag Error "renaming predicate or operation not found" ri]
    unless (isSingle rs)
      $ addDiags [mkDiag Warning "multiple renamings found" ri]
    return rs

{- | Given a CASL identifier, find all
unary operations with that name in the CASL signature, and return a
list of corresponding profiles, i.e. kind, argument sort and result sort. -}
getUnaryOpsById :: Id -> State CspCASLSign [(OpKind, (SORT, SORT))]
getUnaryOpsById ri = do
  om <- gets opMap
  return $ Set.fold (\ oty -> case oty of
     OpType k [s1] s2 -> ((k, (s1, s2)) :)
     _ -> id) [] $ MapSet.lookup ri om

{- | Given a CASL identifier find all binary predicates with that name in the
CASL signature, and return a list of corresponding profiles. -}
getBinPredsById :: Id -> State CspCASLSign [(SORT, SORT)]
getBinPredsById ri = do
  pm <- gets predMap
  return $ Set.fold (\ pty -> case pty of
     PredType [s1, s2] -> ((s1, s2) :)
     _ -> id) [] $ MapSet.lookup ri pm

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
                       context ++ ")" ++ show (printCommAlpha extras)
            in addDiags [mkDiag Error err proc]

-- Static analysis of CASL terms occurring in CspCASL process terms.

{- | Statically analyse a CASL term appearing in a CspCASL process;
any in-scope process variables are added to the signature before
performing the analysis. -}
anaTermCspCASL :: Mix b s () () -> ProcVarMap -> TERM ()
  -> State CspCASLSign (Maybe (TERM ()))
anaTermCspCASL mix pm t = do
    sig <- get
    let newVars = Map.union pm (varMap sig)
        sigext = sig { varMap = newVars }
        Result ds mt = anaTermCspCASL' mix sigext t
    addDiags ds
    return mt

idSetOfSig :: CspCASLSign -> IdSets
idSetOfSig sig =
  unite [mkIdSets (allConstIds sig) (allOpIds sig) $ allPredIds sig]

{- | Statically analyse a CASL term in the context of a CspCASL
signature.  If successful, returns a fully-qualified term. -}
anaTermCspCASL' :: Mix b s () () -> CspCASLSign -> TERM () -> Result (TERM ())
anaTermCspCASL' mix sig trm = fmap snd $ anaTerm (const return) mix
 (ccSig2CASLSign sig) Nothing (getRange trm) trm

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
anaFormulaCspCASL :: Mix b s () () -> ProcVarMap -> FORMULA ()
  -> State CspCASLSign (Maybe (FORMULA ()))
anaFormulaCspCASL mix pm f = do
    addDiags [mkDiag Debug "anaFormulaCspCASL" f]
    sig <- get
    let newVars = Map.union pm (varMap sig)
        sigext = sig { varMap = newVars }
        Result ds mt = anaFormulaCspCASL' mix sigext f
    addDiags ds
    return mt

{- | Statically analyse a CASL formula in the context of a CspCASL
signature.  If successful, returns a fully-qualified formula. -}
anaFormulaCspCASL' :: Mix b s () () -> CspCASLSign -> FORMULA ()
  -> Result (FORMULA ())
anaFormulaCspCASL' mix sig =
  fmap snd . anaForm (const return) mix (ccSig2CASLSign sig)

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
