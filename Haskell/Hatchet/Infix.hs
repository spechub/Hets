{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 Infix

        Description:            Patches the abstract syntax description with
                                the infix precedence and associativity rules
                                for identifiers in the module.

                                The main tasks implemented by this module are:

        Primary Authors:        Lindsay Powles 

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module Infix (infixer) where

import AnnotatedHsSyn   (AHsDecl (..),
                         AHsMatch (..),
                         AHsRhs (..),
                         AHsExp (..),
                         AHsGuardedRhs (..),
                         AHsName (..),
                         AHsIdentifier,
                         AHsAssoc (..),
                         AHsAlt (..),
                         AHsGuardedAlt (..),
                         AHsGuardedAlts (..),
                         AHsStmt (..),
                         AHsFieldUpdate (..),
                         AModule (..))

import TidyModule (TidyModule(..))

import FiniteMaps   (FiniteMap,
                     zeroFM,
                     addToFM,
                     lookupDftFM)

----------------------------------------------------------------------------

type FixityInfo = (Int, AHsAssoc)
type OpKey      = (AModule, AHsIdentifier)
type SymbolMap = FiniteMap OpKey FixityInfo

----------------------------------------------------------------------------

 -- Some constants:

syn_err_msg :: String
syn_err_msg = "Syntax error in input, run through a compiler to check.\n"

syn_err_bad_oparg :: AHsExp -> AHsExp -> String
syn_err_bad_oparg op exp =    syn_err_msg ++ "\tERROR: cannot apply " ++ show op
                           ++ " to the expression: " ++ show exp

syn_err_precedence :: AHsExp -> AHsExp -> String
syn_err_precedence op exp =    syn_err_msg ++ "\tERROR: the precedence of " ++ show op
                            ++ " is incompatible with the precendence of it's argument: " ++ show exp

defaultFixity :: (Int, AHsAssoc)     -- Fixity assigned to operators without explict infix declarations.
defaultFixity = (9, AHsAssocLeft)

terminalFixity :: (Int, AHsAssoc)    -- Fixity given to variables, etc. Used to terminate descent.
terminalFixity = (10, AHsAssocLeft)

unqualModule :: AModule              -- The module which unqualified operators are associated with.
unqualModule = AModule "Prelude"

----------------------------------------------------------------------------

  -- infixer(): The exported top-level function. See header for usage.

infixer :: [AHsDecl] -> TidyModule -> TidyModule
infixer infixRules tidyMod = 
    tidyMod { tidyClassDecls = process tidyClassDecls,
              tidyInstDecls = process tidyInstDecls,
              tidyFunBinds = process tidyFunBinds,
              tidyPatBinds = process tidyPatBinds }
    where
        process field = map (processDecl infixMap) (field tidyMod)
        infixMap = buildSMap infixRules


----------------------------------------------------------------------------

  --  Functions for building and searching the map of operators and their
  -- associated associativity and binding power.

buildSMap :: [AHsDecl] -> SymbolMap
buildSMap infixRules =
    foldl myAddToFM zeroFM $ concat $ map formatDecl infixRules
    where
        formatDecl (AHsInfixDecl _ assoc strength names) = zip (map make_key names) $ circList (strength,assoc)
        circList (str,assc) = (str,assc) : circList (str,assc)
        myAddToFM fm (k,e) = addToFM k e fm
        make_key a_name = case a_name of
            (AQual a_module name)   -> (a_module, name)
            (AUnQual name)          -> (unqualModule, name)


lookupSM :: SymbolMap -> AHsExp -> FixityInfo
lookupSM infixMap exp = case exp of
    AHsVar qname    -> case qname of
                    AQual a_module name -> lookupDftFM infixMap defaultFixity (a_module, name)
                    AUnQual name        -> lookupDftFM infixMap defaultFixity (unqualModule, name)
    AHsCon qname -> case qname of
                    AQual a_module name -> lookupDftFM infixMap defaultFixity (a_module, name)
                    AUnQual name        -> lookupDftFM infixMap defaultFixity (unqualModule, name)
    _           -> error $ "Operator (" ++ show exp ++ ") is invalid."


-----------------------------------------------------------------------------

  --  Functions used to sift through the syntax to find expressions to
  -- operate on.

processDecl :: SymbolMap -> AHsDecl -> AHsDecl
processDecl infixMap decl = case decl of
    AHsClassDecl    srcloc qualtype decls   -> AHsClassDecl srcloc qualtype $ proc_decls decls
    AHsInstDecl     srcloc qualtype decls   -> AHsInstDecl srcloc qualtype $ proc_decls decls
    AHsFunBind      matches                 -> AHsFunBind $ map (processMatch infixMap) matches
    AHsPatBind      srcloc pat rhs decls    -> AHsPatBind srcloc pat (processRhs infixMap rhs) $
                                                          proc_decls decls
    _                                       -> decl
    where
        proc_decls decls = map (processDecl infixMap) decls


processMatch :: SymbolMap -> AHsMatch -> AHsMatch
processMatch infixMap (AHsMatch srcloc qname pats rhs decls) =
    AHsMatch srcloc qname pats new_rhs new_decls
    where
        new_rhs = processRhs infixMap rhs
        new_decls = map (processDecl infixMap) decls


processRhs :: SymbolMap -> AHsRhs -> AHsRhs
processRhs infixMap rhs = case rhs of
    AHsUnGuardedRhs exp     -> AHsUnGuardedRhs $ fst $ processExp infixMap exp
    AHsGuardedRhss  rhss    -> AHsGuardedRhss $ map (processGRhs infixMap) rhss


processGRhs :: SymbolMap -> AHsGuardedRhs -> AHsGuardedRhs 
processGRhs infixMap (AHsGuardedRhs srcloc e1 e2) = AHsGuardedRhs srcloc new_e1 new_e2
    where
        new_e1 = fst $ processExp infixMap e1
        new_e2 = fst $ processExp infixMap e2


processAlt :: SymbolMap -> AHsAlt -> AHsAlt
processAlt infixMap (AHsAlt srcloc pat g_alts decls) = AHsAlt srcloc pat new_g_alts new_decls
    where
        new_g_alts = processGAlts infixMap g_alts
        new_decls = map (processDecl infixMap) decls


processGAlts :: SymbolMap -> AHsGuardedAlts -> AHsGuardedAlts 
processGAlts infixMap g_alts = case g_alts of
    AHsUnGuardedAlt exp     -> AHsUnGuardedAlt $ fst $ processExp infixMap exp
    AHsGuardedAlts galts    -> AHsGuardedAlts $ map (processGAlt infixMap) galts


processGAlt :: SymbolMap -> AHsGuardedAlt -> AHsGuardedAlt
processGAlt infixMap (AHsGuardedAlt srcloc e1 e2) = AHsGuardedAlt srcloc new_e1 new_e2
    where
        new_e1 = fst $ processExp infixMap e1
        new_e2 = fst $ processExp infixMap e2


processStmt :: SymbolMap -> AHsStmt -> AHsStmt
processStmt infixMap stmt = case stmt of
    AHsGenerator srcloc pat exp     -> AHsGenerator srcloc pat $ fst $ processExp infixMap exp
    AHsQualifier exp                -> AHsQualifier $ fst $ processExp infixMap exp
    AHsLetStmt decls                -> AHsLetStmt $ map (processDecl infixMap) decls
 -- _                           -> error "Bad AHsStmt data passed to processStmt."


processFUpdt :: SymbolMap -> AHsFieldUpdate -> AHsFieldUpdate
processFUpdt infixMap (AHsFieldUpdate qname exp) = AHsFieldUpdate qname new_exp
    where
        new_exp = fst $ processExp infixMap exp



-----------------------------------------------------------------------------


    {- processExp():   Where the syntax tree reshaping actually takes
                     place. Assumes the parser that created the syntax
                     assumed the same binding power and left associativity
                     for all operators. Operators are assumed to be only
                     those that are excepted under the Haskell 98 report
                     and sections are also parsed according to this report
                     aswell (NOT according to how current compilers handle
                     sections!). -}

processExp :: SymbolMap -> AHsExp -> (AHsExp, FixityInfo)
processExp infixMap exp = case exp of
    AHsInfixApp l op r  ->
              case (compare l_power op_power) of
                    GT -> (AHsInfixApp new_l op new_r, op_fixity)
                    EQ -> case op_assoc of
                        AHsAssocNone    -> error_precedence op new_l
                        AHsAssocRight   -> case l_assoc of
                            AHsAssocRight   -> case new_l of
                                AHsInfixApp l' op' r' -> (AHsInfixApp l' op' (process_r' r'), l_fixity)
                                _                     -> error_syntax op new_l
                            _               -> error_precedence op new_l
                        AHsAssocLeft    -> case l_assoc of
                            AHsAssocLeft    -> (AHsInfixApp new_l op new_r, op_fixity)
                            _               -> error_precedence op new_l
                    LT -> case new_l of
                        AHsInfixApp l' op' r' -> (AHsInfixApp l' op' (process_r' r'), l_fixity)
                        _                     -> error_syntax op new_l
               where
                    (new_l, l_fixity) = processExp infixMap l
                    l_power = fst l_fixity
                    l_assoc = snd l_fixity
                    op_fixity = lookupSM infixMap op
                    op_power = fst op_fixity
                    op_assoc = snd op_fixity
                    new_r = processExp' r
                    process_r' r' = processExp' $ AHsInfixApp r' op r
                    error_precedence err_op err_lower = error $ syn_err_precedence err_op err_lower
                    error_syntax err_op err_lower = error $ syn_err_bad_oparg err_op err_lower
    AHsApp e1 e2        -> (AHsApp (processExp' e1) (processExp' e2), terminalFixity)
    AHsNegApp e1        -> (AHsNegApp (processExp' e1), terminalFixity)
    AHsLet decls e1     -> (AHsLet (map (processDecl infixMap) decls) (processExp' e1), terminalFixity)
    AHsIf e1 e2 e3      -> (AHsIf (processExp' e1) (processExp' e2) (processExp' e3), terminalFixity)
    AHsCase e1 alts     -> (AHsCase (processExp' e1) (map (processAlt infixMap) alts), terminalFixity)
    AHsDo stmts         -> (AHsDo (map (processStmt infixMap) stmts), terminalFixity)
    AHsTuple exps       -> (AHsTuple (map processExp' exps), terminalFixity)
    AHsList exps        -> (AHsList (map processExp' exps), terminalFixity)
    AHsParen e1         -> (AHsParen (processExp' e1), terminalFixity)
    AHsEnumFrom e1      -> (AHsEnumFrom (processExp' e1), terminalFixity)
    AHsEnumFromTo e1 e2 -> (AHsEnumFromTo (processExp' e1) (processExp' e2), terminalFixity)
    AHsListComp e1 stmts    ->
                           (AHsListComp (processExp' e1) (map (processStmt infixMap) stmts), terminalFixity)
    AHsAsPat name e1        -> (AHsAsPat name (processExp' e1), terminalFixity)
    AHsIrrPat e1            -> (AHsIrrPat (processExp' e1), terminalFixity)
    AHsLeftSection e1 e2    -> (AHsLeftSection e1 (processExp' e2), terminalFixity)
    AHsRightSection e1 e2       -> (AHsRightSection (processExp' e1) e2, terminalFixity)
    AHsLambda srcloc pats e1    -> (AHsLambda srcloc pats (processExp' e1), terminalFixity)
    AHsRecConstr qname f_updts  -> (AHsRecConstr qname (map (processFUpdt infixMap) f_updts), terminalFixity)
    AHsEnumFromThen e1 e2       -> (AHsEnumFromThen (processExp' e1) (processExp' e2), terminalFixity)
    AHsRecUpdate e1 f_updts     ->
                        (AHsRecUpdate (processExp' e1) (map (processFUpdt infixMap) f_updts), terminalFixity)
    AHsEnumFromThenTo e1 e2 e3  ->
                        (AHsEnumFromThenTo (processExp' e1) (processExp' e2) (processExp' e3), terminalFixity)
    AHsExpTypeSig srcloc e1 qtype   -> (AHsExpTypeSig srcloc (processExp' e1) qtype, terminalFixity)
    _                   -> (exp, terminalFixity)
    where
        processExp' = fst . (processExp infixMap)

------------------------------------------------------------------------------
