{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 Rename

        Description:            Renames variables apart in a Module

        Primary Authors:        Toby Ord, Bryn Humberstone, Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------

  Implementation:

     * pass 1

     The first pass is just to collect the names of functions defined within class declarations
     as these are global in scope and must be collected first. This pass is quite fast and simple.

     * pass 2

     The algorithm then proceeds through the syntax tree, from outermost scope
     to innermost in a depth first manner.

     On entering a new scope, updateSubTableWith* is used to get the new names
     in this scope, putting them into the current subTable, clobbering any
     identifiers with the same name in outer scopes. It also creates their new
     names (although no renaming is performed yet)

     Now, all identifiers the algorithm finds before entering the next nested
     scope will have a mapping to a new name in the subTable and their old
     names get replaced by these
     

  * bugs

     It should work for records but it doesn't rename them because it never adds
     them to the scope

     It also needs more testing for records

     It assumes that all PatBinds have only one identifier to the left of the equals
     ie. x     = a b c d   is OK
         (x,y) = a b c d   is not
     this should not be too hard to change

     It doesn't add information about the identifiers in class and instance
     definitions to the identTable.

        - The correct behaviour here is not obvious as these are the only
          identifiers that are declared multiple times, so there is no unique
          source location.
        - The method of declaration is also different to normal as identifiers
          are normally added to the identTable when they are first added to the
          scope, but these are added in the class
          pass and can't be re-added.

     It doesn't rename type signatures that do not have an associated PatBind
     or FunBind

-------------------------------------------------------------------------------}

module Rename    (renameTidyModule, 
                  unRenameAHsSyn,
                  unRename, 
                  getAHsNamesAndASrcLocsFromAHsDecl, 
                  bindOfId, 
                  printIdentTable,
                  IdentTable) where

import AnnotatedHsSyn            -- everything 

import FiniteMaps       (FiniteMap,
                         zeroFM,
                         toListFM,
                         listToFM,
                         addToFM,
                         lookupFM,
                         lookupDftFM)

import List             (nub)

import Char             (isDigit)

import TidyModule       (TidyModule (..))

import Utils            (fromAHsName,
                         Binding (..),
                         fromAHsIdentifier,
                         qualifyName,
                         lJustify,
                         rJustify)

--------------------------------------------------------------------------------

unRenameAHsSyn :: Renameable a => a -> a
unRenameAHsSyn = replaceName unRename

-- a unique number which is part of the Scope State Monad and is used
-- to guarantee uniqueness for the variable names

type Unique = Int

-- a 'Substitution Table' which is a map from old names to new names
-- All names in the current scope are stored in here, with their renamings

type SubTable = FiniteMap AHsName AHsName
{- initialSubTable :: SubTable -}
{- initialSubTable = zeroFM    -}

-- an Identifier Table is a map from renamed names to that identifier's source
-- location and binding type

type IdentTable = FiniteMap AHsName (ASrcLoc, Binding) 

printIdentTable :: IdentTable -> IO ()
printIdentTable idt
   = putStr $ unlines $ map showIdentTabEntry $ toListFM idt 
   where
   showIdentTabEntry :: (AHsName, (ASrcLoc, Binding)) -> String
   showIdentTabEntry (name, (ASrcLoc row col, bind)) 
      = lJustify 40 (fromAHsName name) ++ 
        showPos (row, col) ++ 
        rJustify 10 (show bind)
   showPos pos@(row, col)
      | row < 0 || col < 0 = rJustify 10 "none" 
      | otherwise          = rJustify 10 $ show pos 


-- the monadic state

{- type ScopeState = (Unique, IdentTable) -}  
-- note Bryn changed it to a record. _might_ be more efficient
-- as (say) a triple/quadruple/whatever size it ends up
data ScopeState = ScopeState {  currentModule  :: AModule,
                                unique         :: Unique,
                                globalSubTable :: SubTable,  -- things imported (e.g. Prelude.Int)
                                identTable     :: IdentTable } deriving Show



-- The monadic type

data ScopeSM a = ScopeSM (ScopeState -> (a, ScopeState))

instance Monad ScopeSM where
  -- defines state propagation
  ScopeSM c1 >>= fun         =  ScopeSM (\stateStart -> 
                                           let (result,state') = c1 stateStart 
                                               ScopeSM c2 = fun result
                                           in c2 state')
  return k                   =  ScopeSM (\s -> (k,s))


-- ScopeSM utility stuff

updateScopeSM :: (ScopeState -> ScopeState) -> ScopeSM ()
updateScopeSM f = ScopeSM (\s -> ((), f s))

runScopeSM :: ScopeState -> ScopeSM a -> (a, ScopeState)
runScopeSM s0 (ScopeSM c) =  c s0

-- functions to read from the ScopeSM
select :: (ScopeState -> a) -> ScopeSM a
select selector = ScopeSM (\state -> (selector state, state))

getUnique :: ScopeSM Unique 
getUnique = select unique

getCurrentModule :: ScopeSM AModule
getCurrentModule = select currentModule

getGlobalSubTable :: ScopeSM SubTable
getGlobalSubTable = select globalSubTable

-- functions to modify the ScopeSM

incUnique :: ScopeSM ()
incUnique = updateScopeSM (\state -> state {unique = (unique state) + 1})

addToIdentTable :: AHsName -> (ASrcLoc,Binding) -> ScopeSM ()
addToIdentTable hsName srcLocAndBinding
   = updateScopeSM (\state -> state {identTable = addToFM hsName srcLocAndBinding (identTable state)})

-----------------------------------------------------------
-- The renaming code:
--

----------------------------------------------------------------------------
---   ATTENTION: Now renameTidyModule expects a list of names imported   ---
---              into this module's scope.                               ---
----------------------------------------------------------------------------

-- takes a list of qualified AHsNames that the current module needs to know
-- about (i.e. ones imported from Prelude), and then in the renaming process
-- any of those names appearing in unqualified form will get qualified
-- e.g. we pass in [AQual (AModule "Prelude") "take"] and then in code we see
-- foo = take 3 [1..10], so we translate this to (something like)
-- Main.foo = Prelude.take 3 [1..10]
renameTidyModule :: [AHsName] -> TidyModule -> (TidyModule, IdentTable)
renameTidyModule importedNames tidyMod 
    = (renamedTidyMod, identTable finalState)
    where
    initialGlobalSubTable :: SubTable
    initialGlobalSubTable 
        = listToFM (map makeTranslation importedNames)
          where makeTranslation qname@(AQual _ str) = (AUnQual str, qname)
                makeTranslation unqname = error $ 
                  "renameTidyModule passed an unqualified importedName " ++ show unqname

    classDecls = tidyClassDecls tidyMod

    -- this is the state to start pass 1's monad off with
    startState = ScopeState { identTable     = zeroFM,
                              unique         = 1,   -- start the counting at 1
                              globalSubTable = initialGlobalSubTable,
                              currentModule  = tidyModName tidyMod }

    -- pass 1
    (updatedSubTable, returnStatePass1)
        = runScopeSM startState $
                     updateSubTableWithClasses initialGlobalSubTable classDecls

    -- pass 2
    -- XXX: Toby's original code didn't pass along the value of the identTable
    -- I'm (Bryn) not sure whether this is right or not but I won't change it
    (renamedTidyMod, finalState)
        = runScopeSM (startState { unique = (unique returnStatePass1) })
                     (renameDecls tidyMod updatedSubTable) 

-- This is Bryn's modification to make the code a bit easier to understand for
-- functions like renameAHsNames, renameAHsFileUpdates
mapRename :: (a -> SubTable -> ScopeSM a) -> [a] -> SubTable -> ScopeSM [a]
mapRename renameIndividual individuals subTable
    = mapM (`renameIndividual` subTable) individuals


renameDecls :: TidyModule -> SubTable -> ScopeSM TidyModule
renameDecls tidy subTable
   = do let oldTyDecls    = tidyTyDecls tidy
            oldDataDecls  = tidyDataDecls tidy
            oldNewTyDecls = tidyNewTyDecls tidy
            oldClassDecls = tidyClassDecls tidy
            oldInstDecls  = tidyInstDecls tidy
            oldDefs       = tidyDefDecls tidy
            oldTySigs     = tidyTySigs tidy
            oldFunBinds   = tidyFunBinds tidy
            oldPatBinds   = tidyPatBinds tidy
            oldInfixDecls = tidyInFixDecls tidy
        subTable' <- updateSubTableWithAHsDecls subTable (oldFunBinds++oldPatBinds) TopFun -- FunBinds & PatBinds
        newTyDecls    <- renameAHsDecls oldTyDecls subTable'
        newDataDecls  <- renameAHsDecls oldDataDecls subTable'
        newNewTyDecls <- renameAHsDecls oldNewTyDecls subTable'
        newClassDecls <- renameAHsDecls oldClassDecls subTable'
        newInstDecls  <- renameAHsDecls oldInstDecls subTable'
        newDefs       <- renameAHsDecls oldDefs subTable'
        newTySigs     <- renameAHsDecls oldTySigs subTable'
        newFunBinds   <- renameAHsDecls oldFunBinds subTable'
        newPatBinds   <- renameAHsDecls oldPatBinds subTable'
        -- XXX: the renaming of InFix decls is a tad dodgy, and
        -- it means that if there's a declaration that's not later
        -- used then it won't have the <number>_ prefix. I don't
        -- think this will cause too much of a problem but I am
        -- having trouble understanding what the code is doing 
        -- so I can't easily fix it.
        newInFixDecls <- renameAHsDecls oldInfixDecls subTable'
        let newTidyMod = 
               tidy{tidyTyDecls    = newTyDecls,
                    tidyDataDecls  = newDataDecls,
                    tidyInFixDecls = newInFixDecls,
                    tidyNewTyDecls = newNewTyDecls,
                    tidyClassDecls = newClassDecls,
                    tidyInstDecls  = newInstDecls,
                    tidyDefDecls   = newDefs,
                    tidyTySigs     = newTySigs,
                    tidyFunBinds   = newFunBinds,
                    tidyPatBinds   = newPatBinds}
        return newTidyMod
     

-- The following functions all take a piece of the Haskell syntax tree
-- (as outlined in AHsSyn) and uses the provided SubTable to rename it

-- Some of the functions have to create a new nested scope which they do
-- by creating a new SubTable using updateSubTableWith* and passing that
-- new table down to its children on the syntax tree.

renameAHsDecls :: [AHsDecl] -> SubTable -> ScopeSM ([AHsDecl])
renameAHsDecls decls subtable 
    = do 
      ans <- mapRename renameAHsDecl decls subtable
      return ans

renameAHsDecl :: AHsDecl -> SubTable -> ScopeSM (AHsDecl)
renameAHsDecl (AHsPatBind srcLoc hsPat hsRhs {-where-} hsDecls) subTable
  = do
      hsPat'    <- renameAHsPat hsPat subTable
      subTable' <- updateSubTableWithAHsDecls subTable hsDecls LetFun
      hsDecls'  <- renameAHsDecls hsDecls subTable'
      hsRhs'    <- renameAHsRhs hsRhs subTable'
      let patbind' = (AHsPatBind srcLoc hsPat' hsRhs' {-where-} hsDecls')
      return patbind'
      

--renameAHsDecl (AHsFunBind srcLoc hsMatches) subTable
renameAHsDecl (AHsFunBind hsMatches) subTable
  = do
      hsMatches' <- renameAHsMatches hsMatches subTable
      -- return (AHsFunBind srcLoc hsMatches')
      return (AHsFunBind hsMatches')
renameAHsDecl (AHsTypeSig srcLoc hsNames hsQualType) subTable
  = do
      hsNames' <- renameAHsNames hsNames subTable
      subTable' <- updateSubTableWithAHsQualType subTable hsQualType
      hsQualType' <- renameAHsQualType hsQualType subTable'
      return (AHsTypeSig srcLoc hsNames' hsQualType')
renameAHsDecl (AHsDataDecl srcLoc hsContext hsName hsNames1 hsConDecls hsNames2) subTable
  = do
  {- XXX Bryn changed this so a decl like 
       'data Bool = True | False' becomes
       'data Prelude.Bool = Prelude.True | Prelude.False' -}
      hsName' <- renameAHsName hsName subTable
      subTable' <- updateSubTableWithAHsNames subTable hsNames1
      hsContext' <- renameAHsContext hsContext subTable'
      -- don't need to rename the hsName (it is a constructor)
      hsNames1' <- renameAHsNames hsNames1 subTable'
      hsConDecls' <- renameAHsConDecls hsConDecls subTable'
      -- don't need to rename the hsNames2 as it is just a list of TypeClasses
      return (AHsDataDecl srcLoc hsContext' hsName' hsNames1' hsConDecls' hsNames2)

renameAHsDecl (AHsNewTypeDecl srcLoc hsContext hsName hsNames1 hsConDecl hsNames2) subTable
  = do
      subTable' <- updateSubTableWithAHsNames subTable hsNames1
      hsContext' <- renameAHsContext hsContext subTable'
      -- don't need to rename the hsName (it is a constructor)
      hsNames1' <- renameAHsNames hsNames1 subTable'
      hsConDecl' <- renameAHsConDecl hsConDecl subTable'
      -- don't need to rename the hsNames2 as it is just a list of TypeClasses
      return (AHsNewTypeDecl srcLoc hsContext' hsName hsNames1' hsConDecl' hsNames2)
-- here, we have to create a separate subTable (called the typeSigSubTable) to be passed down
-- because the part that renames the hsQualType in the type signatures needs a subTable with
-- _only_ the class's QualType in it.
-- Yes this is complicated and nasty. It is due mainly to the fact that some (but not all of
-- the type variables in the type sigs of the class's member functions must be renamed and
-- the new variables are used on the fly and not declared in an orderly manner.
renameAHsDecl (AHsClassDecl srcLoc hsQualType hsDecls) subTable
  = do
    -- Note from Bryn: The reason we get the global subtable at this point is that
    -- we start off Pass 1 by looking at class declarations so instead of starting
    -- with an empty subtable, we start with the global subtable (includes imports)
      startingSubTable <- getGlobalSubTable -- only includes things from outside the module (e.g. Int, "take")
      {- WAS: typeSigSubTable <- updateSubTableWithAHsQualType initialSubTable hsQualType -}
      typeSigSubTable <- updateSubTableWithAHsQualType startingSubTable hsQualType 
      hsQualType' <- renameAHsQualType hsQualType typeSigSubTable
      hsDecls' <- renameAHsDecls_insideClass hsDecls subTable typeSigSubTable
      return (AHsClassDecl srcLoc hsQualType' hsDecls')
renameAHsDecl (AHsInstDecl srcLoc hsQualType hsDecls) subTable
  = do
      subTable' <- updateSubTableWithAHsQualType subTable hsQualType
      hsQualType' <- renameAHsQualType hsQualType subTable'
      hsDecls' <- renameAHsDecls hsDecls subTable'
      return (AHsInstDecl srcLoc hsQualType' hsDecls')
renameAHsDecl (AHsInfixDecl srcLoc assoc int hsNames) subTable
    = do
      -- can't do this as we might already have an import
      hsNames' <- renameAHsNames hsNames subTable
      -- we really just want to qualify the names with the
      -- current module
      {-
      modName <- getCurrentModule 
      let hsNames' = map (Utils.qualifyName modName) hsNames
      -}
      return $ AHsInfixDecl srcLoc assoc int hsNames'

renameAHsDecl otherAHsDecl _subTable
  = return otherAHsDecl

-- renameAHsDecl(s)_insideClass is needed to rename the type variables defined
-- in the function prototypes in a class definition without renaming them apart from
-- the type variables defined at the beginning of the class definition.
--
-- To acheive this, renameAHsDecl_insideClass omits a single line from renameAHsDecl
-- so that a new scope is not introduced. It must also thread through the extra subTable
-- to be used in the renaming of the type sigs.


renameAHsDecls_insideClass :: [AHsDecl] -> SubTable -> SubTable -> ScopeSM ([AHsDecl])
renameAHsDecls_insideClass (hsDecl:hsDecls) subTable typeSigSubTable
  = do
      hsDecl'  <- renameAHsDecl_insideClass hsDecl subTable typeSigSubTable 
      hsDecls' <- renameAHsDecls_insideClass hsDecls subTable typeSigSubTable
      return (hsDecl':hsDecls')
renameAHsDecls_insideClass [] _subTable _typeSigSubTable
  = return []

renameAHsDecl_insideClass :: AHsDecl -> SubTable -> SubTable -> ScopeSM (AHsDecl)
renameAHsDecl_insideClass (AHsTypeSig srcLoc hsNames hsQualType) subTable typeSigSubTable
  = do
      hsNames' <- renameAHsNames hsNames subTable
      typeSigSubTable' <- updateSubTableWithAHsQualType_insideClass typeSigSubTable hsQualType
      hsQualType' <- renameAHsQualType hsQualType typeSigSubTable'
      return (AHsTypeSig srcLoc hsNames' hsQualType')
renameAHsDecl_insideClass (AHsPatBind srcLoc hsPat hsRhs {-where-} hsDecls) subTable _typeSigSubTable
  = do      renameAHsDecl (AHsPatBind srcLoc hsPat hsRhs {-where-} hsDecls) subTable
-- renameAHsDecl_insideClass (AHsFunBind srcLoc hsMatches) subTable typeSigSubTable
renameAHsDecl_insideClass (AHsFunBind hsMatches) subTable _typeSigSubTable
  -- = do      renameAHsDecl (AHsFunBind srcLoc hsMatches) subTable
  = do      renameAHsDecl (AHsFunBind hsMatches) subTable
renameAHsDecl_insideClass _hsDecl _subTable _typeSigSubTable
  = error "a strange declaration was encountered in a class declaration"



renameAHsQualType :: AHsQualType -> SubTable -> ScopeSM (AHsQualType)
renameAHsQualType (AHsQualType hsContext hsType) subTable
  = do
      hsContext' <- renameAHsContext hsContext subTable
      hsType' <- renameAHsType hsType subTable
      return (AHsQualType hsContext' hsType')
renameAHsQualType (AHsUnQualType hsType) subTable
  = do
      hsType' <- renameAHsType hsType subTable
      return (AHsUnQualType hsType')

renameAHsContext :: AHsContext -> SubTable -> ScopeSM (AHsContext)
renameAHsContext = mapRename renameAHsAsst

renameAHsAsst :: AHsAsst -> SubTable -> ScopeSM (AHsAsst)
renameAHsAsst (hsName1, hsName2) subTable
  = do
      hsName1' <- renameAHsName hsName1 subTable  -- for class names
      hsName2' <- renameAHsName hsName2 subTable
      return (hsName1', hsName2')

renameAHsConDecls :: [AHsConDecl] -> SubTable -> ScopeSM ([AHsConDecl])
renameAHsConDecls = mapRename renameAHsConDecl

renameAHsConDecl :: AHsConDecl -> SubTable -> ScopeSM (AHsConDecl)
renameAHsConDecl (AHsConDecl srcLoc hsName hsBangTypes) subTable
  = do
      -- the hsName does not need to be renamed as it is a constructor
      -- XXX: Bryn has changed this (falsifying the above) so that 
      -- a declaration like data Bool = True | False is now 
      --                    data Prelude.Bool = Prelude.True | Prelude.False
      hsName' <- renameAHsName hsName subTable
      hsBangTypes' <- renameAHsBangTypes hsBangTypes subTable
      return (AHsConDecl srcLoc hsName' hsBangTypes') 
renameAHsConDecl (AHsRecDecl srcLoc hsName stuff) _subTable
  = do
      -- this will never be executed at the moment because the parser breaks on AHsRecDecls
      return (AHsRecDecl srcLoc hsName stuff)

renameAHsBangTypes :: [AHsBangType] -> SubTable -> ScopeSM ([AHsBangType])
renameAHsBangTypes = mapRename renameAHsBangType

renameAHsBangType :: AHsBangType -> SubTable -> ScopeSM (AHsBangType)
renameAHsBangType (AHsBangedTy hsType) subTable
  = do
      hsType' <- renameAHsType hsType subTable
      return (AHsBangedTy hsType')
renameAHsBangType (AHsUnBangedTy hsType) subTable
  = do
      hsType' <- renameAHsType hsType subTable
      return (AHsUnBangedTy hsType')

renameAHsType :: AHsType -> SubTable -> ScopeSM (AHsType)
renameAHsType (AHsTyFun hsType1 hsType2) subTable
  = do
      hsType1' <- renameAHsType hsType1 subTable
      hsType2' <- renameAHsType hsType2 subTable
      return (AHsTyFun hsType1' hsType2')
renameAHsType (AHsTyTuple hsTypes) subTable
  = do
      hsTypes' <- mapRename renameAHsType hsTypes subTable
      return (AHsTyTuple hsTypes')

renameAHsType (AHsTyApp hsType1 hsType2) subTable
  = do
      hsType1' <- renameAHsType hsType1 subTable
      hsType2' <- renameAHsType hsType2 subTable
      return (AHsTyApp hsType1' hsType2')
renameAHsType (AHsTyVar hsName) subTable
  = do
      hsName' <- renameAHsName hsName subTable
      return (AHsTyVar hsName')
renameAHsType (AHsTyCon hsName) subTable
  = do
      hsName' <- renameAHsName hsName subTable  -- NOTE: This was Bryn's change (to rename tycons)
      return (AHsTyCon hsName')

renameAHsMatches :: [AHsMatch] -> SubTable -> ScopeSM [AHsMatch]
renameAHsMatches = mapRename renameAHsMatch

-- note that for renameAHsMatch, the 'wheres' dominate the 'pats'

renameAHsMatch :: AHsMatch -> SubTable -> ScopeSM AHsMatch
renameAHsMatch (AHsMatch srcLoc hsName hsPats hsRhs {-where-} hsDecls) subTable
  = do
      hsName' <- renameAHsName hsName subTable
      subTable' <- updateSubTableWithAHsPats subTable hsPats srcLoc FunPat
      hsPats' <- renameAHsPats hsPats subTable'
      subTable'' <- updateSubTableWithAHsDecls subTable' hsDecls WhereFun
      hsDecls' <- renameAHsDecls hsDecls subTable''
      hsRhs' <- renameAHsRhs hsRhs subTable''
      return (AHsMatch srcLoc hsName' hsPats' hsRhs' {-where-} hsDecls')


renameAHsPats :: [AHsPat] -> SubTable -> ScopeSM ([AHsPat])
renameAHsPats = mapRename renameAHsPat

renameAHsPat :: AHsPat -> SubTable -> ScopeSM (AHsPat) 
renameAHsPat (AHsPVar hsName) subTable
  = do
      hsName' <- renameAHsName hsName subTable
      return (AHsPVar hsName')
renameAHsPat (AHsPLit hsLiteral) _subTable
  = return (AHsPLit hsLiteral)
renameAHsPat (AHsPNeg hsPat) subTable
  = do
      hsPat' <- renameAHsPat hsPat subTable
      return (AHsPNeg hsPat')
renameAHsPat (AHsPInfixApp hsPat1 hsName hsPat2) subTable
  = do
      hsPat1' <- renameAHsPat hsPat1 subTable
      hsPat2' <- renameAHsPat hsPat2 subTable
      hsName' <- renameAHsName hsName subTable
      return (AHsPInfixApp hsPat1' hsName' hsPat2')
renameAHsPat (AHsPApp hsName hsPats) subTable
  = do
      hsPats' <- renameAHsPats hsPats subTable
      hsName' <- renameAHsName hsName subTable
      return (AHsPApp hsName' hsPats')  -- NOTE: Bryn changed this so we also rename hsName and not just the hsPats
renameAHsPat (AHsPTuple hsPats) subTable
  = do
      hsPats' <- renameAHsPats hsPats subTable
      return (AHsPTuple hsPats')
renameAHsPat (AHsPList hsPats) subTable
  = do
      hsPats' <- renameAHsPats hsPats subTable
      return (AHsPList hsPats')
renameAHsPat (AHsPParen hsPat) subTable
  = do
      hsPat' <- renameAHsPat hsPat subTable
      return (AHsPParen hsPat')
renameAHsPat (AHsPRec hsName hsPatFields) subTable
  = do
      -- the hsName can be ignored as it is a Constructor
      hsPatFields' <- renameAHsPatFields hsPatFields subTable
      return (AHsPRec hsName hsPatFields)
renameAHsPat (AHsPAsPat hsName hsPat) subTable
  = do
      hsName' <- renameAHsName hsName subTable
      hsPat' <- renameAHsPat hsPat subTable
      return (AHsPAsPat hsName' hsPat')
renameAHsPat (AHsPWildCard) _subTable
  = return AHsPWildCard
renameAHsPat (AHsPIrrPat hsPat) subTable
  = do
      hsPat' <- renameAHsPat hsPat subTable
      return (AHsPIrrPat hsPat')


renameAHsPatFields :: [AHsPatField] -> SubTable -> ScopeSM ([AHsPatField])
renameAHsPatFields = mapRename renameAHsPatField

-- although the hsNames here must be unique (field names),
-- I rename them for the sake of completeness
renameAHsPatField :: AHsPatField -> SubTable -> ScopeSM (AHsPatField)
{-
renameAHsPatField (AHsPFieldPun hsName) subTable
  = do
      hsName' <- renameAHsName hsName subTable
      return (AHsPFieldPun hsName')
-}
renameAHsPatField (AHsPFieldPat hsName hsPat) subTable
  = do
      hsName' <- renameAHsName hsName subTable
      hsPat' <- renameAHsPat hsPat subTable
      return (AHsPFieldPat hsName' hsPat')


renameAHsRhs :: AHsRhs -> SubTable -> ScopeSM AHsRhs
renameAHsRhs (AHsUnGuardedRhs hsExp) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      return (AHsUnGuardedRhs hsExp')
renameAHsRhs (AHsGuardedRhss hsGuardedRhss) subTable
  = do
      hsGuardedRhss' <- renameAHsGuardedRhss hsGuardedRhss subTable
      return (AHsGuardedRhss hsGuardedRhss')


renameAHsGuardedRhss :: [AHsGuardedRhs] -> SubTable -> ScopeSM ([AHsGuardedRhs])
renameAHsGuardedRhss = mapRename renameAHsGuardedRhs

renameAHsGuardedRhs :: AHsGuardedRhs -> SubTable -> ScopeSM AHsGuardedRhs
renameAHsGuardedRhs (AHsGuardedRhs srcLoc hsExp1 hsExp2) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      return (AHsGuardedRhs srcLoc hsExp1' hsExp2')


renameAHsExps :: [AHsExp] -> SubTable -> ScopeSM ([AHsExp])
renameAHsExps = mapRename renameAHsExp

renameAHsExp :: AHsExp -> SubTable -> ScopeSM AHsExp
-- renameAHsExp (AHsVar hsName annot) subTable
renameAHsExp (AHsVar hsName) subTable
  = do
      hsName' <- renameAHsName hsName subTable
      -- return (AHsVar hsName' annot)
      return (AHsVar hsName')
renameAHsExp (AHsCon hsName) subTable
  = do
      hsName' <- renameAHsName hsName subTable
      return (AHsCon hsName') 
      -- XXX: this used to be hsName but I (Bryn) didn't want that.
      -- Now a constructor like "False" will be renamed (correctly)
      -- to "Prelude.False" so this is better :)
renameAHsExp (AHsLit hsLiteral) _subTable
  = do
      return (AHsLit hsLiteral)
renameAHsExp (AHsInfixApp hsExp1 hsExp2 hsExp3) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      hsExp3' <- renameAHsExp hsExp3 subTable
      return (AHsInfixApp hsExp1' hsExp2' hsExp3')
renameAHsExp (AHsApp hsExp1 hsExp2) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      return (AHsApp hsExp1' hsExp2')
renameAHsExp (AHsNegApp hsExp) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      return (AHsNegApp hsExp')
renameAHsExp (AHsLambda srcLoc hsPats hsExp) subTable
  = do
      subTable' <- updateSubTableWithAHsPats subTable hsPats srcLoc LamPat
      hsPats' <- renameAHsPats hsPats subTable'
      hsExp' <- renameAHsExp hsExp subTable'
      return (AHsLambda srcLoc hsPats' hsExp')
renameAHsExp (AHsLet hsDecls hsExp) subTable
  = do
      subTable' <- updateSubTableWithAHsDecls subTable hsDecls LetFun
      hsDecls' <- renameAHsDecls hsDecls subTable'
      hsExp' <- renameAHsExp hsExp subTable'
      return (AHsLet hsDecls' hsExp')
renameAHsExp (AHsIf hsExp1 hsExp2 hsExp3) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      hsExp3' <- renameAHsExp hsExp3 subTable
      return (AHsIf hsExp1' hsExp2' hsExp3')
renameAHsExp (AHsCase hsExp hsAlts) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      hsAlts' <- renameAHsAlts hsAlts subTable
      return (AHsCase hsExp' hsAlts')
renameAHsExp (AHsDo hsStmts) subTable
  = do
      (hsStmts',_) <- renameAHsStmts hsStmts subTable
      return (AHsDo hsStmts')
renameAHsExp (AHsTuple hsExps) subTable
  = do
      hsExps' <- renameAHsExps hsExps subTable
      return (AHsTuple hsExps')
renameAHsExp (AHsList hsExps) subTable
  = do
      hsExps' <- renameAHsExps hsExps subTable
      return (AHsList hsExps')
renameAHsExp (AHsParen hsExp) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      return (AHsParen hsExp')
renameAHsExp (AHsLeftSection hsExp1 hsExp2) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      return (AHsLeftSection hsExp1' hsExp2')
renameAHsExp (AHsRightSection hsExp1 hsExp2) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      return (AHsRightSection hsExp1' hsExp2')
-- XXX I'm not 100% sure that this bit works.
renameAHsExp (AHsRecConstr hsName hsFieldUpdates) subTable
  = do
      hsName' <- renameAHsName hsName subTable  -- do I need to change this name?
      hsFieldUpdates' <- renameAHsFieldUpdates hsFieldUpdates subTable
      return (AHsRecConstr hsName' hsFieldUpdates')
renameAHsExp (AHsRecUpdate hsExp hsFieldUpdates) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      hsFieldUpdates' <- renameAHsFieldUpdates hsFieldUpdates subTable
      return (AHsRecUpdate hsExp' hsFieldUpdates')
renameAHsExp (AHsEnumFrom hsExp) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      return (AHsEnumFrom hsExp')
renameAHsExp (AHsEnumFromTo hsExp1 hsExp2) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      return (AHsEnumFromTo hsExp1' hsExp2')
renameAHsExp (AHsEnumFromThen hsExp1 hsExp2) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      return (AHsEnumFromThen hsExp1' hsExp2')
renameAHsExp (AHsEnumFromThenTo hsExp1 hsExp2 hsExp3) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      hsExp3' <- renameAHsExp hsExp3 subTable
      return (AHsEnumFromThenTo hsExp1' hsExp2' hsExp3')
renameAHsExp (AHsListComp hsExp hsStmts) subTable
  = do
      (hsStmts',subTable') <- renameAHsStmts hsStmts subTable
      hsExp' <- renameAHsExp hsExp subTable'
      return (AHsListComp hsExp' hsStmts')     
renameAHsExp (AHsExpTypeSig srcLoc hsExp hsQualType) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      subTable' <- updateSubTableWithAHsQualType subTable hsQualType
      hsQualType' <- renameAHsQualType hsQualType subTable'
      return (AHsExpTypeSig srcLoc hsExp' hsQualType')
renameAHsExp (AHsAsPat hsName hsExp) subTable
  = do
      hsName' <- renameAHsName hsName subTable
      hsExp' <- renameAHsExp hsExp subTable
      return (AHsAsPat hsName' hsExp')
renameAHsExp (AHsWildCard) _
  = do
      return (AHsWildCard)
renameAHsExp (AHsIrrPat hsExp) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      return (AHsIrrPat hsExp')


renameAHsAlts :: [AHsAlt] -> SubTable -> ScopeSM [AHsAlt]
renameAHsAlts = mapRename renameAHsAlt

-- note for renameAHsAlt, the 'wheres' dominate the 'pats'

renameAHsAlt :: AHsAlt -> SubTable -> ScopeSM (AHsAlt)
renameAHsAlt (AHsAlt srcLoc hsPat hsGuardedAlts {-where-} hsDecls) subTable
  = do
      subTable' <- updateSubTableWithAHsPats subTable [hsPat] srcLoc CasePat
      hsPat' <- renameAHsPat hsPat subTable'
      subTable'' <- updateSubTableWithAHsDecls subTable' hsDecls WhereFun
      hsDecls' <- renameAHsDecls hsDecls subTable''
      hsGuardedAlts' <- renameAHsGuardedAlts hsGuardedAlts subTable''
      return (AHsAlt srcLoc hsPat' hsGuardedAlts' hsDecls')

renameAHsGuardedAlts :: AHsGuardedAlts -> SubTable -> ScopeSM (AHsGuardedAlts)
renameAHsGuardedAlts (AHsUnGuardedAlt hsExp) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      return (AHsUnGuardedAlt hsExp')
renameAHsGuardedAlts (AHsGuardedAlts hsGuardedAltList) subTable
  = do
      hsGuardedAltList' <- renameAHsGuardedAltList hsGuardedAltList subTable
      return (AHsGuardedAlts hsGuardedAltList')

renameAHsGuardedAltList :: [AHsGuardedAlt] -> SubTable -> ScopeSM [AHsGuardedAlt]
renameAHsGuardedAltList = mapRename renameAHsGuardedAlt

renameAHsGuardedAlt :: AHsGuardedAlt -> SubTable -> ScopeSM AHsGuardedAlt
renameAHsGuardedAlt (AHsGuardedAlt srcLoc hsExp1 hsExp2) subTable
  = do
      hsExp1' <- renameAHsExp hsExp1 subTable
      hsExp2' <- renameAHsExp hsExp2 subTable
      return (AHsGuardedAlt srcLoc hsExp1' hsExp2')

-- renameAHsStmts is trickier than you would expect because
-- the statements are only in scope after they have been declared
-- and thus the subTable must be more carefully threaded through

-- the updated subTable is returned at the end because it is needed by
-- the first section of a list comprehension.

renameAHsStmts :: [AHsStmt] -> SubTable -> ScopeSM (([AHsStmt],SubTable))
renameAHsStmts (hsStmt:hsStmts) subTable
  = do
      subTable' <- updateSubTableWithAHsStmt subTable hsStmt
      hsStmt' <- renameAHsStmt hsStmt subTable'
      (hsStmts',subTable'') <- renameAHsStmts hsStmts subTable'
      return ((hsStmt':hsStmts'),subTable'')
renameAHsStmts [] subTable
  = do
      return ([],subTable)

renameAHsStmt :: AHsStmt -> SubTable -> ScopeSM (AHsStmt)
renameAHsStmt (AHsGenerator srcLoc hsPat hsExp) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      hsPat' <- renameAHsPat hsPat subTable
      return (AHsGenerator srcLoc hsPat' hsExp')
renameAHsStmt (AHsQualifier hsExp) subTable
  = do
      hsExp' <- renameAHsExp hsExp subTable
      return (AHsQualifier hsExp')
renameAHsStmt (AHsLetStmt hsDecls) subTable
  = do
      hsDecls' <- renameAHsDecls hsDecls subTable
      return (AHsLetStmt hsDecls')


renameAHsFieldUpdates :: [AHsFieldUpdate] -> SubTable -> ScopeSM ([AHsFieldUpdate])
renameAHsFieldUpdates = mapRename renameAHsFieldUpdate

renameAHsFieldUpdate :: AHsFieldUpdate -> SubTable -> ScopeSM (AHsFieldUpdate)
-- XXX I'm not 100% sure that this works
{-
renameAHsFieldUpdate (AHsFieldBind hsName) subTable
  = do
      hsName' <- renameAHsName hsName subTable  -- do i need to rename this name?
      return (AHsFieldBind hsName')
-}
renameAHsFieldUpdate (AHsFieldUpdate hsName hsExp) subTable
  = do
      -- this is a field name and should already be unique but I will rename it for completeness.
      hsName' <- renameAHsName hsName subTable
      hsExp' <- renameAHsExp hsExp subTable
      return (AHsFieldUpdate hsName' hsExp')


renameAHsNames :: [AHsName] -> SubTable -> ScopeSM ([AHsName])
renameAHsNames = mapRename renameAHsName 

-- This looks up a replacement name in the subtable.
-- Regardless of whether the name is found, if it's not qualified 
-- it will be qualified with the current module's prefix. 
renameAHsName :: AHsName -> SubTable -> ScopeSM (AHsName)
renameAHsName hsName subTable
  = case lookupDftFM subTable hsName hsName of
         name@(AQual _ _) -> return name
         AUnQual name -> do modName <- getCurrentModule 
                            return (AQual modName name)




---------------------------------------
-- utility functions

-- clobberAHsName(s) is called by the updateSubTableWith* functions to
-- deal with newly declared identifiers

-- clobberAHsName(s) adds new mappings to the SubTable.
-- If a name already appeared, it's mapping is altered to the new one.

-- clobberAHsNamesAndUpdateIdentTable also adds a mapping from this
-- renamed name to its source location and binding type 

clobberAHsNamesAndUpdateIdentTable :: [(AHsName,ASrcLoc)] -> SubTable -> Binding -> ScopeSM (SubTable)
clobberAHsNamesAndUpdateIdentTable ((hsName,srcLoc):hsNamesAndASrcLocs) subTable binding
  = do
      subTable'  <- clobberAHsNameAndUpdateIdentTable hsName srcLoc subTable binding
      subTable'' <- clobberAHsNamesAndUpdateIdentTable hsNamesAndASrcLocs subTable' binding
      return (subTable'')
clobberAHsNamesAndUpdateIdentTable [] subTable _binding
  = return (subTable)

clobberAHsNameAndUpdateIdentTable :: AHsName -> ASrcLoc -> SubTable -> Binding -> ScopeSM (SubTable)
clobberAHsNameAndUpdateIdentTable hsName srcLoc subTable binding
  = do
      unique <- getUnique
      currModule <- getCurrentModule
      let
        hsName'     = renameAndQualify hsName unique currModule
        subTable'   = addToFM hsName hsName' subTable
      addToIdentTable hsName' (srcLoc, binding)
      incUnique
      return (subTable')


-- takes a list of names and a subtable. adds the associations
-- [name -> renamedName] to the table and returns it.
clobberAHsNames :: [AHsName] -> SubTable -> ScopeSM (SubTable)
clobberAHsNames (hsName:hsNames) subTable
  = do
      subTable'  <- clobberAHsName  hsName  subTable 
      subTable'' <- clobberAHsNames hsNames subTable'
      return (subTable'')
clobberAHsNames [] subTable
  = return subTable

clobberAHsName :: AHsName -> SubTable -> ScopeSM (SubTable)
clobberAHsName hsName subTable
  = do
      unique     <- getUnique       
      currModule <- getCurrentModule
      let hsName'     = renameAndQualify hsName unique currModule
          subTable'   = addToFM hsName hsName' subTable
      incUnique
      return (subTable')



renameAndQualify :: AHsName -> Unique -> AModule -> AHsName
renameAndQualify name unique currentMod
    = case rename name unique of
           AUnQual name' -> AQual currentMod name'
           qual_name    -> qual_name

-- renames a haskell name with its unique number 
rename :: AHsName -> Unique -> AHsName
rename (AUnQual i) unique
 = AUnQual $ renameIdent i unique
rename (AQual modName i) unique
 = AQual modName $ renameIdent i unique

renameIdent :: AHsIdentifier -> Unique -> AHsIdentifier
renameIdent i unique
   = case i of
        AHsIdent s   -> AHsIdent   $ show unique ++ "_" ++ s 
        AHsSpecial s -> AHsSpecial $ show unique ++ "_" ++ s 
        AHsSymbol s  -> AHsSymbol  $ show unique ++ "_" ++ s 

-- unRename gets the original identifier name 

unRename :: AHsName -> AHsName
unRename name
   = case isRenamed name of
          False -> name
          True  -> case name of
                      AUnQual i   -> AUnQual   $ unrenameIdent i
                      AQual mod i -> AQual mod $ unrenameIdent i 

unrenameIdent :: AHsIdentifier -> AHsIdentifier
unrenameIdent i
   = case i of
        AHsIdent s   -> AHsIdent   $ unRenameString s
        AHsSpecial s -> AHsSpecial $ unRenameString s
        AHsSymbol s  -> AHsSymbol  $ unRenameString s

isRenamed :: AHsName -> Bool
isRenamed (AUnQual i)    = isIdentRenamed i 
isRenamed (AQual _mod i) = isIdentRenamed i 

-- an identifier is renamed if it starts with one or more digits
-- such an identifier would normally be illegal in Haskell
isIdentRenamed :: AHsIdentifier -> Bool
isIdentRenamed i = not $ null $ takeWhile isDigit $ fromAHsIdentifier i




unRenameString :: String -> String
unRenameString s
   = (dropUnderscore . dropDigits) s
   where
   dropUnderscore ('_':rest) = rest
   dropUnderscore otherList = otherList
   dropDigits = dropWhile isDigit


-- returns the binding type of a given identifier

bindOfId :: IdentTable -> AHsName -> Binding
bindOfId idtab i
   = case lookupFM idtab i of 
        Nothing -> error $ "bindOfId: could not find binding for this identifier: " ++ show i
        Just (_sloc, bind) -> bind

--------------------------------------------------------
----This section of code updates the current SubTable to reflect the present scope


updateSubTableWithAHsDecls :: SubTable -> [AHsDecl] -> Binding -> ScopeSM (SubTable)
updateSubTableWithAHsDecls subTable [] _binding = return subTable
updateSubTableWithAHsDecls subTable (hsDecl:hsDecls) binding
  = do
      let hsNamesAndASrcLocs = getAHsNamesAndASrcLocsFromAHsDecl hsDecl
      subTable'  <- clobberAHsNamesAndUpdateIdentTable hsNamesAndASrcLocs subTable binding
      subTable'' <- updateSubTableWithAHsDecls subTable' hsDecls binding
      return (subTable'')

updateSubTableWithAHsPats :: SubTable -> [AHsPat] -> ASrcLoc -> Binding -> ScopeSM (SubTable)
updateSubTableWithAHsPats subTable (hsPat:hsPats) srcLoc binding
  = do
      let
        hsNamesAndASrcLocs = zip (getAHsNamesFromAHsPat hsPat) (repeat srcLoc)
      subTable'  <- clobberAHsNamesAndUpdateIdentTable hsNamesAndASrcLocs subTable binding
      subTable'' <- updateSubTableWithAHsPats subTable' hsPats srcLoc binding
      return subTable''
updateSubTableWithAHsPats subTable [] _srcLoc _binding
  = do return (subTable)

-- Only one AHsStmt should be added at a time because each new identifier is only valid
-- below the point at which it is defined

updateSubTableWithAHsStmt :: SubTable -> AHsStmt -> ScopeSM (SubTable)
updateSubTableWithAHsStmt subTable hsStmt
  = do
      let
        hsNamesAndASrcLocs = getAHsNamesAndASrcLocsFromAHsStmt hsStmt
      subTable' <- clobberAHsNamesAndUpdateIdentTable hsNamesAndASrcLocs subTable GenPat
      return (subTable')

----------------------------------------------------------
-- the following updateSubTableWith* functions do not need to alter the identTable aswell
--


-- takes a list of AHsNames representing type variables in a data decl and
-- adds them to the current subTable

updateSubTableWithAHsNames :: SubTable -> [AHsName] -> ScopeSM (SubTable)
updateSubTableWithAHsNames subTable hsNames
  = do
      subTable' <- clobberAHsNames hsNames subTable
      return (subTable')

-- takes an AHsQualType (a type signature) and adds the names of its variables
-- to the current subTable

updateSubTableWithAHsQualType :: SubTable -> AHsQualType -> ScopeSM (SubTable)
updateSubTableWithAHsQualType subTable hsQualType
  = do
      let
        hsNames = nub $ getAHsNamesFromAHsQualType hsQualType
      subTable' <- clobberAHsNames hsNames subTable
      return (subTable')

-- yet another class only function.
-- It uses getNewAHsNamesFromAHsQualType instead of getAHsNamesFromAHsQualType to only get
-- the names that are not already in scope (to avoid _re_ renaming things)

updateSubTableWithAHsQualType_insideClass :: SubTable -> AHsQualType -> ScopeSM (SubTable)
updateSubTableWithAHsQualType_insideClass subTable hsQualType
  = do
      let
        hsNames = nub $ getNewAHsNamesFromAHsQualType subTable hsQualType
      subTable' <- clobberAHsNames hsNames subTable
      return (subTable')


-- takes a list of decls and examines only the class decls
-- to get the names of variables used in their type sigs

updateSubTableWithClasses :: SubTable -> [AHsDecl] -> ScopeSM (SubTable)
updateSubTableWithClasses subTable []
  = return subTable
updateSubTableWithClasses subTable (hsDecl:hsDecls)
  = do
      let hsNames = getAHsNamesFromClass hsDecl
      subTable'  <- clobberAHsNames hsNames subTable
      subTable'' <- updateSubTableWithClasses subTable' hsDecls 
      return (subTable'')

getAHsNamesAndASrcLocsFromAHsDecl :: AHsDecl -> [(AHsName, ASrcLoc)]
getAHsNamesAndASrcLocsFromAHsDecl (AHsPatBind srcLoc (AHsPVar hsName) _ _)
  = [(hsName, srcLoc)]
-- This will cause errors on code with PatBinds of the form (x,y) = blah...
-- and should be changed for a more general renamer (but is fine for thih)
getAHsNamesAndASrcLocsFromAHsDecl (AHsPatBind sloc _ _ _)
  = error $ "non simple pattern binding found (sloc): " ++ show sloc 
-- getAHsNamesAndASrcLocsFromAHsDecl (AHsFunBind _ hsMatches)
getAHsNamesAndASrcLocsFromAHsDecl (AHsFunBind hsMatches)
  = getAHsNamesAndASrcLocsFromAHsMatches hsMatches
getAHsNamesAndASrcLocsFromAHsDecl _otherAHsDecl
  = []

getAHsNamesAndASrcLocsFromAHsMatches :: [AHsMatch] -> [(AHsName, ASrcLoc)]
getAHsNamesAndASrcLocsFromAHsMatches [] = []
--- WARNING: (Bryn) This seems like a bug not to use hsMatches
getAHsNamesAndASrcLocsFromAHsMatches (hsMatch:_hsMatches)
  = getAHsNamesAndASrcLocsFromAHsMatch hsMatch

getAHsNamesAndASrcLocsFromAHsMatch :: AHsMatch -> [(AHsName, ASrcLoc)]
getAHsNamesAndASrcLocsFromAHsMatch (AHsMatch srcLoc hsName _ _ _)
  = [(hsName, srcLoc)]


getAHsNamesFromAHsPat :: AHsPat -> [AHsName]
getAHsNamesFromAHsPat (AHsPVar hsName)
  = [hsName]
getAHsNamesFromAHsPat (AHsPLit _hsName)
  = []
getAHsNamesFromAHsPat (AHsPNeg hsPat)
  = getAHsNamesFromAHsPat hsPat
getAHsNamesFromAHsPat (AHsPInfixApp hsPat1 _hsName hsPat2) -- hsName can be ignored as it is a Constructor (e.g. in (x:xs) we only want to know what's in scope; that is x and xs)
  = getAHsNamesFromAHsPat hsPat1 ++ getAHsNamesFromAHsPat hsPat2
getAHsNamesFromAHsPat (AHsPApp _hsName hsPats)
  = concat (map getAHsNamesFromAHsPat hsPats)
getAHsNamesFromAHsPat (AHsPTuple hsPats)
  = concat (map getAHsNamesFromAHsPat hsPats)
getAHsNamesFromAHsPat (AHsPList hsPats)
  = concat (map getAHsNamesFromAHsPat hsPats)
getAHsNamesFromAHsPat (AHsPParen hsPat)
  = getAHsNamesFromAHsPat hsPat
getAHsNamesFromAHsPat (AHsPRec _hsName hsPatFields)
  = concat $ map getAHsNamesFromAHsPatField hsPatFields -- hsName can be ignored as it is a Constructor
getAHsNamesFromAHsPat (AHsPAsPat hsName hsPat)
  = hsName:(getAHsNamesFromAHsPat hsPat)
getAHsNamesFromAHsPat (AHsPWildCard)
  = []
getAHsNamesFromAHsPat (AHsPIrrPat hsPat)
  = getAHsNamesFromAHsPat hsPat

-- the hsName can be ignored as it is the field name and must already be in scope
getAHsNamesFromAHsPatField :: AHsPatField -> [AHsName]
{-
getAHsNamesFromAHsPatField (AHsPFieldPun _hsName)
  = []
  -}
getAHsNamesFromAHsPatField (AHsPFieldPat _hsName hsPat)
  = getAHsNamesFromAHsPat hsPat

getAHsNamesAndASrcLocsFromAHsStmt :: AHsStmt -> [(AHsName, ASrcLoc)]
getAHsNamesAndASrcLocsFromAHsStmt (AHsGenerator srcLoc hsPat _hsExp)
  = zip (getAHsNamesFromAHsPat hsPat) (repeat srcLoc)
getAHsNamesAndASrcLocsFromAHsStmt (AHsQualifier _hsExp)
  = []
getAHsNamesAndASrcLocsFromAHsStmt (AHsLetStmt hsDecls)
  = concat $ map getAHsNamesAndASrcLocsFromAHsDecl hsDecls


-- the getNew... functions are used only inside class declarations to avoid _re_ renaming things
-- that should be left as is.

getNewAHsNamesFromAHsQualType :: SubTable -> AHsQualType -> [AHsName]
getNewAHsNamesFromAHsQualType subTable (AHsQualType _hsContext hsType)
  = getNewAHsNamesFromAHsType subTable hsType
getNewAHsNamesFromAHsQualType subTable (AHsUnQualType hsType)
  = getNewAHsNamesFromAHsType subTable hsType

getNewAHsNamesFromAHsType :: SubTable -> AHsType -> [AHsName]
getNewAHsNamesFromAHsType subTable (AHsTyFun hsType1 hsType2)
  = (getNewAHsNamesFromAHsType subTable hsType1) ++ (getNewAHsNamesFromAHsType subTable hsType2)
getNewAHsNamesFromAHsType subTable (AHsTyTuple hsTypes)
  = concat $ map (getNewAHsNamesFromAHsType subTable) hsTypes
getNewAHsNamesFromAHsType subTable (AHsTyApp hsType1 hsType2)
  = (getNewAHsNamesFromAHsType subTable hsType1) ++ (getNewAHsNamesFromAHsType subTable hsType2)
getNewAHsNamesFromAHsType subTable (AHsTyVar hsName)
  | lookupFM subTable hsName == Nothing = [hsName]
  | otherwise                           = []
getNewAHsNamesFromAHsType _subTable (AHsTyCon _hsName)
  = [] -- don't rename the Constructors

getAHsNamesFromAHsQualType :: AHsQualType -> [AHsName]
getAHsNamesFromAHsQualType (AHsQualType _hsContext hsType)
  = getAHsNamesFromAHsType hsType
getAHsNamesFromAHsQualType (AHsUnQualType hsType)
  = getAHsNamesFromAHsType hsType

getAHsNamesFromAHsType :: AHsType -> [AHsName]
getAHsNamesFromAHsType (AHsTyFun hsType1 hsType2)
  = (getAHsNamesFromAHsType hsType1) ++ (getAHsNamesFromAHsType hsType2)
getAHsNamesFromAHsType (AHsTyTuple hsTypes)
  = concat $ map getAHsNamesFromAHsType hsTypes
getAHsNamesFromAHsType (AHsTyApp hsType1 hsType2)
  = (getAHsNamesFromAHsType hsType1) ++ (getAHsNamesFromAHsType hsType2)
getAHsNamesFromAHsType (AHsTyVar hsName)
  = [hsName]
getAHsNamesFromAHsType (AHsTyCon _hsName)
  = [] -- don't rename the Constructors


-- gets the names of the functions declared in a class declaration

getAHsNamesFromClass :: AHsDecl -> [AHsName]
getAHsNamesFromClass (AHsClassDecl _srcLoc _hsQualType hsDecls)
  = getAHsNamesFromTypeSigs hsDecls
getAHsNamesFromClass _otherDecl
  = []

-- gets the names of the functions whose types are declared in class decls

getAHsNamesFromTypeSigs :: [AHsDecl] -> [AHsName]
getAHsNamesFromTypeSigs ((AHsTypeSig _srcLoc hsNames _hsQualType):hsDecls)
  = hsNames ++ getAHsNamesFromTypeSigs hsDecls
getAHsNamesFromTypeSigs (_otherDecl:hsDecls)
  = getAHsNamesFromTypeSigs hsDecls
getAHsNamesFromTypeSigs []
  = []

--------------------------------------------------------------------------------

-- the Renameable class


-- stores the instance Renameable for all of AHsSyn

class Renameable a where
    replaceName :: (AHsName -> AHsName) -> a -> a

instance Renameable ASrcLoc where
    replaceName f = id

instance Renameable AHsExportSpec where
    replaceName f hsexportspec
      = let a # b = a $ (replaceName f b)
        in case hsexportspec of
            AHsEVar  name               ->
                AHsEVar  # name			
            AHsEAbs  name               ->
                AHsEAbs  # name			
            AHsEThingAll  name		 ->
                AHsEThingAll  # name		
            AHsEThingWith  name names	 ->
                AHsEThingWith  # name # names	
            AHsEModuleContents mod	 ->
                AHsEModuleContents mod	


instance Renameable AHsImportDecl where
    replaceName f object
      = let a # b = a $ (replaceName f b)
            a $$ b = a b
            infixl 0 $$
        in case object of
            AHsImportDecl  srcloc mod bool maybe1 maybe2 ->
                AHsImportDecl # srcloc $$ mod $$ bool $$ maybe1 $$ maybe2'
                where maybe2' = fmap (\(b,importSpec) -> (b, replaceName f importSpec)) maybe2


instance Renameable AHsImportSpec where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsIVar  name			 ->
                AHsIVar  # name			
            AHsIAbs  name			 ->
                AHsIAbs  # name			
            AHsIThingAll  name		 ->
                AHsIThingAll  # name		
            AHsIThingWith  name names	 ->
                AHsIThingWith  # name # names	


{-
instance Renameable AHsInfixDecl where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsInfixDecl  srcloc fixity names ->
                AHsInfixDecl  # srcloc # fixity # names
-}


{-
instance Renameable AHsFixity where
    replaceName f = id
-}

instance Renameable AHsAssoc where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsAssocNone  ->
                AHsAssocNone 
            AHsAssocLeft  ->
                AHsAssocLeft 
            AHsAssocRight  ->
                AHsAssocRight 


instance Renameable (AHsDecl) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsTypeDecl 	srcloc name names typ ->
                AHsTypeDecl 	srcloc # name # names # typ
            AHsDataDecl 	srcloc context name names condecls names' ->
                AHsDataDecl 	srcloc # context # name # names # condecls # names'
            AHsNewTypeDecl 	srcloc context name names condecl names' ->
                AHsNewTypeDecl 	srcloc # context # name # names # condecl # names'
            AHsClassDecl 	srcloc qualtyp objects ->
                AHsClassDecl 	srcloc # qualtyp # objects
            AHsInstDecl 	srcloc qualtyp objects ->
                AHsInstDecl 	srcloc # qualtyp # objects
            AHsDefaultDecl 	srcloc typ ->
                AHsDefaultDecl 	srcloc # typ
            AHsTypeSig 	srcloc names qualtyp ->
                AHsTypeSig 	srcloc # names # qualtyp
            -- AHsFunBind       srcloc matc ->
            AHsFunBind          matc ->
                -- AHsFunBind  # srcloc # matc
                AHsFunBind  # matc
            AHsPatBind 	srcloc pat r {-where-} objects ->
                AHsPatBind 	srcloc # pat # r # objects


instance Renameable (AHsMatch) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsMatch  srcloc name pats r {-where-} objects ->
                AHsMatch  # srcloc # name # pats # r # objects


instance Renameable AHsConDecl where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsConDecl  srcloc name bangtyps ->
                AHsConDecl  # srcloc # name # bangtyps
            AHsRecDecl  srcloc name names_and_bangtyp ->
                AHsRecDecl  # srcloc # name # names_and_bangtyp




instance Renameable AHsBangType where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsBangedTy    typ ->
                AHsBangedTy  # typ
            AHsUnBangedTy  typ ->
                AHsUnBangedTy  # typ


instance Renameable (AHsRhs) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsUnGuardedRhs  exp ->
                AHsUnGuardedRhs  # exp
            AHsGuardedRhss   guardedrs ->
                AHsGuardedRhss  # guardedrs


instance Renameable (AHsGuardedRhs) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsGuardedRhs  srcloc exp exp' ->
                AHsGuardedRhs  # srcloc # exp # exp'


instance Renameable AHsQualType where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsQualType    context typ ->
                AHsQualType  # context # typ
            AHsUnQualType  typ ->
                AHsUnQualType  # typ


instance Renameable AHsType where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsTyFun    typ typ' ->
                AHsTyFun  # typ # typ'
            AHsTyTuple  typs ->
                AHsTyTuple  # typs
            AHsTyApp    typ typ' ->
                AHsTyApp  # typ # typ'
            AHsTyVar    name ->
                AHsTyVar  # name
            AHsTyCon    name ->
                AHsTyCon  # name

instance Renameable AHsLiteral where
    replaceName f = id

instance Renameable (AHsExp) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            -- AHsVar  name ann -> AHsVar (replaceName f name) ann
            AHsVar  name -> AHsVar (replaceName f name) 
            AHsCon  name ->
                AHsCon  # name
            AHsLit  literal ->
                AHsLit  # literal
            AHsInfixApp  exp exp' exp'' ->
                AHsInfixApp  # exp # exp' # exp''
            AHsApp  exp exp' ->
                AHsApp  # exp # exp'
            AHsNegApp  exp ->
                AHsNegApp  # exp
            AHsLambda  srcloc pats exp ->
                AHsLambda  # srcloc # pats # exp
            AHsLet  objects exp ->
                AHsLet  # objects # exp
            AHsIf  exp exp' exp'' ->
                AHsIf  # exp # exp' # exp''
            AHsCase  exp alts ->
                AHsCase  # exp # alts
            AHsDo  stmts ->
                AHsDo  # stmts
            AHsTuple  exps ->
                AHsTuple  # exps
            AHsList  exps ->
                AHsList  # exps
            AHsParen  exp ->
                AHsParen  # exp
            AHsLeftSection  exp exp' ->
                AHsLeftSection  # exp # exp'
            AHsRightSection  exp exp' ->
                AHsRightSection  # exp # exp'
            AHsRecConstr  name fieldupdates ->
                AHsRecConstr  # name # fieldupdates
            AHsRecUpdate  exp fieldupdates ->
                AHsRecUpdate  # exp # fieldupdates
            AHsEnumFrom  exp ->
                AHsEnumFrom  # exp
            AHsEnumFromTo  exp exp' ->
                AHsEnumFromTo  # exp # exp'
            AHsEnumFromThen  exp exp' ->
                AHsEnumFromThen  # exp # exp'
            AHsEnumFromThenTo  exp exp' exp'' ->
                AHsEnumFromThenTo  # exp # exp' # exp''
            AHsListComp  exp stmts ->
                AHsListComp  # exp # stmts
            AHsExpTypeSig  srcloc exp qualtyp ->
                AHsExpTypeSig  # srcloc # exp # qualtyp
            AHsAsPat  name exp		 ->
                AHsAsPat  # name # exp		
            AHsWildCard 			 ->
                AHsWildCard 			
            AHsIrrPat  exp		 ->
                AHsIrrPat  # exp		

instance Renameable AHsPat where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsPVar  name ->
                AHsPVar  # name
            AHsPLit  literal ->
                AHsPLit  # literal
            AHsPNeg  pat ->
                AHsPNeg  # pat
            AHsPInfixApp  pat name pat' ->
                AHsPInfixApp  # pat # name # pat'
            AHsPApp  name pats ->
                AHsPApp  # name # pats
            AHsPTuple  pats ->
                AHsPTuple  # pats
            AHsPList  pats ->
                AHsPList  # pats
            AHsPParen  pat ->
                AHsPParen  # pat
            AHsPRec  name patfields ->
                AHsPRec  # name # patfields
            AHsPAsPat  name pat ->
                AHsPAsPat  # name # pat
            AHsPWildCard  ->
                AHsPWildCard 
            AHsPIrrPat  pat ->
                AHsPIrrPat  # pat


instance Renameable AHsPatField where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
{-
            AHsPFieldPun  name ->
                AHsPFieldPun  # name
-}
            AHsPFieldPat  name pat ->
                AHsPFieldPat  # name # pat


instance Renameable (AHsStmt) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsGenerator  srcloc pat exp ->
                AHsGenerator  # srcloc # pat # exp
            AHsQualifier  exp ->
                AHsQualifier  # exp
            AHsLetStmt  objects ->
                AHsLetStmt  # objects


instance Renameable (AHsFieldUpdate) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
{-
            AHsFieldBind  name ->
                AHsFieldBind  # name
-}
            AHsFieldUpdate  name exp ->
                AHsFieldUpdate  # name # exp


instance Renameable (AHsAlt) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsAlt  srcloc pat guardedalts objects ->
                AHsAlt  # srcloc # pat # guardedalts # objects


instance Renameable (AHsGuardedAlts) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsUnGuardedAlt  exp ->
                AHsUnGuardedAlt  # exp
            AHsGuardedAlts   guardedalts ->
                AHsGuardedAlts  # guardedalts

instance Renameable (AHsGuardedAlt) where
    replaceName f object
      = let a # b = a $ (replaceName f b)
        in case object of
            AHsGuardedAlt  srcloc exp exp' ->
                AHsGuardedAlt  # srcloc # exp # exp'

instance Renameable AHsName where 
    replaceName f name = f name

instance (Renameable a, Renameable b) => Renameable (a,b) where
    replaceName f (x,y) = (replaceName f x, replaceName f y)
instance Renameable a => Renameable [a] where
    replaceName f xs = map (replaceName f) xs
