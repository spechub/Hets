{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 MultiModuleBasics

        Description:            More Support code for type checking multi-module
                                programs. 

        Primary Authors:        Bryn Humberstone 

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module Haskell.Hatchet.MultiModuleBasics where

import Haskell.Hatchet.Env(Env, joinEnv, emptyEnv)
import Haskell.Hatchet.KindInference(KindEnv)
import Haskell.Hatchet.Class(ClassHierarchy)
import Haskell.Hatchet.AnnotatedHsSyn
import Haskell.Hatchet.Representation

--------------------------------------------------------------------------------


data ModuleInfo = ModuleInfo {
                    moduleName :: AModule,
                    varAssumps :: Env Scheme,  -- function declarations
                         -- map, mapping names to type schemes
                    dconsAssumps :: Env Scheme, -- type declarations
                    -- tyconsMembers is a little bit of a hack (sorry)
                    -- so that we can see what each type constructor has 
                    -- as its datacons (see getTyconsMembers for an example)
                    classHierarchy :: ClassHierarchy,
                    kinds :: KindEnv,
                    synonyms :: [AHsDecl],
                    infixDecls :: [AHsDecl], -- infixities
                    tyconsMembers :: [(AHsName, [AHsName])]
                  } 
   deriving Show


-- takes a module and figures out what type constructor each 
-- data constructor belongs to (return something like  
-- [(Prelude.Bool, [Prelude.True, Prelude.False])]
getTyconsMembers :: AHsModule -> [(AHsName, [AHsName])]
getTyconsMembers (AHsModule _ _ _ decls)
    = [ (tycon, map dconName dataconsDecls) | 
         (AHsDataDecl _ _ tycon _ dataconsDecls _) <- decls ]
    where dconName (AHsConDecl _ name _) = name
          dconName (AHsRecDecl _ name _) = name

-- takes a module and just extracts all the InfixDecls (returns
-- it as a list of AHsDecl, all of which are AHsInfixDecl)
getInfixDecls :: AHsModule -> [AHsDecl]
getInfixDecls (AHsModule _ _ _ decls)
   = [ d | d@(AHsInfixDecl _ _ _ _) <- decls ]
-- filters decls taking members of form (AHsInfixDecl _ _ _) 

emptyModuleInfo :: ModuleInfo
emptyModuleInfo 
    = ModuleInfo { varAssumps = emptyEnv,
                   moduleName = AModule "Empty",
                   dconsAssumps = emptyEnv,
                   classHierarchy = emptyEnv,
                   tyconsMembers = [], 
                   kinds = emptyEnv,
                   infixDecls = [],
                   synonyms = [] }
    

concatModuleInfos :: [ModuleInfo] -> ModuleInfo
concatModuleInfos = foldr joinModuleInfo emptyModuleInfo 

joinModuleInfo :: ModuleInfo -> ModuleInfo -> ModuleInfo
joinModuleInfo mod1 mod2
    = ModuleInfo {
            moduleName = AModule mn,
            varAssumps = comb varAssumps joinEnv,
            dconsAssumps = comb dconsAssumps joinEnv,
            kinds = comb kinds joinEnv,
            tyconsMembers = comb tyconsMembers (++),
            classHierarchy = comb classHierarchy joinEnv,
            synonyms = comb synonyms (++),
            infixDecls = comb infixDecls (++)
    }
    where comb field joiningMethod = joiningMethod (field mod1) (field mod2)
          mn = (\(AModule x) -> x) (moduleName mod1)

modToFilePath :: AModule -> FilePath
modToFilePath (AModule m) = m ++ ".ti"

