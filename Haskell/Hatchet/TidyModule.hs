{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 TidyModule        

        Description:            Splits a module into its basic components

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module TidyModule (
                   tidyModule, 
                   tidyModuleToAHsModule, 
                   TidyModule (..) 
                  ) where

import AnnotatedHsSyn           (AHsModule (..),
                                 AModule,
                                 AHsDecl (..),
                                 AHsExportSpec,
                                 AHsImportDecl
                                ) 
--------------------------------------------------------------------------------

data TidyModule
     = TidyModule 
       {
         tidyModName    :: AModule,                    -- module name
         tidyExports    :: Maybe [AHsExportSpec],      -- export specification
         tidyImports    :: [AHsImportDecl],            -- import specification
         tidyTyDecls    :: [AHsDecl],                -- type decls (type synonyms)
         tidyDataDecls  :: [AHsDecl],                -- data decls
         tidyInFixDecls :: [AHsDecl],                -- infix decls
         tidyNewTyDecls :: [AHsDecl],                -- new type decls
         tidyClassDecls :: [AHsDecl],                -- class decls
         tidyInstDecls  :: [AHsDecl],                -- instance decls
         tidyDefDecls   :: [AHsDecl],                -- default decls
         tidyTySigs     :: [AHsDecl],                -- top-level type sigs
         tidyFunBinds   :: [AHsDecl],                -- top-level function bindings
         tidyPatBinds   :: [AHsDecl]                 -- top-level pattern bindings
       } deriving Show

initTidyModule :: AHsModule -> TidyModule 
initTidyModule (AHsModule modName exports imports _decls)
   = TidyModule {
         tidyModName      = modName,   
         tidyExports      = exports, 
         tidyImports      = imports, 
         tidyTyDecls      = [],
         tidyDataDecls    = [], 
         tidyInFixDecls   = [],
         tidyNewTyDecls   = [], 
         tidyClassDecls   = [],
         tidyInstDecls    = [],
         tidyDefDecls     = [],
         tidyTySigs       = [],
         tidyFunBinds     = [], 
         tidyPatBinds     = [] 
     }

tidyModuleToAHsModule :: TidyModule -> AHsModule
tidyModuleToAHsModule tmod 
  = AHsModule (tidyModName tmod)
              (tidyExports tmod)
              (tidyImports tmod) 
              (concat [tidyTyDecls tmod,
                       tidyDataDecls tmod,
                       tidyInFixDecls tmod,
                       tidyNewTyDecls tmod,
                       tidyClassDecls tmod,
                       tidyInstDecls tmod,
                       tidyDefDecls tmod,
                       tidyTySigs tmod,
                       tidyFunBinds tmod,
                       tidyPatBinds tmod])


tidyModule :: AHsModule -> TidyModule 
tidyModule mod@(AHsModule _modName _exports _imports decls)
   = makeTidyModule (initTidyModule mod) (reverse decls)    -- reverse the decls so they are collected in order
   where
   makeTidyModule :: TidyModule -> [AHsDecl] -> TidyModule
   makeTidyModule tidy [] = tidy
   makeTidyModule tidy (d:decls) 
      = case d of
           (AHsTypeDecl _ _ _ _) 
              -> let oldTyDecls    = tidyTyDecls tidy    in makeTidyModule tidy{tidyTyDecls    = d:oldTyDecls} decls
           (AHsDataDecl _ _ _ _ _ _) 
              -> let oldDataDecls  = tidyDataDecls tidy  in makeTidyModule tidy{tidyDataDecls  = d:oldDataDecls} decls
           (AHsInfixDecl _ _ _ _) 
              -> let oldInFixDecls = tidyInFixDecls tidy in makeTidyModule tidy{tidyInFixDecls = d:oldInFixDecls} decls
           (AHsNewTypeDecl _ _ _ _ _ _)
              -> let oldNewTyDecls = tidyNewTyDecls tidy in makeTidyModule tidy{tidyNewTyDecls = d:oldNewTyDecls} decls
           (AHsClassDecl _ _ _) 
              -> let oldClassDecls = tidyClassDecls tidy in makeTidyModule tidy{tidyClassDecls = d:oldClassDecls} decls
           (AHsInstDecl _ _ _) 
              -> let oldInstDecls  = tidyInstDecls tidy  in makeTidyModule tidy{tidyInstDecls  = d:oldInstDecls} decls
           (AHsDefaultDecl _ _)
              -> let oldDefs       = tidyDefDecls tidy   in makeTidyModule tidy{tidyDefDecls   = d:oldDefs} decls
           (AHsTypeSig _ _ _) 
              -> let oldTySigs     = tidyTySigs tidy     in makeTidyModule tidy{tidyTySigs     = d:oldTySigs} decls
           (AHsFunBind _)
              -> let oldFunBinds   = tidyFunBinds tidy   in makeTidyModule tidy{tidyFunBinds   = d:oldFunBinds} decls
           (AHsPatBind _ _ _ _) 
              -> let oldPatBinds   = tidyPatBinds tidy   in makeTidyModule tidy{tidyPatBinds   = d:oldPatBinds} decls

           
