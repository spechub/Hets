{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 MultiModuleBasics

        Description:            More Support code for type checking multi-module
                                programs. 

        Primary Authors:        Bryn Humberstone 

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module MultiModuleBasics where

import Env(Env, listToEnv, joinEnv, emptyEnv)
import KindInference(KindEnv)
import FiniteMaps(toListFM, listToFM)
import Class(ClassHierarchy)
import ParseLib
import Rename           (unRename)
import AnnotatedHsSyn
import Representation

--------------------------------------------------------------------------------


data ModuleInfo = ModuleInfo {
                    moduleName :: AModule,
                    varAssumps :: Env Scheme,
                    dconsAssumps :: Env Scheme,
                    -- tyconsMembers is a little bit of a hack (sorry)
                    -- so that we can see what each type constructor has 
                    -- as its datacons (see getTyconsMembers for an example)
                    classHierarchy :: ClassHierarchy,
                    kinds :: KindEnv,
                    synonyms :: [AHsDecl],
                    infixDecls :: [AHsDecl], -- infixities
                    tyconsMembers :: [(AHsName, [AHsName])]
                  } 


-- takes a module and figures out what type constructor each 
-- data constructor belongs to (return something like  
-- [(Prelude.Bool, [Prelude.True, Prelude.False])]
getTyconsMembers :: AHsModule -> [(AHsName, [AHsName])]
getTyconsMembers (AHsModule _ _ _ decls)
    = [ (tycon, map dconName dataconsDecls) | 
         decl@(AHsDataDecl _ _ tycon _ dataconsDecls _) <- decls ]
    where dconName (AHsConDecl _ name _) = name
          dconName (AHsRecDecl _ name _) = name

-- takes a module and just extracts all the InfixDecls (returns
-- it as a list of AHsDecl, all of which are AHsInfixDecl)
getInfixDecls :: AHsModule -> [AHsDecl]
getInfixDecls (AHsModule _ _ _ decls)
   = [ d | d@(AHsInfixDecl _ _ _ _) <- decls ]

emptyModuleInfo :: ModuleInfo
emptyModuleInfo 
    = ModuleInfo { varAssumps = emptyEnv,
                   moduleName = error "Unspecified module name",
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
            moduleName = error ("moduleName not defined since " ++ "merge of " 
                                 ++ mn mod1 ++ " and " ++ mn mod2),
            varAssumps = comb varAssumps joinEnv,
            dconsAssumps = comb dconsAssumps joinEnv,
            kinds = comb kinds joinEnv,
            tyconsMembers = comb tyconsMembers (++),
            classHierarchy = comb classHierarchy joinEnv,
            synonyms = comb synonyms (++),
            infixDecls = comb infixDecls (++)
    }
    where comb field joiningMethod = joiningMethod (field mod1) (field mod2)
          mn modInfo = (\(AModule x) -> x) (moduleName modInfo)


modToFilePath :: AModule -> FilePath
modToFilePath (AModule mod) = mod ++ ".ti"


{- The showing and parsing of ModuleInfo is also handled here. Hopefully you won't have
   to read through/debug this code ever! -}
-- we now have a toString and fromString function for everything that we need


{--     The rest of this module is devoted to the class PlainShowParse which is
        a simple way of showing/reading the structures we need. The reason we didn't
        just use 'Show' is that we might later change Show and then our MultiAModule
        parser would break                 --}

-- Need to output variable assumptions, data cons assumptions, 
-- class hierarchy, kind environment, type synonyms defined

-- this is so we can show things in the most boring (easily parsed) fashion possible
class PlainShowParse a where
   toString :: a -> String 
   plainParse :: Parser a   -- everything that's written to a file needs to be read
   
   fromString :: String -> a
   fromString str
       = case papply plainParse str of
              [(output,"")] -> output
              [] -> error $ "(MultiModuleBasics) No parse of " ++ str
              xs  -> error $ "Ambiguous parse of " ++ str ++ toString xs

   toStringList :: [a] -> String
   toStringList xs = genericShowList "[" (map toString xs) "]"

   plainParseList :: Parser [a]
   plainParseList = bracket (symbol "[") (plainParse `sepby` (symbol ",")) (symbol "]")

-- this is actually the instance we're interested in getting
instance PlainShowParse ModuleInfo where
    toString modInfo
        =  toString' ("moduleName", moduleName)
        ++ toString' ("varAssumps", varAssumps) 
        ++ toString' ("dconsAssumps", dconsAssumps) 
        ++ toString' ("classHierarchy", classHierarchy)
        ++ toString' ("kinds", kinds) 
        ++ toString' ("synonyms", synonyms)
        ++ toString' ("tyconsMembers", tyconsMembers)
        ++ toString' ("infixDecls", infixDecls)
        where toString' (name, selector) = toString (name, selector modInfo) ++ "\n\n"

    plainParse 
        = do
          ("moduleName", mn)     <- plainParse
          ("varAssumps", vars)   <- plainParse
          ("dconsAssumps", dc)   <- plainParse
          ("classHierarchy", ch) <- plainParse
          ("kinds", ks)          <- plainParse
          ("synonyms", syns)     <- plainParse
          ("tyconsMembers", tmb) <- plainParse
          ("infixDecls", ifd)    <- plainParse
          return $ ModuleInfo { moduleName = mn,
                                varAssumps = vars, 
                                dconsAssumps = dc,
                                classHierarchy = ch, 
                                kinds = ks,
                                infixDecls = ifd,
                                synonyms = syns,
                                tyconsMembers = tmb }





-- takes the opening/closing brackets and list of elements (as strings)
genericShowList :: String -> [String] -> String -> String
genericShowList opening elts closing
    = opening 
      ++ (if null elts then "" else foldr1 (\x y -> x ++ "," ++ y) elts)
      ++ closing
   

instance PlainShowParse a => PlainShowParse [a] where
    toString = toStringList
    plainParse = plainParseList 

instance PlainShowParse a => PlainShowParse (Env a) where
    toString fm = toString (toListFM fm)
    plainParse = do { x <- plainParseList; return (listToFM x) }

instance PlainShowParse Char where
    toString = show
    toStringList str = show str

    plainParse = bracket (char '\'') item (char '\'') -- anything in single quotes
    {- if this plainParseList fails, then just use reads from Prelude (you'll need to
       wrap it to make it of type Parser) -}
    plainParseList = parseString
        where
        -- this is trickier than it seems, as we must parse what show(String) produces
        -- including handling the escaping of quotes properly
        parseString :: Parser String
        parseString = bracket (char '"') (many respectEscapingChar) (char '"')
            where
            -- keep on working until you get to an unescaped quote
            respectEscapingChar :: Parser Char
            respectEscapingChar = escapedChar +++ sat (\x -> x /= '"')
            
            escapedChar = char '\\' >> item  
    
    -- tested on:
    -- fromString (toString "this is a \" test") :: String  ===> "this is a \" test"


instance PlainShowParse Int where
    toString = show
    plainParse = integer

instance (PlainShowParse a, PlainShowParse b) => PlainShowParse (a,b) where
    -- invisible constructor for tuples
    toString (x,y) = "" `withArgs` [toString x, toString y]

    plainParse 
        = do symbol "(";
             x <- plainParse; symbol ","; 
             y <- plainParse; symbol ")"; 
             return (x,y) 

instance (PlainShowParse a, PlainShowParse b, PlainShowParse c) => PlainShowParse (a,b,c) where
    -- invisible constructor for tuples
    toString (x,y,z) = "" `withArgs` [toString x, toString y, toString z]
        
    plainParse 
        = do 
          symbol "(";
          x <- plainParse; symbol ","; 
          y <- plainParse; symbol ","; 
          z <- plainParse; symbol ")"; 
          return (x,y,z) 

instance (PlainShowParse a, PlainShowParse b, PlainShowParse c, PlainShowParse d) => PlainShowParse (a,b,c,d) where
    -- invisible constructor for tuples
    toString (w,x,y,z) = "" `withArgs` [toString w, toString x, toString y, toString z]
        
    plainParse 
        = do 
          symbol "(";
          w <- plainParse; symbol ","; 
          x <- plainParse; symbol ","; 
          y <- plainParse; symbol ","; 
          z <- plainParse; symbol ")"; 
          return (w,x,y,z) 

withArgs :: String -> [String] -> String
withArgs dataCons args 
    = dataCons ++ genericShowList "(" args ")"

withBrackets :: String -> String
withBrackets str = "(" ++ str ++ ")"

-- this relies on the fact we can parse pairs/triples with brackets, so
-- Foo(a,b) is just symbol "Foo" followed by a (a,b)
parseWithArgs :: PlainShowParse a => String -> (a -> b) -> Parser b
parseWithArgs tag transformer
    = do symbol tag
         -- if we fail on the normal parse, this was probably a singleton, like
         -- AUnQual("foo"), so we have to insert brackets and try again
         res <- plainParse +++ bracketed plainParse +++ 
                  (error $ "parseWithArgs failed after committing to the tag " ++ tag) -- maybe with a function of 4 or more args?
         return (transformer res)


instance PlainShowParse AModule where
    toString (AModule name) = "AModule" `withArgs` [toString name]
    plainParse = "AModule" `parseWithArgs` AModule


-- this can be displayed as "Forall(kinds,preds,tp)"
instance PlainShowParse Scheme where
    toString (Forall kinds (preds :=> tp))
        = "Forall" `withArgs` [toString kinds, toString preds, toString tp]
    plainParse 
        = "Forall" `parseWithArgs` (\(kinds,ps,tp) -> Forall kinds (ps :=> tp))

-- AQual("Prelude","take")  is Prelude.take
instance PlainShowParse AHsName where
    -- we unrename the names to get rid of any 1_ or 23_ at front
    toString ahsname = toString' (unRename ahsname)
        where
        toString' (AQual (AModule str) val) = "AQual" `withArgs` [toString str, toString val]
        toString' (AUnQual val) = "AUnQual" `withArgs` [toString val]

    plainParse = qual +++ unqual
        where
        qual = "AQual" `parseWithArgs` (\(mod,n) -> (AQual (AModule mod) n))
        unqual = "AUnQual" `parseWithArgs` AUnQual

instance PlainShowParse AHsIdentifier where
   toString i 
      = case i of
           AHsIdent   s -> "AHsIdent"   `withArgs` [toString s]
           AHsSpecial s -> "AHsSpecial" `withArgs` [toString s]
           AHsSymbol  s -> "AHsSymbol"  `withArgs` [toString s]

   plainParse = ident +++ special +++ symbol
      where
      ident   = "AHsIdent"   `parseWithArgs` AHsIdent
      special = "AHsSpecial" `parseWithArgs` AHsSpecial 
      symbol  = "AHsSymbol"  `parseWithArgs` AHsSymbol 
       

-- e.g. TVarTyvar(AQual("Prelude","Int"), ...) where (...) is how we write kinds
instance PlainShowParse Type where
    toString t = 
        case t of 
           (TVar (Tyvar hsname kind)) -> "TVarTyvar" `withArgs` [toString hsname, toString kind]
           (TCon (Tycon hsname kind)) -> "TConTycon" `withArgs` [toString hsname, toString kind]
           (TAp t1 t2) -> "TAp" `withArgs` [toString t1, toString t2]
           (TGen int)  -> "TGen" `withArgs` [toString int]
           (TArrow t1 t2) -> "TArrow" `withArgs` [toString t1, toString t2]
           (TTuple types) -> "TTuple(" ++  toString types ++ ")"

    plainParse = tvar +++ tcon +++ tap +++ tgen +++ tarrow +++ ttuple
        where
        tvar = "TVarTyvar" `parseWithArgs` (\(hsname,kind) -> TVar (Tyvar hsname kind))
        tcon = "TConTycon" `parseWithArgs` (\(hsname,kind) -> TCon (Tycon hsname kind))
        tap  = "TAp" `parseWithArgs` (\(t1,t2) -> TAp t1 t2)
        tgen = "TGen" `parseWithArgs` TGen
        tarrow = "TArrow" `parseWithArgs` (\(t1,t2) -> TArrow t1 t2)
        ttuple = "TTuple" `parseWithArgs` (\ts -> TTuple ts) 


instance PlainShowParse Pred where
    toString (IsIn cls tp) = "IsIn" `withArgs` [toString cls, toString tp]
    plainParse = "IsIn" `parseWithArgs` (\(cls,tp) -> IsIn cls tp)

-- kinds aren't too hard to parse in infix notation, so we keep that (there
-- are going to be some extra brackets floating around in this printing)
instance PlainShowParse Kind where
    toString Star = "*"
    toString (Kfun k1 k2) = withBrackets (toString k1 ++ "->" ++ toString k2)

    plainParse = binopr "->" Kfun $  -- assumes bracketing to the right
                 bracketed plainParse +++ retVal "*" Star


-- instance PlainShowParse Class (a Class is just an AHsName)

instance PlainShowParse Inst where
    toString (preds :=> pred) = ":=>" `withArgs` [toString preds, toString pred]
    plainParse = ":=>" `parseWithArgs` (\(preds,pred) -> preds :=> pred)

instance PlainShowParse Assump where
    toString (name :>: scheme) = ":>:" `withArgs` [toString name, toString scheme]
    plainParse = ":>:" `parseWithArgs` (\(name,scheme) -> name :>: scheme)

instance PlainShowParse AHsAssoc where
    -- Note: it's important that these have quotes around them in the .ti
    -- files so that "infixr" doesn't get parsed as [("infix", "r")] which
    -- is obviously no good.
    toString AHsAssocNone = toString "infix"
    toString AHsAssocLeft = toString "infixl"
    toString AHsAssocRight = toString "infixr"

    plainParse = ("infix"  ==> AHsAssocNone)
             +++ ("infixl" ==> AHsAssocLeft)
             +++ ("infixr" ==> AHsAssocRight)
         where str ==> val = symbol ("\"" ++ str ++ "\"") >> return val

instance PlainShowParse AHsDecl where
    toString (AHsInfixDecl _ assoc binding names)
        = "AHsInfixDecl" `withArgs` [toString assoc, toString binding, toString names]
    toString (AHsTypeDecl _ name names hstype)
        = "AHsTypeDecl" `withArgs` [toString name, toString names, toString hstype]
    toString _ = 
        error "(MultiModuleBasics) Can't toString of AHsDecls other than infix/type syns"

    plainParse = infixDecl +++ typeDecl -- +++ cantParse
        where
        typeDecl = "AHsTypeDecl" `parseWithArgs` (\(a,b,c) -> AHsTypeDecl bogusASrcLoc a b c)
        infixDecl = "AHsInfixDecl" `parseWithArgs` (\(a,b,c) -> AHsInfixDecl bogusASrcLoc a b c)
        -- cantParse = error "(MultiModuleBasics) Can't plainParse AHsDecls other than infix/type syns!"

{-
    -- this is here so we can keep working with empty lists of synonyms
    plainParseList = empty +++ otherwise
        where empty = symbol "[]" >> return []
              otherwise = error "Sorry. I can't parse [AHsDecl] yet!"
              -}

instance PlainShowParse AHsType where
    toString (AHsTyFun t1 t2) = "AHsTyFun" `withArgs` [toString t1, toString t2]
    toString (AHsTyTuple ts) = "AHsTyTuple" `withArgs` [toString ts]
    toString (AHsTyApp t1 t2) = "AHsTyApp" `withArgs` [toString t1, toString t2]
    toString (AHsTyVar name) = "AHsTyVar" `withArgs` [toString name]
    toString (AHsTyCon name) = "AHsTyCon" `withArgs` [toString name]

    plainParse = tyfun +++ tytuple +++ tyapp +++ tyvar +++ tycon
        where
        tyfun   = "AHsTyFun" `parseWithArgs` (\(t1,t2) -> AHsTyFun t1 t2)
        tytuple = "AHsTyTuple" `parseWithArgs` AHsTyTuple
        tyapp   = "AHsTyApp" `parseWithArgs` (\(t1,t2) -> AHsTyApp t1 t2)
        tyvar   = "AHsTyVar" `parseWithArgs` AHsTyVar
        tycon   = "AHsTyCon" `parseWithArgs` AHsTyCon


-- so we can see which types we haven't done yet
todo :: String -> String
todo = id

-- useful little combinators

binopr :: String -> (a -> a -> a) -> Parser a -> Parser a 
binopr sym ret = flip chainr1 (retVal sym ret)

retVal :: String -> a -> Parser a 
retVal sym ret = symbol sym >> return ret

bracketed :: Parser a -> Parser a
bracketed parser = bracket (symbol "(") parser (symbol ")")
