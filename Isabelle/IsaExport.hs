module Isabelle.IsaExport where

import Text.XML.HaXml.XmlContent hiding (Const)
import Text.XML.HaXml.OneOfN
import Text.XML.HaXml.Types


{-Type decls-}

newtype Export = Export (List1 Thy)   deriving (Eq,Show)
data Thy = Thy Thy_Attrs (List1 Import) [Keyword] [UseFile] Body
         deriving (Eq,Show)
data Thy_Attrs = Thy_Attrs
    { thyName :: String
    , thyHeader :: (Maybe String)
    } deriving (Eq,Show)
data Keyword = Keyword
    { keywordName :: String
    } deriving (Eq,Show)
data Import = Import
    { importName :: String
    } deriving (Eq,Show)
data UseFile = UseFile
    { useFileName :: String
    } deriving (Eq,Show)
newtype Body = Body [Body_]   deriving (Eq,Show)
data Body_ = Body_Locale Locale
           | Body_Cls Cls
           | Body_TypeSynonym TypeSynonym
           | Body_Datatypes Datatypes
           | Body_Domains Domains
           | Body_Consts Consts
           | Body_Axioms Axioms
           | Body_Lemma Lemma
           | Body_Definition Definition
           | Body_Funs Funs
           | Body_Primrec Primrec
           | Body_Fixrec Fixrec
           | Body_Instantiation Instantiation
           | Body_Instance Instance
           | Body_Subclass Subclass
           | Body_Typedef Typedef
           | Body_Defs Defs
           deriving (Eq,Show)
data Locale = Locale Locale_Attrs Ctxt [Parent] Body
            deriving (Eq,Show)
data Locale_Attrs = Locale_Attrs
    { localeName :: String
    } deriving (Eq,Show)
data Cls = Cls Cls_Attrs Ctxt [Parent] Body
         deriving (Eq,Show)
data Cls_Attrs = Cls_Attrs
    { clsName :: String
    } deriving (Eq,Show)
data TypeSynonym = TypeSynonym TypeSynonym_Attrs (Maybe Mixfix)
                               Vars (OneOf3 TVar TFree Type)
                 deriving (Eq,Show)
data TypeSynonym_Attrs = TypeSynonym_Attrs
    { typeSynonymName :: String
    , typeSynonymTarget :: (Maybe String)
    } deriving (Eq,Show)
newtype Datatypes = Datatypes (List1 Datatype)   deriving (Eq,Show)
data Datatype = Datatype Datatype_Attrs (Maybe Mixfix)
                         (List1 Constructor) [TFree]
              deriving (Eq,Show)
data Datatype_Attrs = Datatype_Attrs
    { datatypeName :: String
    } deriving (Eq,Show)
data Constructor = Constructor Constructor_Attrs (Maybe Mixfix)
                               (OneOf3 TVar TFree Type) [(OneOf3 TVar TFree Type)]
                 deriving (Eq,Show)
data Constructor_Attrs = Constructor_Attrs
    { constructorName :: (Maybe String)
    } deriving (Eq,Show)
newtype Domains = Domains (List1 Domain)   deriving (Eq,Show)
data Domain = Domain Domain_Attrs (Maybe Mixfix) [TFree]
                     (List1 DomainConstructor)
            deriving (Eq,Show)
data Domain_Attrs = Domain_Attrs
    { domainName :: String
    } deriving (Eq,Show)
data DomainConstructor = DomainConstructor DomainConstructor_Attrs
                                           (OneOf3 TVar TFree Type) [DomainConstructorArg]
                       deriving (Eq,Show)
data DomainConstructor_Attrs = DomainConstructor_Attrs
    { domainConstructorName :: String
    } deriving (Eq,Show)
data DomainConstructorArg = DomainConstructorArg DomainConstructorArg_Attrs
                                                 (OneOf3 TVar TFree Type)
                          deriving (Eq,Show)
data DomainConstructorArg_Attrs = DomainConstructorArg_Attrs
    { domainConstructorArgLazy :: (Maybe String)
    , domainConstructorArgName :: (Maybe String)
    } deriving (Eq,Show)
newtype Consts = Consts (List1 ConstDef)   deriving (Eq,Show)
data ConstDef = ConstDef ConstDef_Attrs (Maybe Mixfix)
                         (OneOf3 TVar TFree Type)
              deriving (Eq,Show)
data ConstDef_Attrs = ConstDef_Attrs
    { constDefName :: String
    } deriving (Eq,Show)
newtype Axioms = Axioms (List1 Axiom)   deriving (Eq,Show)
data Axiom = Axiom Axiom_Attrs
                   (OneOf6 Bound Free Var Const App Abs)
           deriving (Eq,Show)
data Axiom_Attrs = Axiom_Attrs
    { axiomName :: String
    , axiomArgs :: String
    } deriving (Eq,Show)
data Lemma = Lemma Lemma_Attrs Ctxt Proof (List1 (Shows))
           deriving (Eq,Show)
data Lemma_Attrs = Lemma_Attrs
    { lemmaTarget :: (Maybe String)
    } deriving (Eq,Show)
data Definition = Definition Definition_Attrs (Maybe Mixfix)
                             (OneOf3 TVar TFree Type)
                             (List1 (OneOf6 Bound Free Var Const App Abs))
                deriving (Eq,Show)
data Definition_Attrs = Definition_Attrs
    { definitionName :: String
    , definitionTarget :: (Maybe String)
    } deriving (Eq,Show)
data Funs = Funs Funs_Attrs (List1 Fun)
          deriving (Eq,Show)
data Funs_Attrs = Funs_Attrs
    { funsTarget :: (Maybe String)
    , funsSequential :: (Maybe String)
    , funsDefault :: (Maybe String)
    , funsDomintros :: (Maybe String)
    , funsPartials :: (Maybe String)
    } deriving (Eq,Show)
data Fun = Fun Fun_Attrs (Maybe Mixfix) (OneOf3 TVar TFree Type)
               (List1 Equation)
         deriving (Eq,Show)
data Fun_Attrs = Fun_Attrs
    { funName :: String
    } deriving (Eq,Show)
newtype Equation = Equation (List1 (OneOf6 Bound Free Var Const App Abs))   deriving (Eq,Show)
data Primrec = Primrec Primrec_Attrs (List1 Fun)
             deriving (Eq,Show)
data Primrec_Attrs = Primrec_Attrs
    { primrecTarget :: (Maybe String)
    } deriving (Eq,Show)
newtype Fixrec = Fixrec (List1 FixrecFun)   deriving (Eq,Show)
data FixrecFun = FixrecFun FixrecFun_Attrs (Maybe Mixfix)
                           (OneOf3 TVar TFree Type) (List1 FixrecEquation)
               deriving (Eq,Show)
data FixrecFun_Attrs = FixrecFun_Attrs
    { fixrecFunName :: String
    } deriving (Eq,Show)
data FixrecEquation = FixrecEquation FixrecEquation_Attrs Premises
                                     (List1 (OneOf6 Bound Free Var Const App Abs))
                    deriving (Eq,Show)
data FixrecEquation_Attrs = FixrecEquation_Attrs
    { fixrecEquationUnchecked :: (Maybe String)
    } deriving (Eq,Show)
newtype Premises = Premises [(OneOf6 Bound Free Var Const App Abs)]   deriving (Eq,Show)
data Instantiation = Instantiation Instantiation_Attrs Arity Body
                   deriving (Eq,Show)
data Instantiation_Attrs = Instantiation_Attrs
    { instantiationType :: String
    } deriving (Eq,Show)
data Instance = Instance Instance_Attrs Proof (Maybe (Vars,Arity))
              deriving (Eq,Show)
data Instance_Attrs = Instance_Attrs
    { instanceClass :: (Maybe String)
    , instanceRel :: (Maybe String)
    , instanceClass1 :: (Maybe String)
    } deriving (Eq,Show)
data Subclass = Subclass Subclass_Attrs Proof
              deriving (Eq,Show)
data Subclass_Attrs = Subclass_Attrs
    { subclassClass :: String
    , subclassTarget :: (Maybe String)
    } deriving (Eq,Show)
data Typedef = Typedef Typedef_Attrs (Maybe Mixfix) Proof
                       (OneOf6 Bound Free Var Const App Abs) [TFree]
             deriving (Eq,Show)
data Typedef_Attrs = Typedef_Attrs
    { typedefType :: String
    , typedefM1 :: (Maybe String)
    , typedefM2 :: (Maybe String)
    } deriving (Eq,Show)
data Defs = Defs Defs_Attrs (List1 Def)
          deriving (Eq,Show)
data Defs_Attrs = Defs_Attrs
    { defsUnchecked :: (Maybe String)
    , defsOverloaded :: (Maybe String)
    } deriving (Eq,Show)
data Def = Def Def_Attrs (OneOf3 TVar TFree Type)
               (OneOf6 Bound Free Var Const App Abs)
         deriving (Eq,Show)
data Def_Attrs = Def_Attrs
    { defName :: String
    , defArgs :: String
    , defConst :: String
    } deriving (Eq,Show)
newtype Sort = Sort (List1 Class)   deriving (Eq,Show)
data Arity = Arity Sort [Sort]
           deriving (Eq,Show)
newtype Vars = Vars [TFree]   deriving (Eq,Show)
data Parent = Parent
    { parentName :: String
    } deriving (Eq,Show)
newtype Fixes = Fixes [Fix]   deriving (Eq,Show)
data Fix = Fix Fix_Attrs (OneOf3 TVar TFree Type) (Maybe Mixfix)
         deriving (Eq,Show)
data Fix_Attrs = Fix_Attrs
    { fixName :: String
    } deriving (Eq,Show)
newtype Assumes = Assumes [Assumption]   deriving (Eq,Show)
data Assumption = Assumption Assumption_Attrs
                             (OneOf6 Bound Free Var Const App Abs)
                deriving (Eq,Show)
data Assumption_Attrs = Assumption_Attrs
    { assumptionName :: String
    , assumptionArgs :: String
    } deriving (Eq,Show)
newtype Ctxt = Ctxt [(OneOf2 Fixes Assumes)]   deriving (Eq,Show)
data Mixfix = Mixfix Mixfix_Attrs
                     [(OneOf4 Arg AString Break Block)]
            deriving (Eq,Show)
data Mixfix_Attrs = Mixfix_Attrs
    { mixfixNargs :: String
    , mixfixPrio :: String
    , mixfixPretty :: String
    } deriving (Eq,Show)
data Arg = Arg
    { argPrio :: String
    } deriving (Eq,Show)
data AString = AString
    { stringVal :: String
    } deriving (Eq,Show)
data Break = Break
    { breakPrio :: String
    } deriving (Eq,Show)
data Block = Block Block_Attrs [(OneOf4 Arg AString Break Block)]
           deriving (Eq,Show)
data Block_Attrs = Block_Attrs
    { blockPrio :: String
    } deriving (Eq,Show)
newtype Proof = Proof String   deriving (Eq,Show)
data Shows = Shows Shows_Attrs (List1 AShow)
           deriving (Eq,Show)
data Shows_Attrs = Shows_Attrs
    { showsName :: String
    , showsArgs :: (Maybe String)
    } deriving (Eq,Show)
newtype AShow = AShow (List1 (OneOf6 Bound Free Var Const App Abs))   deriving (Eq,Show)
data Bound = Bound
    { boundIndex :: String
    } deriving (Eq,Show)
data Free = FreeTVar Free_Attrs TVar
          | FreeTFree Free_Attrs TFree
          | FreeType Free_Attrs Type
          deriving (Eq,Show)
data Free_Attrs = Free_Attrs
    { freeName :: String
    } deriving (Eq,Show)
data Var = VarTVar Var_Attrs TVar
         | VarTFree Var_Attrs TFree
         | VarType Var_Attrs Type
         deriving (Eq,Show)
data Var_Attrs = Var_Attrs
    { varName :: String
    , varIndex :: (Maybe String)
    } deriving (Eq,Show)
data Const = Const Const_Attrs (OneOf3 TVar TFree Type)
           deriving (Eq,Show)
data Const_Attrs = Const_Attrs
    { constName :: String
    } deriving (Eq,Show)
data App = App (OneOf6 Bound Free Var Const App Abs)
               (OneOf6 Bound Free Var Const App Abs)
         deriving (Eq,Show)
data Abs = Abs Abs_Attrs (OneOf3 TVar TFree Type)
               (OneOf6 Bound Free Var Const App Abs)
         deriving (Eq,Show)
data Abs_Attrs = Abs_Attrs
    { absVname :: String
    } deriving (Eq,Show)
data TVar = TVar TVar_Attrs [Class]
          deriving (Eq,Show)
data TVar_Attrs = TVar_Attrs
    { tVarName :: String
    , tVarIndex :: (Maybe String)
    } deriving (Eq,Show)
data TFree = TFree TFree_Attrs [Class]
           deriving (Eq,Show)
data TFree_Attrs = TFree_Attrs
    { tFreeName :: String
    } deriving (Eq,Show)
data Type = Type Type_Attrs [(OneOf3 TVar TFree Type)]
          deriving (Eq,Show)
data Type_Attrs = Type_Attrs
    { typeName :: String
    } deriving (Eq,Show)
data Class = Class
    { className :: String
    } deriving (Eq,Show)


{-Instance decls-}

instance HTypeable Export where
    toHType _ = Defined "Export" [] []
instance XmlContent Export where
    toContents (Export a) =
        [CElem (Elem (N "Export") [] (toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Export"]
        ; interior e $ return (Export) `apply` parseContents
        } `adjustErr` ("in <Export>, "++)

instance HTypeable Thy where
    toHType _ = Defined "Thy" [] []
instance XmlContent Thy where
    toContents (Thy as a b c d) =
        [CElem (Elem (N "Thy") (toAttrs as) (toContents a ++
                                             concatMap toContents b ++ concatMap toContents c ++
                                             toContents d)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Thy"]
        ; interior e $ return (Thy (fromAttrs as)) `apply` parseContents
                       `apply` many parseContents `apply` many parseContents
                       `apply` parseContents
        } `adjustErr` ("in <Thy>, "++)
instance XmlAttributes Thy_Attrs where
    fromAttrs as =
        Thy_Attrs
          { thyName = definiteA fromAttrToStr "Thy" "name" as
          , thyHeader = possibleA fromAttrToStr "header" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (thyName v)
        , maybeToAttr toAttrFrStr "header" (thyHeader v)
        ]

instance HTypeable Keyword where
    toHType _ = Defined "Keyword" [] []
instance XmlContent Keyword where
    toContents as =
        [CElem (Elem (N "Keyword") (toAttrs as) []) ()]
    parseContents = do
        { (Elem _ as []) <- element ["Keyword"]
        ; return (fromAttrs as)
        } `adjustErr` ("in <Keyword>, "++)
instance XmlAttributes Keyword where
    fromAttrs as =
        Keyword
          { keywordName = definiteA fromAttrToStr "Keyword" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (keywordName v)
        ]

instance HTypeable Import where
    toHType _ = Defined "Import" [] []
instance XmlContent Import where
    toContents as =
        [CElem (Elem (N "Import") (toAttrs as) []) ()]
    parseContents = do
        { (Elem _ as []) <- element ["Import"]
        ; return (fromAttrs as)
        } `adjustErr` ("in <Import>, "++)
instance XmlAttributes Import where
    fromAttrs as =
        Import
          { importName = definiteA fromAttrToStr "Import" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (importName v)
        ]

instance HTypeable UseFile where
    toHType _ = Defined "UseFile" [] []
instance XmlContent UseFile where
    toContents as =
        [CElem (Elem (N "UseFile") (toAttrs as) []) ()]
    parseContents = do
        { (Elem _ as []) <- element ["UseFile"]
        ; return (fromAttrs as)
        } `adjustErr` ("in <UseFile>, "++)
instance XmlAttributes UseFile where
    fromAttrs as =
        UseFile
          { useFileName = definiteA fromAttrToStr "UseFile" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (useFileName v)
        ]

instance HTypeable Body where
    toHType _ = Defined "Body" [] []
instance XmlContent Body where
    toContents (Body a) =
        [CElem (Elem (N "Body") [] (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Body"]
        ; interior e $ return (Body) `apply` many parseContents
        } `adjustErr` ("in <Body>, "++)

instance HTypeable Body_ where
    toHType _ = Defined "Body" [] []
instance XmlContent Body_ where
    toContents (Body_Locale a) = toContents a
    toContents (Body_Cls a) = toContents a
    toContents (Body_TypeSynonym a) = toContents a
    toContents (Body_Datatypes a) = toContents a
    toContents (Body_Domains a) = toContents a
    toContents (Body_Consts a) = toContents a
    toContents (Body_Axioms a) = toContents a
    toContents (Body_Lemma a) = toContents a
    toContents (Body_Definition a) = toContents a
    toContents (Body_Funs a) = toContents a
    toContents (Body_Primrec a) = toContents a
    toContents (Body_Fixrec a) = toContents a
    toContents (Body_Instantiation a) = toContents a
    toContents (Body_Instance a) = toContents a
    toContents (Body_Subclass a) = toContents a
    toContents (Body_Typedef a) = toContents a
    toContents (Body_Defs a) = toContents a
    parseContents = oneOf
        [ return (Body_Locale) `apply` parseContents
        , return (Body_Cls) `apply` parseContents
        , return (Body_TypeSynonym) `apply` parseContents
        , return (Body_Datatypes) `apply` parseContents
        , return (Body_Domains) `apply` parseContents
        , return (Body_Consts) `apply` parseContents
        , return (Body_Axioms) `apply` parseContents
        , return (Body_Lemma) `apply` parseContents
        , return (Body_Definition) `apply` parseContents
        , return (Body_Funs) `apply` parseContents
        , return (Body_Primrec) `apply` parseContents
        , return (Body_Fixrec) `apply` parseContents
        , return (Body_Instantiation) `apply` parseContents
        , return (Body_Instance) `apply` parseContents
        , return (Body_Subclass) `apply` parseContents
        , return (Body_Typedef) `apply` parseContents
        , return (Body_Defs) `apply` parseContents
        ] `adjustErr` ("in <Body>, "++)

instance HTypeable Locale where
    toHType _ = Defined "Locale" [] []
instance XmlContent Locale where
    toContents (Locale as a b c) =
        [CElem (Elem (N "Locale") (toAttrs as) (toContents a ++
                                                concatMap toContents b ++ toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Locale"]
        ; interior e $ return (Locale (fromAttrs as)) `apply` parseContents
                       `apply` many parseContents `apply` parseContents
        } `adjustErr` ("in <Locale>, "++)
instance XmlAttributes Locale_Attrs where
    fromAttrs as =
        Locale_Attrs
          { localeName = definiteA fromAttrToStr "Locale" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (localeName v)
        ]

instance HTypeable Cls where
    toHType _ = Defined "Cls" [] []
instance XmlContent Cls where
    toContents (Cls as a b c) =
        [CElem (Elem (N "Cls") (toAttrs as) (toContents a ++
                                             concatMap toContents b ++ toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Cls"]
        ; interior e $ return (Cls (fromAttrs as)) `apply` parseContents
                       `apply` many parseContents `apply` parseContents
        } `adjustErr` ("in <Cls>, "++)
instance XmlAttributes Cls_Attrs where
    fromAttrs as =
        Cls_Attrs
          { clsName = definiteA fromAttrToStr "Cls" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (clsName v)
        ]

instance HTypeable TypeSynonym where
    toHType _ = Defined "TypeSynonym" [] []
instance XmlContent TypeSynonym where
    toContents (TypeSynonym as a b c) =
        [CElem (Elem (N "TypeSynonym") (toAttrs as) (maybe [] toContents a
                                                     ++ toContents b ++ toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["TypeSynonym"]
        ; interior e $ return (TypeSynonym (fromAttrs as))
                       `apply` optional parseContents `apply` parseContents
                       `apply` parseContents
        } `adjustErr` ("in <TypeSynonym>, "++)
instance XmlAttributes TypeSynonym_Attrs where
    fromAttrs as =
        TypeSynonym_Attrs
          { typeSynonymName = definiteA fromAttrToStr "TypeSynonym" "name" as
          , typeSynonymTarget = possibleA fromAttrToStr "target" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (typeSynonymName v)
        , maybeToAttr toAttrFrStr "target" (typeSynonymTarget v)
        ]

instance HTypeable Datatypes where
    toHType _ = Defined "Datatypes" [] []
instance XmlContent Datatypes where
    toContents (Datatypes a) =
        [CElem (Elem (N "Datatypes") [] (toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Datatypes"]
        ; interior e $ return (Datatypes) `apply` parseContents
        } `adjustErr` ("in <Datatypes>, "++)

instance HTypeable Datatype where
    toHType _ = Defined "Datatype" [] []
instance XmlContent Datatype where
    toContents (Datatype as a b c) =
        [CElem (Elem (N "Datatype") (toAttrs as) (maybe [] toContents a ++
                                                  toContents b ++ concatMap toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Datatype"]
        ; interior e $ return (Datatype (fromAttrs as))
                       `apply` optional parseContents `apply` parseContents
                       `apply` many parseContents
        } `adjustErr` ("in <Datatype>, "++)
instance XmlAttributes Datatype_Attrs where
    fromAttrs as =
        Datatype_Attrs
          { datatypeName = definiteA fromAttrToStr "Datatype" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (datatypeName v)
        ]

instance HTypeable Constructor where
    toHType _ = Defined "Constructor" [] []
instance XmlContent Constructor where
    toContents (Constructor as a b c) =
        [CElem (Elem (N "Constructor") (toAttrs as) (maybe [] toContents a
                                                     ++ toContents b ++ concatMap toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Constructor"]
        ; interior e $ return (Constructor (fromAttrs as))
                       `apply` optional parseContents `apply` parseContents
                       `apply` many parseContents
        } `adjustErr` ("in <Constructor>, "++)
instance XmlAttributes Constructor_Attrs where
    fromAttrs as =
        Constructor_Attrs
          { constructorName = possibleA fromAttrToStr "name" as
          }
    toAttrs v = catMaybes 
        [ maybeToAttr toAttrFrStr "name" (constructorName v)
        ]

instance HTypeable Domains where
    toHType _ = Defined "Domains" [] []
instance XmlContent Domains where
    toContents (Domains a) =
        [CElem (Elem (N "Domains") [] (toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Domains"]
        ; interior e $ return (Domains) `apply` parseContents
        } `adjustErr` ("in <Domains>, "++)

instance HTypeable Domain where
    toHType _ = Defined "Domain" [] []
instance XmlContent Domain where
    toContents (Domain as a b c) =
        [CElem (Elem (N "Domain") (toAttrs as) (maybe [] toContents a ++
                                                concatMap toContents b ++ toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Domain"]
        ; interior e $ return (Domain (fromAttrs as))
                       `apply` optional parseContents `apply` many parseContents
                       `apply` parseContents
        } `adjustErr` ("in <Domain>, "++)
instance XmlAttributes Domain_Attrs where
    fromAttrs as =
        Domain_Attrs
          { domainName = definiteA fromAttrToStr "Domain" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (domainName v)
        ]

instance HTypeable DomainConstructor where
    toHType _ = Defined "DomainConstructor" [] []
instance XmlContent DomainConstructor where
    toContents (DomainConstructor as a b) =
        [CElem (Elem (N "DomainConstructor") (toAttrs as) (toContents a ++
                                                           concatMap toContents b)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["DomainConstructor"]
        ; interior e $ return (DomainConstructor (fromAttrs as))
                       `apply` parseContents `apply` many parseContents
        } `adjustErr` ("in <DomainConstructor>, "++)
instance XmlAttributes DomainConstructor_Attrs where
    fromAttrs as =
        DomainConstructor_Attrs
          { domainConstructorName = definiteA fromAttrToStr "DomainConstructor" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (domainConstructorName v)
        ]

instance HTypeable DomainConstructorArg where
    toHType _ = Defined "DomainConstructorArg" [] []
instance XmlContent DomainConstructorArg where
    toContents (DomainConstructorArg as a) =
        [CElem (Elem (N "DomainConstructorArg") (toAttrs as) (toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["DomainConstructorArg"]
        ; interior e $ return (DomainConstructorArg (fromAttrs as))
                       `apply` parseContents
        } `adjustErr` ("in <DomainConstructorArg>, "++)
instance XmlAttributes DomainConstructorArg_Attrs where
    fromAttrs as =
        DomainConstructorArg_Attrs
          { domainConstructorArgLazy = possibleA fromAttrToStr "lazy" as
          , domainConstructorArgName = possibleA fromAttrToStr "name" as
          }
    toAttrs v = catMaybes 
        [ maybeToAttr toAttrFrStr "lazy" (domainConstructorArgLazy v)
        , maybeToAttr toAttrFrStr "name" (domainConstructorArgName v)
        ]

instance HTypeable Consts where
    toHType _ = Defined "Consts" [] []
instance XmlContent Consts where
    toContents (Consts a) =
        [CElem (Elem (N "Consts") [] (toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Consts"]
        ; interior e $ return (Consts) `apply` parseContents
        } `adjustErr` ("in <Consts>, "++)

instance HTypeable ConstDef where
    toHType _ = Defined "ConstDef" [] []
instance XmlContent ConstDef where
    toContents (ConstDef as a b) =
        [CElem (Elem (N "ConstDef") (toAttrs as) (maybe [] toContents a ++
                                                  toContents b)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["ConstDef"]
        ; interior e $ return (ConstDef (fromAttrs as))
                       `apply` optional parseContents `apply` parseContents
        } `adjustErr` ("in <ConstDef>, "++)
instance XmlAttributes ConstDef_Attrs where
    fromAttrs as =
        ConstDef_Attrs
          { constDefName = definiteA fromAttrToStr "ConstDef" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (constDefName v)
        ]

instance HTypeable Axioms where
    toHType _ = Defined "Axioms" [] []
instance XmlContent Axioms where
    toContents (Axioms a) =
        [CElem (Elem (N "Axioms") [] (toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Axioms"]
        ; interior e $ return (Axioms) `apply` parseContents
        } `adjustErr` ("in <Axioms>, "++)

instance HTypeable Axiom where
    toHType _ = Defined "Axiom" [] []
instance XmlContent Axiom where
    toContents (Axiom as a) =
        [CElem (Elem (N "Axiom") (toAttrs as) (toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Axiom"]
        ; interior e $ return (Axiom (fromAttrs as)) `apply` parseContents
        } `adjustErr` ("in <Axiom>, "++)
instance XmlAttributes Axiom_Attrs where
    fromAttrs as =
        Axiom_Attrs
          { axiomName = definiteA fromAttrToStr "Axiom" "name" as
          , axiomArgs = definiteA fromAttrToStr "Axiom" "args" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (axiomName v)
        , toAttrFrStr "args" (axiomArgs v)
        ]

instance HTypeable Lemma where
    toHType _ = Defined "Lemma" [] []
instance XmlContent Lemma where
    toContents (Lemma as a b c) =
        [CElem (Elem (N "Lemma") (toAttrs as) (toContents a ++ toContents b
                                               ++ toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Lemma"]
        ; interior e $ return (Lemma (fromAttrs as)) `apply` parseContents
                       `apply` parseContents `apply` parseContents
        } `adjustErr` ("in <Lemma>, "++)
instance XmlAttributes Lemma_Attrs where
    fromAttrs as =
        Lemma_Attrs
          { lemmaTarget = possibleA fromAttrToStr "target" as
          }
    toAttrs v = catMaybes 
        [ maybeToAttr toAttrFrStr "target" (lemmaTarget v)
        ]

instance HTypeable Definition where
    toHType _ = Defined "Definition" [] []
instance XmlContent Definition where
    toContents (Definition as a b c) =
        [CElem (Elem (N "Definition") (toAttrs as) (maybe [] toContents a
                                                    ++ toContents b ++ toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Definition"]
        ; interior e $ return (Definition (fromAttrs as))
                       `apply` optional parseContents `apply` parseContents
                       `apply` parseContents
        } `adjustErr` ("in <Definition>, "++)
instance XmlAttributes Definition_Attrs where
    fromAttrs as =
        Definition_Attrs
          { definitionName = definiteA fromAttrToStr "Definition" "name" as
          , definitionTarget = possibleA fromAttrToStr "target" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (definitionName v)
        , maybeToAttr toAttrFrStr "target" (definitionTarget v)
        ]

instance HTypeable Funs where
    toHType _ = Defined "Funs" [] []
instance XmlContent Funs where
    toContents (Funs as a) =
        [CElem (Elem (N "Funs") (toAttrs as) (toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Funs"]
        ; interior e $ return (Funs (fromAttrs as)) `apply` parseContents
        } `adjustErr` ("in <Funs>, "++)
instance XmlAttributes Funs_Attrs where
    fromAttrs as =
        Funs_Attrs
          { funsTarget = possibleA fromAttrToStr "target" as
          , funsSequential = possibleA fromAttrToStr "sequential" as
          , funsDefault = possibleA fromAttrToStr "default" as
          , funsDomintros = possibleA fromAttrToStr "domintros" as
          , funsPartials = possibleA fromAttrToStr "partials" as
          }
    toAttrs v = catMaybes 
        [ maybeToAttr toAttrFrStr "target" (funsTarget v)
        , maybeToAttr toAttrFrStr "sequential" (funsSequential v)
        , maybeToAttr toAttrFrStr "default" (funsDefault v)
        , maybeToAttr toAttrFrStr "domintros" (funsDomintros v)
        , maybeToAttr toAttrFrStr "partials" (funsPartials v)
        ]

instance HTypeable Fun where
    toHType _ = Defined "Fun" [] []
instance XmlContent Fun where
    toContents (Fun as a b c) =
        [CElem (Elem (N "Fun") (toAttrs as) (maybe [] toContents a ++
                                             toContents b ++ toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Fun"]
        ; interior e $ return (Fun (fromAttrs as))
                       `apply` optional parseContents `apply` parseContents
                       `apply` parseContents
        } `adjustErr` ("in <Fun>, "++)
instance XmlAttributes Fun_Attrs where
    fromAttrs as =
        Fun_Attrs
          { funName = definiteA fromAttrToStr "Fun" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (funName v)
        ]

instance HTypeable Equation where
    toHType _ = Defined "Equation" [] []
instance XmlContent Equation where
    toContents (Equation a) =
        [CElem (Elem (N "Equation") [] (toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Equation"]
        ; interior e $ return (Equation) `apply` parseContents
        } `adjustErr` ("in <Equation>, "++)

instance HTypeable Primrec where
    toHType _ = Defined "Primrec" [] []
instance XmlContent Primrec where
    toContents (Primrec as a) =
        [CElem (Elem (N "Primrec") (toAttrs as) (toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Primrec"]
        ; interior e $ return (Primrec (fromAttrs as))
                       `apply` parseContents
        } `adjustErr` ("in <Primrec>, "++)
instance XmlAttributes Primrec_Attrs where
    fromAttrs as =
        Primrec_Attrs
          { primrecTarget = possibleA fromAttrToStr "target" as
          }
    toAttrs v = catMaybes 
        [ maybeToAttr toAttrFrStr "target" (primrecTarget v)
        ]

instance HTypeable Fixrec where
    toHType _ = Defined "Fixrec" [] []
instance XmlContent Fixrec where
    toContents (Fixrec a) =
        [CElem (Elem (N "Fixrec") [] (toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Fixrec"]
        ; interior e $ return (Fixrec) `apply` parseContents
        } `adjustErr` ("in <Fixrec>, "++)

instance HTypeable FixrecFun where
    toHType _ = Defined "FixrecFun" [] []
instance XmlContent FixrecFun where
    toContents (FixrecFun as a b c) =
        [CElem (Elem (N "FixrecFun") (toAttrs as) (maybe [] toContents a ++
                                                   toContents b ++ toContents c)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["FixrecFun"]
        ; interior e $ return (FixrecFun (fromAttrs as))
                       `apply` optional parseContents `apply` parseContents
                       `apply` parseContents
        } `adjustErr` ("in <FixrecFun>, "++)
instance XmlAttributes FixrecFun_Attrs where
    fromAttrs as =
        FixrecFun_Attrs
          { fixrecFunName = definiteA fromAttrToStr "FixrecFun" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (fixrecFunName v)
        ]

instance HTypeable FixrecEquation where
    toHType _ = Defined "FixrecEquation" [] []
instance XmlContent FixrecEquation where
    toContents (FixrecEquation as a b) =
        [CElem (Elem (N "FixrecEquation") (toAttrs as) (toContents a ++
                                                        toContents b)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["FixrecEquation"]
        ; interior e $ return (FixrecEquation (fromAttrs as))
                       `apply` parseContents `apply` parseContents
        } `adjustErr` ("in <FixrecEquation>, "++)
instance XmlAttributes FixrecEquation_Attrs where
    fromAttrs as =
        FixrecEquation_Attrs
          { fixrecEquationUnchecked = possibleA fromAttrToStr "unchecked" as
          }
    toAttrs v = catMaybes 
        [ maybeToAttr toAttrFrStr "unchecked" (fixrecEquationUnchecked v)
        ]

instance HTypeable Premises where
    toHType _ = Defined "Premises" [] []
instance XmlContent Premises where
    toContents (Premises a) =
        [CElem (Elem (N "Premises") [] (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Premises"]
        ; interior e $ return (Premises) `apply` many parseContents
        } `adjustErr` ("in <Premises>, "++)

instance HTypeable Instantiation where
    toHType _ = Defined "Instantiation" [] []
instance XmlContent Instantiation where
    toContents (Instantiation as a b) =
        [CElem (Elem (N "Instantiation") (toAttrs as) (toContents a ++
                                                       toContents b)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Instantiation"]
        ; interior e $ return (Instantiation (fromAttrs as))
                       `apply` parseContents `apply` parseContents
        } `adjustErr` ("in <Instantiation>, "++)
instance XmlAttributes Instantiation_Attrs where
    fromAttrs as =
        Instantiation_Attrs
          { instantiationType = definiteA fromAttrToStr "Instantiation" "type" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "type" (instantiationType v)
        ]

instance HTypeable Instance where
    toHType _ = Defined "Instance" [] []
instance XmlContent Instance where
    toContents (Instance as a b) =
        [CElem (Elem (N "Instance") (toAttrs as) (toContents a ++
                                                  maybe [] toContents b)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Instance"]
        ; interior e $ return (Instance (fromAttrs as))
                       `apply` parseContents `apply` optional parseContents
        } `adjustErr` ("in <Instance>, "++)
instance XmlAttributes Instance_Attrs where
    fromAttrs as =
        Instance_Attrs
          { instanceClass = possibleA fromAttrToStr "class" as
          , instanceRel = possibleA fromAttrToStr "rel" as
          , instanceClass1 = possibleA fromAttrToStr "class1" as
          }
    toAttrs v = catMaybes 
        [ maybeToAttr toAttrFrStr "class" (instanceClass v)
        , maybeToAttr toAttrFrStr "rel" (instanceRel v)
        , maybeToAttr toAttrFrStr "class1" (instanceClass1 v)
        ]

instance HTypeable Subclass where
    toHType _ = Defined "Subclass" [] []
instance XmlContent Subclass where
    toContents (Subclass as a) =
        [CElem (Elem (N "Subclass") (toAttrs as) (toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Subclass"]
        ; interior e $ return (Subclass (fromAttrs as))
                       `apply` parseContents
        } `adjustErr` ("in <Subclass>, "++)
instance XmlAttributes Subclass_Attrs where
    fromAttrs as =
        Subclass_Attrs
          { subclassClass = definiteA fromAttrToStr "Subclass" "class" as
          , subclassTarget = possibleA fromAttrToStr "target" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "class" (subclassClass v)
        , maybeToAttr toAttrFrStr "target" (subclassTarget v)
        ]

instance HTypeable Typedef where
    toHType _ = Defined "Typedef" [] []
instance XmlContent Typedef where
    toContents (Typedef as a b c d) =
        [CElem (Elem (N "Typedef") (toAttrs as) (maybe [] toContents a ++
                                                 toContents b ++ toContents c ++
                                                 concatMap toContents d)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Typedef"]
        ; interior e $ return (Typedef (fromAttrs as))
                       `apply` optional parseContents `apply` parseContents
                       `apply` parseContents `apply` many parseContents
        } `adjustErr` ("in <Typedef>, "++)
instance XmlAttributes Typedef_Attrs where
    fromAttrs as =
        Typedef_Attrs
          { typedefType = definiteA fromAttrToStr "Typedef" "type" as
          , typedefM1 = possibleA fromAttrToStr "m1" as
          , typedefM2 = possibleA fromAttrToStr "m2" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "type" (typedefType v)
        , maybeToAttr toAttrFrStr "m1" (typedefM1 v)
        , maybeToAttr toAttrFrStr "m2" (typedefM2 v)
        ]

instance HTypeable Defs where
    toHType _ = Defined "Defs" [] []
instance XmlContent Defs where
    toContents (Defs as a) =
        [CElem (Elem (N "Defs") (toAttrs as) (toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Defs"]
        ; interior e $ return (Defs (fromAttrs as)) `apply` parseContents
        } `adjustErr` ("in <Defs>, "++)
instance XmlAttributes Defs_Attrs where
    fromAttrs as =
        Defs_Attrs
          { defsUnchecked = possibleA fromAttrToStr "unchecked" as
          , defsOverloaded = possibleA fromAttrToStr "overloaded" as
          }
    toAttrs v = catMaybes 
        [ maybeToAttr toAttrFrStr "unchecked" (defsUnchecked v)
        , maybeToAttr toAttrFrStr "overloaded" (defsOverloaded v)
        ]

instance HTypeable Def where
    toHType _ = Defined "Def" [] []
instance XmlContent Def where
    toContents (Def as a b) =
        [CElem (Elem (N "Def") (toAttrs as) (toContents a ++
                                             toContents b)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Def"]
        ; interior e $ return (Def (fromAttrs as)) `apply` parseContents
                       `apply` parseContents
        } `adjustErr` ("in <Def>, "++)
instance XmlAttributes Def_Attrs where
    fromAttrs as =
        Def_Attrs
          { defName = definiteA fromAttrToStr "Def" "name" as
          , defArgs = definiteA fromAttrToStr "Def" "args" as
          , defConst = definiteA fromAttrToStr "Def" "const" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (defName v)
        , toAttrFrStr "args" (defArgs v)
        , toAttrFrStr "const" (defConst v)
        ]

instance HTypeable Sort where
    toHType _ = Defined "Sort" [] []
instance XmlContent Sort where
    toContents (Sort a) =
        [CElem (Elem (N "Sort") [] (toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Sort"]
        ; interior e $ return (Sort) `apply` parseContents
        } `adjustErr` ("in <Sort>, "++)

instance HTypeable Arity where
    toHType _ = Defined "Arity" [] []
instance XmlContent Arity where
    toContents (Arity a b) =
        [CElem (Elem (N "Arity") [] (toContents a ++
                                     concatMap toContents b)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Arity"]
        ; interior e $ return (Arity) `apply` parseContents
                       `apply` many parseContents
        } `adjustErr` ("in <Arity>, "++)

instance HTypeable Vars where
    toHType _ = Defined "Vars" [] []
instance XmlContent Vars where
    toContents (Vars a) =
        [CElem (Elem (N "Vars") [] (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Vars"]
        ; interior e $ return (Vars) `apply` many parseContents
        } `adjustErr` ("in <Vars>, "++)

instance HTypeable Parent where
    toHType _ = Defined "Parent" [] []
instance XmlContent Parent where
    toContents as =
        [CElem (Elem (N "Parent") (toAttrs as) []) ()]
    parseContents = do
        { (Elem _ as []) <- element ["Parent"]
        ; return (fromAttrs as)
        } `adjustErr` ("in <Parent>, "++)
instance XmlAttributes Parent where
    fromAttrs as =
        Parent
          { parentName = definiteA fromAttrToStr "Parent" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (parentName v)
        ]

instance HTypeable Fixes where
    toHType _ = Defined "Fixes" [] []
instance XmlContent Fixes where
    toContents (Fixes a) =
        [CElem (Elem (N "Fixes") [] (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Fixes"]
        ; interior e $ return (Fixes) `apply` many parseContents
        } `adjustErr` ("in <Fixes>, "++)

instance HTypeable Fix where
    toHType _ = Defined "Fix" [] []
instance XmlContent Fix where
    toContents (Fix as a b) =
        [CElem (Elem (N "Fix") (toAttrs as) (toContents a ++
                                             maybe [] toContents b)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Fix"]
        ; interior e $ return (Fix (fromAttrs as)) `apply` parseContents
                       `apply` optional parseContents
        } `adjustErr` ("in <Fix>, "++)
instance XmlAttributes Fix_Attrs where
    fromAttrs as =
        Fix_Attrs
          { fixName = definiteA fromAttrToStr "Fix" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (fixName v)
        ]

instance HTypeable Assumes where
    toHType _ = Defined "Assumes" [] []
instance XmlContent Assumes where
    toContents (Assumes a) =
        [CElem (Elem (N "Assumes") [] (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Assumes"]
        ; interior e $ return (Assumes) `apply` many parseContents
        } `adjustErr` ("in <Assumes>, "++)

instance HTypeable Assumption where
    toHType _ = Defined "Assumption" [] []
instance XmlContent Assumption where
    toContents (Assumption as a) =
        [CElem (Elem (N "Assumption") (toAttrs as) (toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Assumption"]
        ; interior e $ return (Assumption (fromAttrs as))
                       `apply` parseContents
        } `adjustErr` ("in <Assumption>, "++)
instance XmlAttributes Assumption_Attrs where
    fromAttrs as =
        Assumption_Attrs
          { assumptionName = definiteA fromAttrToStr "Assumption" "name" as
          , assumptionArgs = definiteA fromAttrToStr "Assumption" "args" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (assumptionName v)
        , toAttrFrStr "args" (assumptionArgs v)
        ]

instance HTypeable Ctxt where
    toHType _ = Defined "Ctxt" [] []
instance XmlContent Ctxt where
    toContents (Ctxt a) =
        [CElem (Elem (N "Ctxt") [] (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Ctxt"]
        ; interior e $ return (Ctxt) `apply` many parseContents
        } `adjustErr` ("in <Ctxt>, "++)

instance HTypeable Mixfix where
    toHType _ = Defined "Mixfix" [] []
instance XmlContent Mixfix where
    toContents (Mixfix as a) =
        [CElem (Elem (N "Mixfix") (toAttrs as) (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Mixfix"]
        ; interior e $ return (Mixfix (fromAttrs as))
                       `apply` many parseContents
        } `adjustErr` ("in <Mixfix>, "++)
instance XmlAttributes Mixfix_Attrs where
    fromAttrs as =
        Mixfix_Attrs
          { mixfixNargs = definiteA fromAttrToStr "Mixfix" "nargs" as
          , mixfixPrio = definiteA fromAttrToStr "Mixfix" "prio" as
          , mixfixPretty = definiteA fromAttrToStr "Mixfix" "pretty" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "nargs" (mixfixNargs v)
        , toAttrFrStr "prio" (mixfixPrio v)
        , toAttrFrStr "pretty" (mixfixPretty v)
        ]

instance HTypeable Arg where
    toHType _ = Defined "Arg" [] []
instance XmlContent Arg where
    toContents as =
        [CElem (Elem (N "Arg") (toAttrs as) []) ()]
    parseContents = do
        { (Elem _ as []) <- element ["Arg"]
        ; return (fromAttrs as)
        } `adjustErr` ("in <Arg>, "++)
instance XmlAttributes Arg where
    fromAttrs as =
        Arg
          { argPrio = definiteA fromAttrToStr "Arg" "prio" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "prio" (argPrio v)
        ]

instance HTypeable AString where
    toHType _ = Defined "String" [] []
instance XmlContent AString where
    toContents as =
        [CElem (Elem (N "String") (toAttrs as) []) ()]
    parseContents = do
        { (Elem _ as []) <- element ["String"]
        ; return (fromAttrs as)
        } `adjustErr` ("in <String>, "++)
instance XmlAttributes AString where
    fromAttrs as =
        AString
          { stringVal = definiteA fromAttrToStr "String" "val" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "val" (stringVal v)
        ]

instance HTypeable Break where
    toHType _ = Defined "Break" [] []
instance XmlContent Break where
    toContents as =
        [CElem (Elem (N "Break") (toAttrs as) []) ()]
    parseContents = do
        { (Elem _ as []) <- element ["Break"]
        ; return (fromAttrs as)
        } `adjustErr` ("in <Break>, "++)
instance XmlAttributes Break where
    fromAttrs as =
        Break
          { breakPrio = definiteA fromAttrToStr "Break" "prio" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "prio" (breakPrio v)
        ]

instance HTypeable Block where
    toHType _ = Defined "Block" [] []
instance XmlContent Block where
    toContents (Block as a) =
        [CElem (Elem (N "Block") (toAttrs as) (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Block"]
        ; interior e $ return (Block (fromAttrs as))
                       `apply` many parseContents
        } `adjustErr` ("in <Block>, "++)
instance XmlAttributes Block_Attrs where
    fromAttrs as =
        Block_Attrs
          { blockPrio = definiteA fromAttrToStr "Block" "prio" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "prio" (blockPrio v)
        ]

instance HTypeable Proof where
    toHType _ = Defined "Proof" [] []
instance XmlContent Proof where
    toContents (Proof a) =
        [CElem (Elem (N "Proof") [] (toText a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Proof"]
        ; interior e $ return (Proof) `apply` (text `onFail` return "")
        } `adjustErr` ("in <Proof>, "++)

instance HTypeable Shows where
    toHType _ = Defined "Shows" [] []
instance XmlContent Shows where
    toContents (Shows as a) =
        [CElem (Elem (N "Shows") (toAttrs as) (toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Shows"]
        ; interior e $ return (Shows (fromAttrs as)) `apply` parseContents
        } `adjustErr` ("in <Shows>, "++)
instance XmlAttributes Shows_Attrs where
    fromAttrs as =
        Shows_Attrs
          { showsName = definiteA fromAttrToStr "Shows" "name" as
          , showsArgs = possibleA fromAttrToStr "args" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (showsName v)
        , maybeToAttr toAttrFrStr "args" (showsArgs v)
        ]

instance HTypeable AShow where
    toHType _ = Defined "Show" [] []
instance XmlContent AShow where
    toContents (AShow a) =
        [CElem (Elem (N "Show") [] (toContents a)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["Show"]
        ; interior e $ return (AShow) `apply` parseContents
        } `adjustErr` ("in <Show>, "++)

instance HTypeable Bound where
    toHType _ = Defined "Bound" [] []
instance XmlContent Bound where
    toContents as =
        [CElem (Elem (N "Bound") (toAttrs as) []) ()]
    parseContents = do
        { (Elem _ as []) <- element ["Bound"]
        ; return (fromAttrs as)
        } `adjustErr` ("in <Bound>, "++)
instance XmlAttributes Bound where
    fromAttrs as =
        Bound
          { boundIndex = definiteA fromAttrToStr "Bound" "index" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "index" (boundIndex v)
        ]

instance HTypeable Free where
    toHType _ = Defined "Free" [] []
instance XmlContent Free where
    toContents (FreeTVar as a) =
        [CElem (Elem (N "Free") (toAttrs as) (toContents a) ) ()]
    toContents (FreeTFree as a) =
        [CElem (Elem (N "Free") (toAttrs as) (toContents a) ) ()]
    toContents (FreeType as a) =
        [CElem (Elem (N "Free") (toAttrs as) (toContents a) ) ()]
    parseContents = do 
        { e@(Elem _ as _) <- element ["Free"]
        ; interior e $ oneOf
            [ return (FreeTVar (fromAttrs as)) `apply` parseContents
            , return (FreeTFree (fromAttrs as)) `apply` parseContents
            , return (FreeType (fromAttrs as)) `apply` parseContents
            ] `adjustErr` ("in <Free>, "++)
        }
instance XmlAttributes Free_Attrs where
    fromAttrs as =
        Free_Attrs
          { freeName = definiteA fromAttrToStr "Free" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (freeName v)
        ]

instance HTypeable Var where
    toHType _ = Defined "Var" [] []
instance XmlContent Var where
    toContents (VarTVar as a) =
        [CElem (Elem (N "Var") (toAttrs as) (toContents a) ) ()]
    toContents (VarTFree as a) =
        [CElem (Elem (N "Var") (toAttrs as) (toContents a) ) ()]
    toContents (VarType as a) =
        [CElem (Elem (N "Var") (toAttrs as) (toContents a) ) ()]
    parseContents = do 
        { e@(Elem _ as _) <- element ["Var"]
        ; interior e $ oneOf
            [ return (VarTVar (fromAttrs as)) `apply` parseContents
            , return (VarTFree (fromAttrs as)) `apply` parseContents
            , return (VarType (fromAttrs as)) `apply` parseContents
            ] `adjustErr` ("in <Var>, "++)
        }
instance XmlAttributes Var_Attrs where
    fromAttrs as =
        Var_Attrs
          { varName = definiteA fromAttrToStr "Var" "name" as
          , varIndex = possibleA fromAttrToStr "index" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (varName v)
        , maybeToAttr toAttrFrStr "index" (varIndex v)
        ]

instance HTypeable Const where
    toHType _ = Defined "Const" [] []
instance XmlContent Const where
    toContents (Const as a) =
        [CElem (Elem (N "Const") (toAttrs as) (toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Const"]
        ; interior e $ return (Const (fromAttrs as)) `apply` parseContents
        } `adjustErr` ("in <Const>, "++)
instance XmlAttributes Const_Attrs where
    fromAttrs as =
        Const_Attrs
          { constName = definiteA fromAttrToStr "Const" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (constName v)
        ]

instance HTypeable App where
    toHType _ = Defined "App" [] []
instance XmlContent App where
    toContents (App a b) =
        [CElem (Elem (N "App") [] (toContents a ++ toContents b)) ()]
    parseContents = do
        { e@(Elem _ [] _) <- element ["App"]
        ; interior e $ return (App) `apply` parseContents
                       `apply` parseContents
        } `adjustErr` ("in <App>, "++)

instance HTypeable Abs where
    toHType _ = Defined "Abs" [] []
instance XmlContent Abs where
    toContents (Abs as a b) =
        [CElem (Elem (N "Abs") (toAttrs as) (toContents a ++
                                             toContents b)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Abs"]
        ; interior e $ return (Abs (fromAttrs as)) `apply` parseContents
                       `apply` parseContents
        } `adjustErr` ("in <Abs>, "++)
instance XmlAttributes Abs_Attrs where
    fromAttrs as =
        Abs_Attrs
          { absVname = definiteA fromAttrToStr "Abs" "vname" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "vname" (absVname v)
        ]

instance HTypeable TVar where
    toHType _ = Defined "TVar" [] []
instance XmlContent TVar where
    toContents (TVar as a) =
        [CElem (Elem (N "TVar") (toAttrs as) (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["TVar"]
        ; interior e $ return (TVar (fromAttrs as))
                       `apply` many parseContents
        } `adjustErr` ("in <TVar>, "++)
instance XmlAttributes TVar_Attrs where
    fromAttrs as =
        TVar_Attrs
          { tVarName = definiteA fromAttrToStr "TVar" "name" as
          , tVarIndex = possibleA fromAttrToStr "index" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (tVarName v)
        , maybeToAttr toAttrFrStr "index" (tVarIndex v)
        ]

instance HTypeable TFree where
    toHType _ = Defined "TFree" [] []
instance XmlContent TFree where
    toContents (TFree as a) =
        [CElem (Elem (N "TFree") (toAttrs as) (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["TFree"]
        ; interior e $ return (TFree (fromAttrs as))
                       `apply` many parseContents
        } `adjustErr` ("in <TFree>, "++)
instance XmlAttributes TFree_Attrs where
    fromAttrs as =
        TFree_Attrs
          { tFreeName = definiteA fromAttrToStr "TFree" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (tFreeName v)
        ]

instance HTypeable Type where
    toHType _ = Defined "Type" [] []
instance XmlContent Type where
    toContents (Type as a) =
        [CElem (Elem (N "Type") (toAttrs as) (concatMap toContents a)) ()]
    parseContents = do
        { e@(Elem _ as _) <- element ["Type"]
        ; interior e $ return (Type (fromAttrs as))
                       `apply` many parseContents
        } `adjustErr` ("in <Type>, "++)
instance XmlAttributes Type_Attrs where
    fromAttrs as =
        Type_Attrs
          { typeName = definiteA fromAttrToStr "Type" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (typeName v)
        ]

instance HTypeable Class where
    toHType _ = Defined "class" [] []
instance XmlContent Class where
    toContents as =
        [CElem (Elem (N "class") (toAttrs as) []) ()]
    parseContents = do
        { (Elem _ as []) <- element ["class"]
        ; return (fromAttrs as)
        } `adjustErr` ("in <class>, "++)
instance XmlAttributes Class where
    fromAttrs as =
        Class
          { className = definiteA fromAttrToStr "class" "name" as
          }
    toAttrs v = catMaybes 
        [ toAttrFrStr "name" (className v)
        ]



{-Done-}
