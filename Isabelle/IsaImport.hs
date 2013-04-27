module Isabelle.IsaImport where

import Text.XML.HaXml.OneOfN
import Text.XML.HaXml.XmlContent (fReadXml)
import Isabelle.IsaExport
import qualified Isabelle.IsaSign as IsaSign
import qualified Isabelle.IsaConsts as IsaConsts
import Data.Maybe (fromMaybe)

importIsaDataIO :: String ->
 IO [(String,[String],[(String,IsaSign.Typ)],
     [(String,IsaSign.Term)], [(String,IsaSign.Term)],
     IsaSign.DomainTab, [(String,IsaSign.FunDef)],
     [(IsaSign.IsaClass,IsaSign.ClassDecl)],
     [(String,IsaSign.LocaleDecl)])]
importIsaDataIO p = do
 IsaExport d' <- fReadXml p
 return $ importIsaData d'

importIsaData :: [IsaTheory] ->
 [(String,[String],[(String,IsaSign.Typ)],
  [(String,IsaSign.Term)], [(String,IsaSign.Term)],
  IsaSign.DomainTab, [(String,IsaSign.FunDef)],
  [(IsaSign.IsaClass,IsaSign.ClassDecl)],
  [(String,IsaSign.LocaleDecl)])]
importIsaData = map (\(IsaTheory attrs imports axioms theorems consts
                               datatypes funs classes locales) ->
 let imports'   = map importName imports
     consts'    = map hXmlConst2IsaConst consts
     axioms'    = map hXmlAxiom2IsaAxiom axioms
     theorems'  = map hXmlTheorem2IsaTheorem theorems
     datatypes' = map hXmlRecDataType2IsaRecDataType datatypes
     funs'      = map hXmlFunction2IsaFunDef funs
     classes'   = map hXmlClass2IsaClassDecl classes
     locales'   = map hXmlLocale2IsaLocaleDecl locales
 in (isaTheoryName attrs,imports',consts',
     axioms',theorems',datatypes',funs',classes',locales'))

hXmlConst2IsaConst :: Const -> (String,IsaSign.Typ)
hXmlConst2IsaConst (ConstTVar  a v) =
 (constName a, hXmlOneOf3_2IsaTyp $ OneOf3 v)
hXmlConst2IsaConst (ConstTFree a f) =
 (constName a, hXmlOneOf3_2IsaTyp $ TwoOf3 f)
hXmlConst2IsaConst (ConstType  a t) =
 (constName a, hXmlOneOf3_2IsaTyp $ ThreeOf3 t)

hXmlAxiom2IsaAxiom :: Axiom -> (String,IsaSign.Term)
hXmlAxiom2IsaAxiom (AxiomBound a b) =
 (axiomName a, hXmlOneOf6_2IsaTerm [] $ OneOf6 b)
hXmlAxiom2IsaAxiom (AxiomFree a f)  =
 (axiomName a, hXmlOneOf6_2IsaTerm [] $ TwoOf6 f)
hXmlAxiom2IsaAxiom (AxiomVar a v)   =
 (axiomName a, hXmlOneOf6_2IsaTerm [] $ ThreeOf6 v)
hXmlAxiom2IsaAxiom (AxiomConst a c) =
 (axiomName a, hXmlOneOf6_2IsaTerm [] $ FourOf6 c)
hXmlAxiom2IsaAxiom (AxiomApp a ap)  =
 (axiomName a, hXmlOneOf6_2IsaTerm [] $ FiveOf6 ap)
hXmlAxiom2IsaAxiom (AxiomAbs a ab)  =
 (axiomName a, hXmlOneOf6_2IsaTerm [] $ SixOf6 ab)

hXmlTheorem2IsaTheorem :: Theorem -> (String,IsaSign.Term)
hXmlTheorem2IsaTheorem (TheoremBound a b) =
 (theoremName a, hXmlOneOf6_2IsaTerm [] $ OneOf6 b)
hXmlTheorem2IsaTheorem (TheoremFree a f)  =
 (theoremName a, hXmlOneOf6_2IsaTerm [] $ TwoOf6 f)
hXmlTheorem2IsaTheorem (TheoremVar a v)   =
 (theoremName a, hXmlOneOf6_2IsaTerm [] $ ThreeOf6 v)
hXmlTheorem2IsaTheorem (TheoremConst a c) =
 (theoremName a, hXmlOneOf6_2IsaTerm [] $ FourOf6 c)
hXmlTheorem2IsaTheorem (TheoremApp a ap)  =
 (theoremName a, hXmlOneOf6_2IsaTerm [] $ FiveOf6 ap)
hXmlTheorem2IsaTheorem (TheoremAbs a ab)  =
 (theoremName a, hXmlOneOf6_2IsaTerm [] $ SixOf6 ab)

hXmlRecDataType2IsaRecDataType :: RecDatatypes -> [IsaSign.DomainEntry]
hXmlRecDataType2IsaRecDataType (RecDatatypes dts) =
 map hXmlDataType2IsaDataType dts

hXmlDataType2IsaDataType :: Datatype -> IsaSign.DomainEntry
hXmlDataType2IsaDataType (Datatype a tps cs) =
 (IsaSign.Type (datatypeName a) IsaConsts.holType $ map hXmlOneOf3_2IsaTyp tps,
  map (\(Constructor ca cs') ->
   (IsaConsts.mkVName $ constructorName ca,
    map trans cs')) cs)
 where
  trans (Constructor_TVar  v) = hXmlOneOf3_2IsaTyp $ OneOf3 v 
  trans (Constructor_TFree f) = hXmlOneOf3_2IsaTyp $ TwoOf3 f
  trans (Constructor_Type  t) = hXmlOneOf3_2IsaTyp $ ThreeOf3 t

hXmlFunction2IsaFunDef :: Function -> (String,IsaSign.FunDef)
hXmlFunction2IsaFunDef (Function a t eqs) =
 (functionName a, (hXmlOneOf3_2IsaTyp t, map hXmlEquation2IsaFunEqs eqs))

hXmlEquation2IsaFunEqs :: Equations -> ([IsaSign.Term],IsaSign.Term)
hXmlEquation2IsaFunEqs (Equations eqs) =
 let eqs' = map hXmlEquation_2IsaTerm eqs
 in (init eqs',last eqs')

hXmlEquation_2IsaTerm :: Equations_ -> IsaSign.Term
hXmlEquation_2IsaTerm (Equations_Bound b) =
 hXmlOneOf6_2IsaTerm [] $ OneOf6 b
hXmlEquation_2IsaTerm (Equations_Free f)  =
 hXmlOneOf6_2IsaTerm [] $ TwoOf6 f
hXmlEquation_2IsaTerm (Equations_Var v)   =
 hXmlOneOf6_2IsaTerm [] $ ThreeOf6 v
hXmlEquation_2IsaTerm (Equations_Const c) =
 hXmlOneOf6_2IsaTerm [] $ FourOf6 c
hXmlEquation_2IsaTerm (Equations_App ap)  =
 hXmlOneOf6_2IsaTerm [] $ FiveOf6 ap
hXmlEquation_2IsaTerm (Equations_Abs ab)  =
 hXmlOneOf6_2IsaTerm [] $ SixOf6 ab

hXmlClass2IsaClassDecl :: ClassDef -> (IsaSign.IsaClass,IsaSign.ClassDecl)
hXmlClass2IsaClassDecl (ClassDef a ps ass parms) =
 (IsaSign.IsaClass $ classDefName a,
  (map (IsaSign.IsaClass . parentName) ps,
   map hXmlAssumption2NamedIsaTerm ass,
   map hXmlClassParam2NamedIsaTyp parms))

hXmlAssumption2NamedIsaTerm :: Assumption -> (String,IsaSign.Term)
hXmlAssumption2NamedIsaTerm (AssumptionBound a b) =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ OneOf6 b)
hXmlAssumption2NamedIsaTerm (AssumptionFree a f)  =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ TwoOf6 f)
hXmlAssumption2NamedIsaTerm (AssumptionVar a v)   =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ ThreeOf6 v)
hXmlAssumption2NamedIsaTerm (AssumptionConst a c) =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ FourOf6 c)
hXmlAssumption2NamedIsaTerm (AssumptionApp a ap)  =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ FiveOf6 ap)
hXmlAssumption2NamedIsaTerm (AssumptionAbs a ab)  =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ SixOf6 ab)

hXmlClassParam2NamedIsaTyp :: ClassParam -> (String,IsaSign.Typ)
hXmlClassParam2NamedIsaTyp (ClassParamTVar  a v) =
 (classParamName a, hXmlOneOf3_2IsaTyp $ OneOf3 v)
hXmlClassParam2NamedIsaTyp (ClassParamTFree a f) =
 (classParamName a, hXmlOneOf3_2IsaTyp $ TwoOf3 f)
hXmlClassParam2NamedIsaTyp (ClassParamType  a t) =
 (classParamName a, hXmlOneOf3_2IsaTyp $ ThreeOf3 t)

hXmlLocale2IsaLocaleDecl :: Locale -> (String,IsaSign.LocaleDecl)
hXmlLocale2IsaLocaleDecl (Locale a parms ass thms ps) =
 let altSyn = \at -> case localeParamMixfix_i at of
                      Just i' ->
                       let i = (read i') :: Int
                       in case (localeParamInfix at,localeParamInfixl at,
                               localeParamInfixr at) of
                          (Just s,_,_) -> Just $ IsaSign.AltSyntax s [i,i] i
                          (_,Just s,_) -> Just $ IsaSign.AltSyntax s [i+1,i] i
                          (_,_,Just s) -> Just $ IsaSign.AltSyntax s [i,i+1] i
                          _ -> Nothing
                      _ -> Nothing
     params =
      map (\lc -> case lc of
                  LocaleParamTVar at tv ->(localeParamName at,
                   hXmlOneOf3_2IsaTyp (OneOf3 tv), altSyn at)
                  LocaleParamTFree at tf -> (localeParamName at,
                   hXmlOneOf3_2IsaTyp (TwoOf3 tf), altSyn at)
                  LocaleParamType at t -> (localeParamName at,
                   hXmlOneOf3_2IsaTyp (ThreeOf3 t), altSyn at)) parms
 in (localeName a,((map parentName ps), map hXmlAssumption2NamedIsaTerm ass,
                map hXmlTheorem2IsaTheorem thms,params))

hXmlType_2IsaTyp :: Type_ -> IsaSign.Typ
hXmlType_2IsaTyp (Type_TVar v) = hXmlOneOf3_2IsaTyp (OneOf3 v)
hXmlType_2IsaTyp (Type_TFree f) = hXmlOneOf3_2IsaTyp (TwoOf3 f)
hXmlType_2IsaTyp (Type_Type t) = hXmlOneOf3_2IsaTyp (ThreeOf3 t)

hXmlType2IsaTyp :: Type -> IsaSign.Typ
hXmlType2IsaTyp (Type attrs tps) =
 IsaSign.Type (typeName attrs) IsaConsts.holType (map hXmlType_2IsaTyp tps)

hXmlTFree2IsaTyp :: TFree -> IsaSign.Typ
hXmlTFree2IsaTyp (TFree attrs cls) =
 IsaSign.TFree (tFreeName attrs)
  (map hXmlClass2IsaClass cls)

hXmlOneOf3_2IsaTyp :: (OneOf3 TVar TFree Type) -> IsaSign.Typ
hXmlOneOf3_2IsaTyp (OneOf3 (TVar a cls)) =
 IsaSign.TVar (IsaSign.Indexname (tVarName a)
    (read (fromMaybe "0" (tVarIndex a)) :: Int))
  (map hXmlClass2IsaClass cls)
hXmlOneOf3_2IsaTyp (TwoOf3 f) = hXmlTFree2IsaTyp f
hXmlOneOf3_2IsaTyp (ThreeOf3 t) = hXmlType2IsaTyp t

hXmlClass2IsaClass :: Class -> IsaSign.IsaClass
hXmlClass2IsaClass = IsaSign.IsaClass . className

hXmlOneOf6_2IsaTerm :: [String] -> OneOf6 Bound Free Var Const App Abs -> IsaSign.Term
hXmlOneOf6_2IsaTerm l o = case o of
  (OneOf6 (Bound bindex)) ->
    let idx = (read bindex) :: Int
    in IsaSign.Free . IsaConsts.mkVName $ (l!!idx)
  (TwoOf6 f) -> case f of
                 FreeTVar  a _ -> free a
                 FreeTFree a _ -> free a
                 FreeType  a _ -> free a
   where free = IsaSign.Free . IsaConsts.mkVName . freeName
  (ThreeOf6 v) ->
   let vattrs = case v of
                 VarTVar d _ -> d
                 VarTFree d _ -> d
                 VarType d _ -> d
   in IsaSign.Free . IsaConsts.mkVName . varName $ vattrs
  (FourOf6 c) -> hXmlConst2IsaTerm c
  (FiveOf6 a) -> hXmlApp2IsaTerm l a
  (SixOf6 a)  -> hXmlAbs2IsaTerm l a

hXmlConst2IsaTerm :: Const -> IsaSign.Term
hXmlConst2IsaTerm c = case c of
  ConstTVar attrs c1 -> const' attrs (OneOf3 c1)
  ConstTFree attrs c1 -> const' attrs (TwoOf3 c1)
  ConstType attrs c1 -> const' attrs (ThreeOf3 c1)
 where const' a d =
        let vname = IsaSign.VName {
          IsaSign.new = constName a,
          IsaSign.altSyn = case constMixfix_i a of
           Just i' -> let i = (read i') :: Int
            in case (constInfix a,constInfixl a,constInfixr a) of
                (Just s,_,_) -> Just $ IsaSign.AltSyntax (t s) [i,i] i
                (_,Just s,_) -> Just $ IsaSign.AltSyntax (t s) [i+1,i] i
                (_,_,Just s) -> Just $ IsaSign.AltSyntax (t s) [i,i+1] i
                _ -> Nothing
              where t s = "(_ "++s++"/ _)"
              {- We need to do this so that pretty printing actually works
                 (see IsaConsts.hs 550+ and
                 IsaPrint.hs 319 (replaceUnderlines 399)
                 Maybe the use of alternative Syntax needs to be
                 completely overhauled?
              -}
           Nothing -> Nothing
         }
        in IsaSign.Const vname
              $ IsaSign.Hide
                 (hXmlOneOf3_2IsaTyp d)
                 IsaSign.NA
                 Nothing

hXmlApp2IsaTerm :: [String] -> App -> IsaSign.Term
hXmlApp2IsaTerm l (App f1 f2) = IsaSign.App (hXmlOneOf6_2IsaTerm l f1)
                                          (hXmlOneOf6_2IsaTerm l f2)
                                          IsaSign.NotCont
hXmlAbs2IsaTerm :: [String] -> Abs -> IsaSign.Term
hXmlAbs2IsaTerm l (Abs attrs t f) = IsaSign.Abs
 (IsaSign.Const (IsaConsts.mkVName . absVname $ attrs)
              $ IsaSign.Disp (hXmlOneOf3_2IsaTyp t)
                             IsaSign.NA
                             Nothing)
 {-(IsaSign.Free (IsaSign.mkVName . absVname $ attrs))-}
 (hXmlOneOf6_2IsaTerm (absVname attrs:l) f)
 IsaSign.NotCont

