module Isabelle.IsaImport where

import Text.XML.HaXml.OneOfN
import Text.XML.HaXml.XmlContent (fReadXml,List1(..))
import Isabelle.IsaExport
import qualified Isabelle.IsaSign as IsaSign
import qualified Isabelle.IsaConsts as IsaConsts
import Data.Maybe (fromMaybe)

type IsaData = (String,Maybe String,[String],[String],
                [String],[IsaSign.Sentence])

importIsaDataIO :: String ->
 IO [IsaData]
importIsaDataIO p = do
 Export (NonEmpty thys) <- fReadXml p
 return $ importIsaData thys

importIsaData :: [Thy] -> [IsaData]
importIsaData = map (\(Thy a imports keywords uses body) ->
 let imports'  = (\(NonEmpty l) -> map importName l) imports
     keywords' = map keywordName keywords
     uses'     = map useFileName uses
     body'     = map hXmlBody_2IsaSentence ((\(Body l) -> l) body)
 in (thyName a,thyHeader a,imports',keywords',uses',body'))

hXmlBody_2IsaSentence :: Body_ -> IsaSign.Sentence
hXmlBody_2IsaSentence (Body_Locale (Locale a ctxt sig parents body)) =
 IsaSign.Locale {
  IsaSign.localeName    = IsaSign.mkQName $ localeName a,
  IsaSign.localeContext = hXmlCtxt2IsaCtxt ctxt,
  IsaSign.localeSigData = hXmlSigData2IsaSigData sig,
  IsaSign.localeParents = map (IsaSign.mkQName . parentName) parents,
  IsaSign.localeBody    = map hXmlBody_2IsaSentence ((\(Body l) -> l) body) }
hXmlBody_2IsaSentence (Body_Cls (Cls a ctxt sig parents body)) =
 IsaSign.Class {
  IsaSign.className    = IsaSign.mkQName $ clsName a,
  IsaSign.classContext = hXmlCtxt2IsaCtxt ctxt,
  IsaSign.classSigData = hXmlSigData2IsaSigData sig,
  IsaSign.classParents = map (IsaSign.mkQName . parentName) parents,
  IsaSign.classBody    = map hXmlBody_2IsaSentence ((\(Body l) -> l) body) }
hXmlBody_2IsaSentence (Body_TypeSynonym (TypeSynonym a sig (Vars vars) tp)) =
 IsaSign.TypeSynonym (IsaSign.mkQName $ typeSynonymName a)
                     (hXmlSigData2IsaSigData sig)
                     (map (\(TFree a _ ) -> tFreeName a) vars)
                     (hXmlOneOf3_2IsaTyp tp)
hXmlBody_2IsaSentence (Body_Datatypes (Datatypes (NonEmpty dts))) =
 IsaSign.Datatypes (map hXmlDatatype2IsaDatatype dts)
hXmlBody_2IsaSentence (Body_Consts (Consts (NonEmpty consts))) =
 IsaSign.Consts (map (\(ConstDef a sig t) ->
  (hXmlSigData2IsaSigData sig,constDefName a,
   hXmlOneOf3_2IsaTyp t)) consts)
hXmlBody_2IsaSentence (Body_Axioms (Axioms (NonEmpty axioms))) =
 IsaSign.Axioms (map hXmlAxiom2IsaAxiom axioms)
hXmlBody_2IsaSentence (Body_Lemma (Lemma a ctxt (Proof proof)
                                                (NonEmpty shows))) =
 IsaSign.Lemma {
  IsaSign.lemmaTarget  = maybe Nothing (Just . IsaSign.mkQName) (lemmaTarget a),
  IsaSign.lemmaContext = hXmlCtxt2IsaCtxt ctxt,
  IsaSign.lemmaProof   = Just proof,
  IsaSign.lemmaProps   = map (\(Shows a (NonEmpty tms)) ->
   IsaSign.Props {
    IsaSign.propsName  = if null $ showsName a then Nothing
                         else Just $ IsaSign.mkQName $ showsName a,
    IsaSign.propsArgs  = if null $ showsArgs a then Nothing
                         else Just $ showsArgs a,
    IsaSign.props      = map (\(AShow (NonEmpty l)) ->
                          case map hXmlAShow_2IsaTerm l of
                           t:tms -> IsaSign.Prop {IsaSign.prop = t,
                                                  IsaSign.propPats = tms}
                           _ -> error "This should not happen!") tms}) shows }
hXmlBody_2IsaSentence (Body_Definition (Definition a sig maybe_tp tm)) =
 IsaSign.Definition {
  IsaSign.definitionName    = maybe Nothing (Just . IsaSign.mkQName) $
                               definitionName a,
  IsaSign.definitionTarget  = definitionTarget a,
  IsaSign.definitionSigData = hXmlSigData2IsaSigData sig,
  IsaSign.definitionType    = maybe Nothing (\tp -> Just $
                            hXmlOneOf3_2IsaTyp tp) maybe_tp,
  IsaSign.definitionTerm    = hXmlOneOf6_2IsaTerm [] $ tm }
hXmlBody_2IsaSentence (Body_Fun (Fun a sig (NonEmpty fsigs) (NonEmpty tms))) =
 IsaSign.Fun {
  IsaSign.funSigData = hXmlSigData2IsaSigData sig,
  IsaSign.funTarget = maybe Nothing (Just . IsaSign.mkQName) $
                       funTarget a,
  IsaSign.funSequential = maybe False (\_ -> True) $ funSequential a,
  IsaSign.funDefault    = funDefault a,
  IsaSign.funDomintros  = maybe False (\_ -> True) $ funDomintros a,
  IsaSign.funPartials   = maybe False (\_ -> True) $ funPartials a,
  IsaSign.funSigs       = map (\(FunSig a maybe_tp) ->
   IsaSign.FunSig {
    IsaSign.funSigType = case maybe_tp of
     Just (FunSig_TVar v)  -> Just $ hXmlOneOf3_2IsaTyp (OneOf3 v)
     Just (FunSig_TFree f) -> Just $ hXmlOneOf3_2IsaTyp (TwoOf3 f)
     Just (FunSig_Type t)  -> Just $ hXmlOneOf3_2IsaTyp (ThreeOf3 t)
     Nothing -> Nothing,
    IsaSign.funSigName = IsaSign.mkQName $ funSigName a })
   fsigs,
  IsaSign.funEquations  = map (hXmlOneOf6_2IsaTerm []) tms }

hXmlCtxt2IsaCtxt :: Ctxt -> IsaSign.Ctxt
hXmlCtxt2IsaCtxt (Ctxt fixes' assumes') = IsaSign.Ctxt {
  IsaSign.fixes   = case fixes' of
                          Just (Fixes fixes) -> map hXmlFix2IsaNamedTyp fixes
                          _ -> [],
  IsaSign.assumes = case assumes' of
                          Just (Assumes assumes) ->
                           map hXmlAssumption2IsaNamedTerm assumes
                          _ -> [] }

hXmlSigData2IsaSigData :: SigData -> IsaSign.SigData
hXmlSigData2IsaSigData (SigData a) = IsaSign.SigData $
 map hXmlSigData_2IsaAddSigData a

hXmlSigData_2IsaAddSigData :: SigData_ -> IsaSign.AddSigData
hXmlSigData_2IsaAddSigData (SigData_AddType (AddType a as)) =
 IsaSign.AddType {
  IsaSign.name  = IsaSign.mkQName $ addTypeName a,
  IsaSign.arity = read $ addTypeArity a,
  IsaSign.mx    = case addTypePrio a of
                   Just s  -> Just (read s,map hXmlOneOf4_2IsaMixfixTemplate as)
                   Nothing -> Nothing }
hXmlSigData_2IsaAddSigData (SigData_AddConst (AddConst a t as)) =
 IsaSign.AddConst {
  IsaSign.name  = IsaSign.mkQName $ addConstName a,
  IsaSign.nargs = maybe Nothing (\i -> Just $ read i) $ addConstNargs a,
  IsaSign.tp    = maybe Nothing (\t -> Just $ hXmlOneOf3_2IsaTyp t) t,
  IsaSign.mx    = case addConstPrio a of
                   Just s  -> Just (read s,map hXmlOneOf4_2IsaMixfixTemplate as)
                   Nothing -> Nothing }
hXmlSigData_2IsaAddSigData (SigData_AddTypeSynonym (AddTypeSynonym a t)) =
 IsaSign.AddTypeSynonym {
  IsaSign.name = IsaSign.mkQName $ addTypeSynonymName a,
  IsaSign.tpS  = hXmlOneOf3_2IsaTyp t }

hXmlOneOf4_2IsaMixfixTemplate :: OneOf4 Arg AString Break Block ->
                                 IsaSign.MixfixTemplate
hXmlOneOf4_2IsaMixfixTemplate (OneOf4 a) =
 IsaSign.Arg (read $ argPrio a)
hXmlOneOf4_2IsaMixfixTemplate (TwoOf4 a) =
 IsaSign.Str (stringVal a)
hXmlOneOf4_2IsaMixfixTemplate (ThreeOf4 a) =
 IsaSign.Break (read $ breakPrio a)
hXmlOneOf4_2IsaMixfixTemplate (FourOf4 (Block a as)) =
 IsaSign.Block (read $ blockPrio a) (map hXmlOneOf4_2IsaMixfixTemplate as)

hXmlDatatype2IsaDatatype :: Datatype -> IsaSign.Datatype
hXmlDatatype2IsaDatatype (Datatype a sig (NonEmpty cs) vars) =
 IsaSign.Datatype {
  IsaSign.datatypeName         = IsaSign.mkQName $ datatypeName a,
  IsaSign.datatypeSigData      = hXmlSigData2IsaSigData sig,
  IsaSign.datatypeTVars        = map (\(TFree a _ ) -> tFreeName a) vars,
  IsaSign.datatypeConstructors = map (\(Constructor a tps) ->
   IsaSign.DatatypeConstructor {
    IsaSign.constructorName = IsaSign.mkQName $ constructorName a,
    IsaSign.constructorArgs = map hXmlOneOf3_2IsaTyp tps }) cs }

hXmlFix2IsaNamedTyp :: Fix -> (String,Maybe IsaSign.Typ)
hXmlFix2IsaNamedTyp (Fix a (Just (Fix_TVar v))) =
 (fixName a,Just $ hXmlOneOf3_2IsaTyp (OneOf3 v))
hXmlFix2IsaNamedTyp (Fix a (Just (Fix_TFree v))) =
 (fixName a,Just $ hXmlOneOf3_2IsaTyp (TwoOf3 v))
hXmlFix2IsaNamedTyp (Fix a (Just (Fix_Type v))) =
 (fixName a,Just $ hXmlOneOf3_2IsaTyp (ThreeOf3 v))
hXmlFix2IsaNamedTyp (Fix a Nothing) = (fixName a,Nothing)

hXmlAssumption2IsaNamedTerm :: Assumption -> (String,IsaSign.Term)
hXmlAssumption2IsaNamedTerm (AssumptionBound a b) =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ OneOf6 b)
hXmlAssumption2IsaNamedTerm (AssumptionFree a f)  =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ TwoOf6 f)
hXmlAssumption2IsaNamedTerm (AssumptionVar a v)   =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ ThreeOf6 v)
hXmlAssumption2IsaNamedTerm (AssumptionConst a c) =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ FourOf6 c)
hXmlAssumption2IsaNamedTerm (AssumptionApp a ap)  =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ FiveOf6 ap)
hXmlAssumption2IsaNamedTerm (AssumptionAbs a ab)  =
 (assumptionName a, hXmlOneOf6_2IsaTerm [] $ SixOf6 ab)

hXmlAShow_2IsaTerm :: AShow_ -> IsaSign.Term
hXmlAShow_2IsaTerm (AShow_Bound b) = hXmlOneOf6_2IsaTerm [] $ OneOf6 b
hXmlAShow_2IsaTerm (AShow_Free f)  = hXmlOneOf6_2IsaTerm [] $ TwoOf6 f
hXmlAShow_2IsaTerm (AShow_Var v)   = hXmlOneOf6_2IsaTerm [] $ ThreeOf6 v
hXmlAShow_2IsaTerm (AShow_Const c) = hXmlOneOf6_2IsaTerm [] $ FourOf6 c
hXmlAShow_2IsaTerm (AShow_App ap)  = hXmlOneOf6_2IsaTerm [] $ FiveOf6 ap
hXmlAShow_2IsaTerm (AShow_Abs ab)  = hXmlOneOf6_2IsaTerm [] $ SixOf6 ab

hXmlAxiom2IsaAxiom :: Axiom -> IsaSign.Axiom
hXmlAxiom2IsaAxiom (AxiomBound a b) =
 IsaSign.Axiom {
  IsaSign.axiomName = IsaSign.mkQName $ axiomName a,
  IsaSign.axiomArgs = axiomArgs a,
  IsaSign.axiomTerm = hXmlOneOf6_2IsaTerm [] $ OneOf6 b }
hXmlAxiom2IsaAxiom (AxiomFree a f)  =
 IsaSign.Axiom {
  IsaSign.axiomName = IsaSign.mkQName $ axiomName a,
  IsaSign.axiomArgs = axiomArgs a,
  IsaSign.axiomTerm = hXmlOneOf6_2IsaTerm [] $ TwoOf6 f }
hXmlAxiom2IsaAxiom (AxiomVar a v)   =
 IsaSign.Axiom {
  IsaSign.axiomName = IsaSign.mkQName $ axiomName a,
  IsaSign.axiomArgs = axiomArgs a,
  IsaSign.axiomTerm = hXmlOneOf6_2IsaTerm [] $ ThreeOf6 v }
hXmlAxiom2IsaAxiom (AxiomConst a c) =
 IsaSign.Axiom {
  IsaSign.axiomName = IsaSign.mkQName $ axiomName a,
  IsaSign.axiomArgs = axiomArgs a,
  IsaSign.axiomTerm = hXmlOneOf6_2IsaTerm [] $ FourOf6 c }
hXmlAxiom2IsaAxiom (AxiomApp a ap)  =
 IsaSign.Axiom {
  IsaSign.axiomName = IsaSign.mkQName $ axiomName a,
  IsaSign.axiomArgs = axiomArgs a,
  IsaSign.axiomTerm = hXmlOneOf6_2IsaTerm [] $ FiveOf6 ap }
hXmlAxiom2IsaAxiom (AxiomAbs a ab)  =
 IsaSign.Axiom {
  IsaSign.axiomName = IsaSign.mkQName $ axiomName a,
  IsaSign.axiomArgs = axiomArgs a,
  IsaSign.axiomTerm = hXmlOneOf6_2IsaTerm [] $ SixOf6 ab }

hXmlConst2IsaConst :: Const -> (String,IsaSign.Typ)
hXmlConst2IsaConst (ConstTVar  a v) =
 (constName a, hXmlOneOf3_2IsaTyp $ OneOf3 v)
hXmlConst2IsaConst (ConstTFree a f) =
 (constName a, hXmlOneOf3_2IsaTyp $ TwoOf3 f)
hXmlConst2IsaConst (ConstType  a t) =
 (constName a, hXmlOneOf3_2IsaTyp $ ThreeOf3 t)

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

hXmlType_2IsaTyp :: Type_ -> IsaSign.Typ
hXmlType_2IsaTyp (Type_TVar v) = hXmlOneOf3_2IsaTyp (OneOf3 v)
hXmlType_2IsaTyp (Type_TFree f) = hXmlOneOf3_2IsaTyp (TwoOf3 f)
hXmlType_2IsaTyp (Type_Type t) = hXmlOneOf3_2IsaTyp (ThreeOf3 t)

hXmlClass2IsaClass :: Class -> IsaSign.IsaClass
hXmlClass2IsaClass = IsaSign.IsaClass . className

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
          IsaSign.altSyn = Nothing
              {- We need to do this so that pretty printing actually works
                 (see IsaConsts.hs 550+ and
                 IsaPrint.hs 319 (replaceUnderlines 399)
                 Maybe the use of alternative Syntax needs to be
                 completely overhauled?
              -}
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

