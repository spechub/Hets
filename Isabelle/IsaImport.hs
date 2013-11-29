module Isabelle.IsaImport where

import Text.XML.HaXml.OneOfN
import Text.XML.HaXml.XmlContent (fReadXml, List1 (..))
import Isabelle.IsaExport
import qualified Isabelle.IsaSign as IsaSign
import qualified Isabelle.IsaConsts as IsaConsts
import Data.Maybe (fromMaybe, isJust)

type IsaData = (String, Maybe String, [String], [String],
                [String], [IsaSign.Sentence])

importIsaDataIO :: String ->
 IO [IsaData]
importIsaDataIO p = do
 Export (NonEmpty thys) <- fReadXml p
 return $ importIsaData thys

importIsaData :: [Thy] -> [IsaData]
importIsaData = map (\ (Thy a imports keywords uses body) ->
 let imports' = (\ (NonEmpty l) -> map importName l) imports
     keywords' = map keywordName keywords
     uses' = map useFileName uses
     body' = map hXmlBody_2IsaSentence ((\ (Body l) -> l) body)
 in (thyName a, thyHeader a, imports', keywords', uses', body'))

hXmlBody_2IsaSentence :: Body_ -> IsaSign.Sentence
hXmlBody_2IsaSentence (Body_Locale (Locale a ctxt parents body)) =
 IsaSign.Locale {
  IsaSign.localeName = IsaSign.mkQName $ localeName a,
  IsaSign.localeContext = hXmlCtxt2IsaCtxt ctxt,
  IsaSign.localeParents = map (IsaSign.mkQName . parentName) parents,
  IsaSign.localeBody = map hXmlBody_2IsaSentence ((\ (Body l) -> l) body) }
hXmlBody_2IsaSentence (Body_Cls (Cls a ctxt parents body)) =
 IsaSign.Class {
  IsaSign.className = IsaSign.mkQName $ clsName a,
  IsaSign.classContext = hXmlCtxt2IsaCtxt ctxt,
  IsaSign.classParents = map (IsaSign.mkQName . parentName) parents,
  IsaSign.classBody = map hXmlBody_2IsaSentence ((\ (Body l) -> l) body) }
hXmlBody_2IsaSentence (Body_TypeSynonym (TypeSynonym a mx (Vars vars) tp)) =
 IsaSign.TypeSynonym (IsaSign.mkQName $ typeSynonymName a)
                     (fmap hXmlMixfix2IsaMixfix mx)
                     (map (\ (TFree a' _ ) -> tFreeName a') vars)
                     (hXmlOneOf3_2IsaTyp tp)
hXmlBody_2IsaSentence (Body_Datatypes (Datatypes (NonEmpty dts))) =
 IsaSign.Datatypes (map hXmlDatatype2IsaDatatype dts)
hXmlBody_2IsaSentence (Body_Domains (Domains (NonEmpty dts))) =
 IsaSign.Domains (map hXmlDomain2IsaDomain dts)
hXmlBody_2IsaSentence (Body_Consts (Consts (NonEmpty consts))) =
 IsaSign.Consts (map (\ (ConstDef a m t) ->
  (constDefName a, fmap hXmlMixfix2IsaMixfix m,
   hXmlOneOf3_2IsaTyp t)) consts)
hXmlBody_2IsaSentence (Body_Axioms (Axioms (NonEmpty axioms))) =
 IsaSign.Axioms (map hXmlAxiom2IsaAxiom axioms)
hXmlBody_2IsaSentence (Body_Lemma (Lemma a ctxt (Proof proof) (NonEmpty s))) =
 IsaSign.Lemma {
  IsaSign.lemmaTarget = fmap IsaSign.mkQName (lemmaTarget a),
  IsaSign.lemmaContext = hXmlCtxt2IsaCtxt ctxt,
  IsaSign.lemmaProof = Just proof,
  IsaSign.lemmaProps = map (\ (Shows a' (NonEmpty tms)) ->
   IsaSign.Props {
    IsaSign.propsName = if null $ showsName a' then Nothing
                         else Just $ IsaSign.mkQName $ showsName a',
    IsaSign.propsArgs = showsArgs a',
    IsaSign.props = map (\ (AShow (NonEmpty l)) ->
                          case map (hXmlOneOf6_2IsaTerm []) l of
                           t : tms' -> IsaSign.Prop {IsaSign.prop = t,
                                                   IsaSign.propPats = tms' }
                           _ -> error "This should not happen!") tms}) s }
hXmlBody_2IsaSentence (Body_Definition (Definition a m tp (NonEmpty tms))) =
 IsaSign.Definition {
  IsaSign.definitionName = IsaSign.mkQName $ definitionName a,
  IsaSign.definitionMixfix = fmap hXmlMixfix2IsaMixfix m,
  IsaSign.definitionTarget = definitionTarget a,
  IsaSign.definitionType = hXmlOneOf3_2IsaTyp tp,
  IsaSign.definitionVars = map (hXmlOneOf6_2IsaTerm []) $ init tms,
  IsaSign.definitionTerm = hXmlOneOf6_2IsaTerm [] $ last tms }
hXmlBody_2IsaSentence (Body_Funs (Funs a (NonEmpty funs))) =
 IsaSign.Fun {
  IsaSign.funTarget = fmap IsaSign.mkQName $ funsTarget a,
  IsaSign.funSequential = isJust $ funsSequential a,
  IsaSign.funDefault = funsDefault a,
  IsaSign.funDomintros = isJust $ funsDomintros a,
  IsaSign.funPartials = isJust $ funsPartials a,
  IsaSign.funEquations = map (\ (Fun a' mx tp (NonEmpty eqs)) ->
   (funName a', fmap hXmlMixfix2IsaMixfix mx,
    hXmlOneOf3_2IsaTyp tp, map (\ (Equation (NonEmpty tms)) ->
         let tms' = map (hXmlOneOf6_2IsaTerm []) tms
         in (init tms', last tms')) eqs)) funs }
hXmlBody_2IsaSentence (Body_Primrec (Primrec a (NonEmpty funs))) =
 IsaSign.Primrec {
  IsaSign.primrecTarget = fmap IsaSign.mkQName $ primrecTarget a,
  IsaSign.primrecEquations = map (\ (Fun a' mx tp (NonEmpty eqs)) ->
   (funName a', fmap hXmlMixfix2IsaMixfix mx,
    hXmlOneOf3_2IsaTyp tp, map (\ (Equation (NonEmpty tms)) ->
         let tms' = map (hXmlOneOf6_2IsaTerm []) tms
         in (init tms', last tms')) eqs)) funs }
hXmlBody_2IsaSentence (Body_Fixrec (Fixrec (NonEmpty fs))) =
 IsaSign.Fixrec $ map (\ (FixrecFun a mx tp (NonEmpty eqs)) ->
  (fixrecFunName a, fmap hXmlMixfix2IsaMixfix mx,
   hXmlOneOf3_2IsaTyp tp, map hXmlFixrecEquation2IsaFixrecEquation eqs)) fs
hXmlBody_2IsaSentence (Body_Instantiation
 (Instantiation a arity body)) =
 IsaSign.Instantiation {
  IsaSign.instantiationType = instantiationType a,
  IsaSign.instantiationArity = (\ (Arity a1 a2) -> (hXmlSort2IsaSort a1,
   map hXmlSort2IsaSort a2)) arity,
  IsaSign.instantiationBody =
   map hXmlBody_2IsaSentence ((\ (Body l) -> l) body) }
hXmlBody_2IsaSentence (Body_Instance (Instance a (Proof proof) h)) =
 case (instanceClass a, instanceRel a, instanceClass1 a, h) of
  (Just c, Just rel, Just c1, _) -> IsaSign.InstanceSubclass {
   IsaSign.instanceClass = c,
   IsaSign.instanceRel = rel,
   IsaSign.instanceClass1 = c1,
   IsaSign.instanceProof = proof }
  (_, _, _, Just (Vars vars, Arity a1 a2)) -> IsaSign.InstanceArity {
              IsaSign.instanceTypes = map (\ (TFree a' _ ) -> tFreeName a') vars,
              IsaSign.instanceArity = (hXmlSort2IsaSort a1,
                                       map hXmlSort2IsaSort a2),
              IsaSign.instanceProof = proof }
  _ -> IsaSign.InstanceProof proof
hXmlBody_2IsaSentence (Body_Subclass (Subclass a (Proof proof))) =
 IsaSign.Subclass {
  IsaSign.subclassClass = subclassClass a,
  IsaSign.subclassTarget = fmap IsaSign.mkQName $ subclassTarget a,
  IsaSign.subclassProof = proof }
hXmlBody_2IsaSentence (Body_Typedef (Typedef a mx (Proof proof) tm vs)) =
 IsaSign.Typedef {
  IsaSign.typedefName = IsaSign.mkQName $ typedefType a,
  IsaSign.typedefVars = map (\ (TFree a' s) -> (tFreeName a',
   map hXmlClass2IsaClass s)) vs,
  IsaSign.typedefMixfix = fmap hXmlMixfix2IsaMixfix mx,
  IsaSign.typedefMorphisms = case (typedefM1 a, typedefM2 a) of
   (Just m1, Just m2) -> Just (IsaSign.mkQName m1, IsaSign.mkQName m2)
   _ -> Nothing,
  IsaSign.typedefTerm = hXmlOneOf6_2IsaTerm [] tm,
  IsaSign.typedefProof = proof }
hXmlBody_2IsaSentence (Body_Defs (Defs a (NonEmpty defs))) =
 IsaSign.Defs {
  IsaSign.defsUnchecked = isJust $ defsUnchecked a,
  IsaSign.defsOverloaded = isJust $ defsOverloaded a,
  IsaSign.defsEquations = map (\ (Def a' tp tm) ->
   IsaSign.DefEquation {
    IsaSign.defEquationName = IsaSign.mkQName $ defName a',
    IsaSign.defEquationConst = defConst a',
    IsaSign.defEquationConstType = hXmlOneOf3_2IsaTyp tp,
    IsaSign.defEquationTerm = hXmlOneOf6_2IsaTerm [] tm,
    IsaSign.defEquationArgs = defArgs a' }) defs }

hXmlCtxt2IsaCtxt :: Ctxt -> IsaSign.Ctxt
hXmlCtxt2IsaCtxt (Ctxt ctxt) =
 let (fixes, assumes) = foldl (\ (fixes', assumes') c ->
      case c of
       OneOf2 (Fixes f) -> (fixes' ++ map (\ (Fix a t mx) ->
        (fixName a, fmap hXmlMixfix2IsaMixfix mx,
         hXmlOneOf3_2IsaTyp t)) f, assumes')
       TwoOf2 (Assumes a) -> (fixes', assumes' ++ map (\ (Assumption a' tm) ->
        (assumptionName a', hXmlOneOf6_2IsaTerm [] tm)) a)) ([], []) ctxt
 in IsaSign.Ctxt {
  IsaSign.fixes = fixes,
  IsaSign.assumes = assumes }

hXmlMixfix2IsaMixfix :: Mixfix -> IsaSign.Mixfix
hXmlMixfix2IsaMixfix (Mixfix a symbs) = IsaSign.Mixfix {
 IsaSign.mixfixNargs = read $ mixfixNargs a,
 IsaSign.mixfixPrio = read $ mixfixPrio a,
 IsaSign.mixfixPretty = mixfixPretty a,
 IsaSign.mixfixTemplate = map hXmlOneOf4_2IsaMixfixTemplate symbs }

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
hXmlDatatype2IsaDatatype (Datatype a mx (NonEmpty cs) vars) =
 IsaSign.Datatype {
  IsaSign.datatypeName = IsaSign.mkQName $ datatypeName a,
  IsaSign.datatypeTVars = map hXmlTFree2IsaTyp vars,
  IsaSign.datatypeMixfix = fmap hXmlMixfix2IsaMixfix mx,
  IsaSign.datatypeConstructors = map (\ (Constructor a' mx' tp tps) ->
   case constructorName a' of
    Just name ->
     IsaSign.DatatypeConstructor {
       IsaSign.constructorName = IsaSign.mkQName name,
       IsaSign.constructorType = hXmlOneOf3_2IsaTyp tp,
       IsaSign.constructorMixfix = fmap hXmlMixfix2IsaMixfix mx',
       IsaSign.constructorArgs = map hXmlOneOf3_2IsaTyp tps }
    Nothing ->
     IsaSign.DatatypeNoConstructor {
      IsaSign.constructorArgs = map hXmlOneOf3_2IsaTyp (tp : tps) }) cs }

hXmlDomain2IsaDomain :: Domain -> IsaSign.Domain
hXmlDomain2IsaDomain (Domain a mx vars (NonEmpty cs)) =
 IsaSign.Domain {
  IsaSign.domainName = IsaSign.mkQName $ domainName a,
  IsaSign.domainTVars = map hXmlTFree2IsaTyp vars,
  IsaSign.domainMixfix = fmap hXmlMixfix2IsaMixfix mx,
  IsaSign.domainConstructors = map (\ (DomainConstructor a' tp args) ->
   IsaSign.DomainConstructor {
    IsaSign.domainConstructorName = IsaSign.mkQName $ domainConstructorName a',
    IsaSign.domainConstructorType = hXmlOneOf3_2IsaTyp tp,
    IsaSign.domainConstructorArgs = map (\ (DomainConstructorArg a'' tp') ->
     IsaSign.DomainConstructorArg {
      IsaSign.domainConstructorArgSel = fmap IsaSign.mkQName $
                                         domainConstructorArgName a'',
      IsaSign.domainConstructorArgType = hXmlOneOf3_2IsaTyp tp',
      IsaSign.domainConstructorArgLazy = isJust $ domainConstructorArgLazy a''})
     args } ) cs}

hXmlFixrecEquation2IsaFixrecEquation :: FixrecEquation -> IsaSign.FixrecEquation
hXmlFixrecEquation2IsaFixrecEquation (FixrecEquation a (Premises ps)
 (NonEmpty tms)) = IsaSign.FixrecEquation {
  IsaSign.fixrecEquationUnchecked = isJust $ fixrecEquationUnchecked a,
  IsaSign.fixrecEquationPremises = map (hXmlOneOf6_2IsaTerm []) ps,
  IsaSign.fixrecEquationPatterns = map (hXmlOneOf6_2IsaTerm []) $ init tms,
  IsaSign.fixrecEquationTerm = hXmlOneOf6_2IsaTerm [] $ last tms }

hXmlAxiom2IsaAxiom :: Axiom -> IsaSign.Axiom
hXmlAxiom2IsaAxiom (Axiom a tm) =
 IsaSign.Axiom {
  IsaSign.axiomName = IsaSign.mkQName $ axiomName a,
  IsaSign.axiomArgs = axiomArgs a,
  IsaSign.axiomTerm = hXmlOneOf6_2IsaTerm [] tm }

hXmlClass2IsaClass :: Class -> IsaSign.IsaClass
hXmlClass2IsaClass = IsaSign.IsaClass . className

hXmlSort2IsaSort :: Sort -> IsaSign.Sort
hXmlSort2IsaSort (Sort (NonEmpty cls)) = map hXmlClass2IsaClass cls

hXmlType2IsaTyp :: Type -> IsaSign.Typ
hXmlType2IsaTyp (Type attrs tps) =
 IsaSign.Type (typeName attrs) IsaConsts.holType (map hXmlOneOf3_2IsaTyp tps)

hXmlTFree2IsaTyp :: TFree -> IsaSign.Typ
hXmlTFree2IsaTyp (TFree attrs cls) =
 IsaSign.TFree (tFreeName attrs)
  (map hXmlClass2IsaClass cls)

hXmlOneOf3_2IsaTyp :: OneOf3 TVar TFree Type -> IsaSign.Typ
hXmlOneOf3_2IsaTyp (OneOf3 (TVar a cls)) =
 IsaSign.TVar (IsaSign.Indexname (tVarName a)
    (read (fromMaybe "0" (tVarIndex a)) :: Int))
  (map hXmlClass2IsaClass cls)
hXmlOneOf3_2IsaTyp (TwoOf3 f) = hXmlTFree2IsaTyp f
hXmlOneOf3_2IsaTyp (ThreeOf3 t) = hXmlType2IsaTyp t

hXmlOneOf6_2IsaTerm :: [String] -> OneOf6 Bound Free Var Const App Abs ->
                       IsaSign.Term
hXmlOneOf6_2IsaTerm l o = case o of
  (OneOf6 (Bound bindex)) ->
    let idx = read bindex :: Int
    in IsaSign.Free . IsaConsts.mkVName $ (l !! idx)
  (TwoOf6 f) -> case f of
                 FreeTVar a _ -> free a
                 FreeTFree a _ -> free a
                 FreeType a _ -> free a
   where free = IsaSign.Free . IsaConsts.mkVName . freeName
  (ThreeOf6 v) ->
   let vattrs = case v of
                 VarTVar d _ -> d
                 VarTFree d _ -> d
                 VarType d _ -> d
   in IsaSign.Free . IsaConsts.mkVName . varName $ vattrs
  (FourOf6 c) -> hXmlConst2IsaTerm c
  (FiveOf6 a) -> hXmlApp2IsaTerm l a
  (SixOf6 a) -> hXmlAbs2IsaTerm l a

hXmlConst2IsaTerm :: Const -> IsaSign.Term
hXmlConst2IsaTerm (Const a t) =
 let vname = IsaSign.VName {
      IsaSign.new = constName a,
      IsaSign.altSyn = Nothing }
 in IsaSign.Const vname $ IsaSign.Hide
     (hXmlOneOf3_2IsaTyp t) IsaSign.NA Nothing

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
 (hXmlOneOf6_2IsaTerm (absVname attrs : l) f)
 IsaSign.NotCont
