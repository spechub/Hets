module Isabelle.IsaImport where

import Text.XML.HaXml.OneOfN
import Text.XML.HaXml.XmlContent (fReadXml)
import Isabelle.IsaExport
import qualified Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.List (intercalate)

importIsaDataIO :: String ->
 IO (String,[(String,IsaSign.Typ,Maybe IsaSign.Term)],
     [(String,IsaSign.Term)], [(String,IsaSign.Term)],
     IsaSign.DomainTab)
importIsaDataIO p = do
 d' <- fReadXml p
 return $ importIsaData d'

importIsaData :: IsaExport ->
 (String,[(String,IsaSign.Typ,Maybe IsaSign.Term)],
  [(String,IsaSign.Term)], [(String,IsaSign.Term)],
  IsaSign.DomainTab)
importIsaData (IsaExport attrs (Consts consts)
               (Axioms axioms) 
               (Theorems theorems)
               (Types types)) =
 let consts'   = map mapConst                      consts
     axioms'   = map (hXmlTerm2IsaTerm []) axioms
     theorems' = map (hXmlTerm2IsaTerm []) theorems
     types'    = map hXmlTypeDecl2IsaTypeDecl      types
 in (isaExportFile attrs,consts',axioms',theorems',types')

mapConst :: ConstDecl -> (String,IsaSign.Typ, Maybe IsaSign.Term)
mapConst (ConstDecl attrs tp tm) =
 let tm' = case tm of
      OneOf2 t -> Just $ snd . (hXmlTerm2IsaTerm []) $ t
      TwoOf2 _ -> Nothing
 in (constDeclName attrs, hXmlOneOf3_2IsaTyp tp, tm')

hXmlTerm2IsaTerm :: [String] -> Term -> (String,IsaSign.Term)
hXmlTerm2IsaTerm l (TermBound attrs (Bound bindex)) =
  (termName attrs, 
    let idx = (read bindex) :: Int
    in IsaSign.Free . IsaSign.mkVName $ (l!!idx))
hXmlTerm2IsaTerm _ (TermFree attrs f) = case f of
  FreeTVar a _ -> (n, free a)
  FreeTFree a _ -> (n, free a)
  FreeType a _ -> (n, free a)
 where n = termName attrs
       free = IsaSign.Free . IsaSign.mkVName . freeName
hXmlTerm2IsaTerm _ (TermVar attrs v) =
 let vattrs = case v of
               VarTVar d _ -> d
               VarTFree d _ -> d
               VarType d _ -> d

 in (termName attrs,
     IsaSign.Free . IsaSign.mkVName . varName $ vattrs)
hXmlTerm2IsaTerm _ (TermConst attrs c) = (termName attrs, hXmlConst2IsaTerm c)
hXmlTerm2IsaTerm l (TermApp attrs a) = (termName attrs, hXmlApp2IsaTerm l a)
hXmlTerm2IsaTerm l (TermAbs attrs a) = (termName attrs, hXmlAbs2IsaTerm l a)

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
 (IsaSign.Const (IsaSign.mkVName . absVname $ attrs)
              $ IsaSign.Disp (hXmlOneOf3_2IsaTyp t)
                             IsaSign.NA
                             Nothing)
 {-(IsaSign.Free (IsaSign.mkVName . absVname $ attrs))-}
 (hXmlOneOf6_2IsaTerm (absVname attrs:l) f)
 IsaSign.NotCont

hXmlOneOf6_2IsaTerm :: [String] -> OneOf6 Bound Free Var Const App Abs -> IsaSign.Term
hXmlOneOf6_2IsaTerm l o = case o of
  (OneOf6 b) -> tm $ TermBound n b
  (TwoOf6 f) -> tm $ TermFree n f
  (ThreeOf6 v) -> tm $ TermVar n v
  (FourOf6 c) -> tm $ TermConst n c
  (FiveOf6 a) -> tm $ TermApp n a
  (SixOf6 a) -> tm $ TermAbs n a
 where tm = snd . (hXmlTerm2IsaTerm l)
       n = Term_Attrs ""

hXmlType_2IsaTyp :: Type_ -> IsaSign.Typ
hXmlType_2IsaTyp (Type_TVar v) = hXmlOneOf3_2IsaTyp (OneOf3 v)
hXmlType_2IsaTyp (Type_TFree f) = hXmlOneOf3_2IsaTyp (TwoOf3 f)
hXmlType_2IsaTyp (Type_Type t) = hXmlOneOf3_2IsaTyp (ThreeOf3 t)

hXmlType2IsaTyp :: Type -> IsaSign.Typ
hXmlType2IsaTyp (Type attrs tps) =
 IsaSign.Type (typeName attrs) holType (map hXmlType_2IsaTyp tps)

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

hXmlTypeDecl2IsaTypeDecl :: TypeDecl -> [IsaSign.DomainEntry]
hXmlTypeDecl2IsaTypeDecl (TypeDecl _ rs) = 
 let recmap = foldl (\m (RecType ra vs _) ->
                      Map.insert ((read (recTypeI ra))::Int) 
                                 ((if length (recTypeVsToString vs) > 0
                                    then (recTypeVsToString vs) ++ " "
                                    else "") ++ (recTypeName ra))
                                 m) Map.empty rs
      where recTypeVsToString (Vars vs) = intercalate " "
             (map (\v -> case v of
                          Vars_DtTFree f -> dtTFreeS f
                          _ -> "") vs)
 in map (hXmlRecType2IsaTypeDecl recmap) rs


hXmlRecType2IsaTypeDecl :: Map.Map Int String ->
 RecType -> IsaSign.DomainEntry
hXmlRecType2IsaTypeDecl recmap (RecType a (Vars vs) (Constructors cs)) = 
 let trans c = case c of
                Constructor_DtTFree (DtTFree f) ->
                 hXmlOneOf3_2IsaTyp
                  (TwoOf3 (TFree (TFree_Attrs f) []))
                Constructor_DtType (DtType ta dts) ->
                 IsaSign.Type (dtTypeS ta) holType
                  (map (\dt -> case dt of
                     DtType_DtTFree f -> trans (Constructor_DtTFree f)
                     DtType_DtType t -> trans (Constructor_DtType t)
                     DtType_DtRec r -> trans (Constructor_DtRec r)) dts)
                Constructor_DtRec (DtRec r) ->
                 hXmlOneOf3_2IsaTyp
                  (ThreeOf3 (Type (Type_Attrs (Map.findWithDefault ""
                    ((read r)::Int) recmap)) []))
 in ((IsaSign.Type (recTypeName a) holType
      (map (\v -> case v of
             Vars_DtTFree f -> trans (Constructor_DtTFree f)
             Vars_DtType t -> trans (Constructor_DtType t)
             Vars_DtRec r -> trans (Constructor_DtRec r)) vs),
      recTypeAltname a),
      map (\(Constructor ca cs') ->
       (IsaSign.mkVName (constructorVal ca),map trans cs')) cs)
