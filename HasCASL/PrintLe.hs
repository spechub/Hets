{- |
Module      :  ./HasCASL/PrintLe.hs
Description :  pretty printing signatures
Copyright   :  (c) Christian Maeder, Uni Bremen, DFKI GmbH 2002-2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

pretty printing a HasCASL environment
-}

module HasCASL.PrintLe
  ( diffClass
  , diffClassMap
  , mergeClassInfo
  , mergeClassMap
  , addClassMap
  , addCpoMap
  , minimizeClassMap
  , mergeMap
  , improveDiag
  , diffTypeMap
  , diffType
  , printMap1
  , mostSyms
  , delPreDefs
  ) where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.ClassAna

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set
import Common.Keywords
import Common.Result

import Control.Monad (foldM)
import Data.List
import Data.Maybe

import Data.Hashable

instance Pretty ClassInfo where
    pretty (ClassInfo rk ks) = less <+>
        if Set.null ks then pretty (rawToKind rk) else
        printList0 (Set.toList ks)

printGenKind :: GenKind -> Doc
printGenKind k = case k of
    Loose -> empty
    Free -> text freeS
    Generated -> text generatedS

instance Pretty TypeDefn where
    pretty td = case td of
        NoTypeDefn -> empty
        PreDatatype -> text "%(data type)%"
        AliasTypeDefn s -> text assignS <+> pretty s
        DatatypeDefn dd -> text "%[" <> pretty dd <> text "]%"

printAltDefn :: AltDefn -> Doc
printAltDefn (Construct mi ts p sels) = case mi of
    Just i -> pretty i <+> fsep (map (parens . semiDs) sels) <> pretty p
    Nothing -> text (typeS ++ sS) <+> ppWithCommas ts

instance Pretty Selector where
    pretty (Select mi t p) = let d = pretty t in case mi of
        Just i -> pretty i <+> case p of
            Partial -> text colonQuMark
               <+> if isSimpleType t then d else parens d
            Total -> colon
               <+> if isPrefixOf "?" $ show d then parens d else d
        Nothing -> d

instance Pretty TypeInfo where
    pretty (TypeInfo _ _ _ def) = pretty def

instance Pretty TypeVarDefn where
    pretty (TypeVarDefn v vk _ i) =
        printVarKind v vk <+> text ("%(var_" ++ shows i ")%")

instance Pretty VarDefn where
    pretty (VarDefn ty) =
        colon <+> pretty ty

instance Pretty ConstrInfo where
    pretty (ConstrInfo i t) =
        pretty i <+> colon <+> pretty t

instance Pretty OpDefn where
    pretty od = case od of
        NoOpDefn _ -> empty
        ConstructData _ -> text "%(constructor)%"
        SelectData cs _ -> sep
            [ text "%(selector of constructor(s)"
            , printList0 (Set.toList cs) <> text ")%" ]
        Definition b t ->
            sep [text $ "%[ " ++ if isPred b then "<=>" else "="
                , pretty t <+> text "]%" ]

isOpDefn :: OpBrand -> OpDefn -> Bool
isOpDefn b od = case od of
  NoOpDefn c -> c == b
  Definition c _ -> c == b
  _ -> False

isPredOpDefn :: OpDefn -> Bool
isPredOpDefn = isOpDefn Pred

isFunOpDefn :: OpDefn -> Bool
isFunOpDefn = isOpDefn Fun

instance Pretty OpInfo where
    pretty o = let od = opDefn o in
      sep [pretty $ (if isPredOpDefn od then unPredTypeScheme else id)
          $ opType o, pretty od]

instance Pretty DataEntry where
    pretty (DataEntry im j k args _ talts) = let
        i = Map.findWithDefault j j im
        mapAlt (Construct mi tys p sels) = Construct mi
          (map (mapType im) tys) p $ map (map mapSel) sels
        mapSel (Select mi ty p) = Select mi (mapType im ty) p
        alts = Set.map mapAlt talts
        in printGenKind k <+> keyword typeS <+>
           fsep [fcat $ pretty i : map (parens . pretty) args
                , defn, cat $ punctuate (space <> bar <> space)
                $ map printAltDefn $ Set.toList alts]

instance Pretty Sentence where
    pretty s = case s of
        Formula t -> (case t of
          QuantifiedTerm Universal (_ : _) _ _ -> id
          _ -> addBullet) $ pretty t
        DatatypeSen ls -> vcat (map pretty ls)
        ProgEqSen _ _ pe -> keyword programS <+> pretty pe

delPreDefs :: Env -> Env
delPreDefs e =
  let cm = classMap e
      tm = typeMap e
      ops = assumps e
      ocm = diffClassMap cm cpoMap
  in e
  { classMap = ocm
  , typeMap = diffTypeMap ocm tm bTypes
  , assumps = foldr (Map.delete . fst) ops bList }

getSuperClasses :: ClassMap -> [(Id, Kind)]
getSuperClasses = concatMap
  ( \ (i, ci) -> map ( \ s -> (i, s))
    . Set.toList $ Set.delete (rawToKind $ rawKind ci) $ classKinds ci)
  . Map.toList

getSuperTypes :: TypeMap -> [(Id, Id)]
getSuperTypes = concatMap
  ( \ (i, ti) -> map ( \ s -> (i, s))
    . Set.toList $ superTypes ti)
  . Map.toList

getTypeKinds :: TypeMap -> [(Id, Kind)]
getTypeKinds = concatMap
  ( \ (i, ti) -> map ( \ k -> (i, k))
    . Set.toList $ otherTypeKinds ti)
  . Map.toList

getTypeAliases :: TypeMap -> [(Id, Type)]
getTypeAliases = foldr
  ( \ (i, td) -> case typeDefn td of
    AliasTypeDefn ty -> ((i, ty) :)
    _ -> id) [] . Map.toList

instance Pretty Env where
    pretty env = let
      d = delPreDefs env
      cm = classMap d
      tm = typeMap d
      tvs = localTypeVars d
      vs = localVars d
      poMap = Map.map (Set.partition (isPredOpDefn . opDefn)) $ assumps d
      pMap = Map.map fst poMap
      aoMap = Map.map snd poMap
      foMap = Map.map (Set.partition (isFunOpDefn . opDefn)) aoMap
      fMap = Map.map fst foMap
      oMap = Map.map snd foMap
      ltm = getTypeKinds tm
      stm = getSuperTypes tm
      atm = getTypeAliases tm
      scm = getSuperClasses cm
      bas = map (\ (b, o) -> Unparsed_anno (Annote_word "binder")
             (Line_anno $ " " ++ show b ++ ", " ++ show o) $ posOfId b)
            $ Map.toList $ binders d
      mkPlural s = s ++ if last s == 's' then "es" else "s"
      header2 l s = keyword $ case l of
        _ : _ : _ -> mkPlural s
        _ -> s
      header m s = keyword $
        if Map.size m < 2 then s else mkPlural s
      in noPrint (Map.null cm) (header cm classS)
        $+$ printMap0 (Map.map ( \ ci -> ci { classKinds = Set.empty }) cm)
        $+$ noPrint (null scm) (header2 scm classS)
        $+$ vcat (punctuate semi $ map ( \ (i, s) ->
            pretty i <+> text lessS <+> pretty s) scm)
        $+$ noPrint (null ltm) (header2 ltm typeS)
        $+$ vcat (punctuate semi $ map ( \ (i, k) ->
            pretty i <+> colon <+> pretty k) ltm)
        $+$ noPrint (null stm) (header2 stm typeS)
        $+$ vcat (punctuate semi $ map ( \ (i, s) ->
            pretty i <+> text lessS <+> pretty s) stm)
        $+$ noPrint (null atm) (header2 atm typeS)
        $+$ printAliasTypes atm
        $+$ noPrint (Map.null tvs) (header tvs varS)
        $+$ printMap0 tvs
        $+$ vcat (map annoDoc bas)
        $+$ printSetMap (keyword opS) space oMap
        $+$ printSetMap (keyword predS) space pMap
        $+$ printSetMap (keyword functS) space fMap
        $+$ noPrint (Map.null vs) (header vs varS)
        $+$ printMap0 vs
        $+$ vcat (map (pretty . fromLabelledSen) . reverse $ sentences d)
        $+$ vcat (map pretty . reverse $ envDiags d)

mostSyms :: Env -> [Symbol]
mostSyms e = let
  d = delPreDefs e
  cm = classMap d
  tm = typeMap d
  in map (\ (i, k) -> idToClassSymbol i $ rawKind k) (Map.toList cm)
      ++ map (\ (i, s) -> Symbol i $ SuperClassSymbol s) (getSuperClasses cm)
      ++ map (\ (i, s) -> Symbol i $ TypeKindInstance s) (getTypeKinds tm)
      ++ map (\ (i, s) -> Symbol i $ SuperTypeSymbol s) (getSuperTypes tm)
      ++ map (\ (i, s) -> Symbol i $ TypeAliasSymbol s) (getTypeAliases tm)
      ++ concatMap (\ (i, ts) ->
                    map (\ t -> (if isPredOpDefn $ opDefn t then
                           Symbol i . PredAsItemType . unPredTypeScheme
                           else idToOpSymbol i) $ opType t) $ Set.toList ts)
             (Map.toList $ assumps d)

printAliasType :: Type -> Doc
printAliasType ty =
    let (args, t) = getArgsAndType ty in
    fsep $ map (parens . pretty) args ++ [text assignS, pretty t]

printAliasTypes :: [(Id, Type)] -> Doc
printAliasTypes = vcat . punctuate semi .
   map (\ (i, ty) -> sep [pretty i, printAliasType ty])

getArgsAndType :: Type -> ([TypeArg], Type)
getArgsAndType ty = case ty of
  TypeAbs arg t _ -> let (l, r) = getArgsAndType t in (arg : l, r)
  _ -> ([], ty)

printMap0 :: (Pretty a, Ord a, Hashable a, Pretty b) => Map.HashMap a b -> Doc
printMap0 = printMap id (vcat . punctuate semi) $ \ a b -> fsep [a, b]

printMap1 :: (Pretty a, Ord a, Hashable a, Pretty b) => Map.HashMap a b -> Doc
printMap1 = printMap id vcat $ \ a b -> fsep [a, mapsto, b]

instance Pretty Morphism where
  pretty m =
      let tm = typeIdMap m
          cm = classIdMap m
          fm = funMap m
          {- the types in funs are already mapped
          key und value types only differ wrt. partiality -}
          ds = Map.foldrWithKey ( \ (i, _) (j, t) ->
                ((pretty i <+> mapsto <+>
                  pretty j <+> colon <+> pretty t) :))
               [] fm
      in (if Map.null tm then empty
         else keyword (typeS ++ sS) <+> printMap1 tm)
         $+$ (if Map.null cm then empty
         else keyword (classS ++ sS) <+> printMap1 cm)
         $+$ (if Map.null fm then empty
             else keyword (opS ++ sS) <+> sepByCommas ds)
         $+$ colon <+> specBraces (pretty $ msource m)
                    $+$ mapsto
                    <+> specBraces (pretty $ mtarget m)

instance Pretty Symbol where
    pretty s = let ty = symType s in
      printSK (symbTypeToKind ty) [()] <+> pretty (symName s) <+> case ty of
        SuperTypeSymbol sty -> less <+> pretty sty
        SuperClassSymbol k -> less <+> pretty k
        TypeAliasSymbol t -> printAliasType t
        TypeKindInstance k -> colon <+> pretty k
        OpAsItemType sc -> colon <+> pretty sc
        TypeAsItemType k -> colon <+> pretty (rawToKind k)
        ClassAsItemType k -> colon <+> pretty (rawToKind k)
        PredAsItemType sc -> colon <+> pretty sc

instance Pretty RawSymbol where
  pretty rs = case rs of
      AnID i -> pretty i
      AKindedId k i -> printSK k [i] <+> pretty i
      ASymbol s -> pretty s

improveDiag :: (GetRange a, Pretty a) => a -> Diagnosis -> Diagnosis
improveDiag v d = d
  { diagString = let f : l = lines $ diagString d in
      unlines $ (f ++ " of '" ++ showDoc v "'") : l
  , diagPos = getRange v }

mergeMap :: (Ord a, GetRange a, Pretty a, Hashable a) => (b -> b -> Result b)
         -> Map.HashMap a b -> Map.HashMap a b -> Result (Map.HashMap a b)
mergeMap f m1 = foldM ( \ m (k, v) -> case Map.lookup k m of
    Nothing -> return $ Map.insert k v m
    Just w -> let
      Result ds r = do
        u <- f w v
        return $ Map.insert k u m
      in Result (map (improveDiag k) ds) r) m1 . Map.toList

mergeClassInfo :: ClassInfo -> ClassInfo -> Result ClassInfo
mergeClassInfo c1 c2 = do
    k <- minRawKind "class raw kind" (rawKind c1) $ rawKind c2
    return $ ClassInfo k $ Set.union (classKinds c1) $ classKinds c2

minimizeClassMap :: ClassMap -> ClassMap
minimizeClassMap cm = Map.map (\ ci -> ci { classKinds =
                          keepMinKinds cm [classKinds ci] }) cm

mergeClassMap :: ClassMap -> ClassMap -> Result ClassMap
mergeClassMap c = fmap minimizeClassMap . mergeMap mergeClassInfo c

addClassMap :: ClassMap -> ClassMap -> ClassMap
addClassMap c = fromMaybe (error "addClassMap") . maybeResult . mergeClassMap c

addCpoMap :: ClassMap -> ClassMap
addCpoMap = addClassMap cpoMap

diffClassMap :: ClassMap -> ClassMap -> ClassMap
diffClassMap c1 c2 =
  let ce = addClassMap c1 c2
  in Map.differenceWith (diffClass ce) c1 c2

-- | compute difference of class infos
diffClass :: ClassMap -> ClassInfo -> ClassInfo -> Maybe ClassInfo
diffClass cm (ClassInfo r1 k1) (ClassInfo _ k2) =
    let ks = Set.filter (\ k -> Set.null $
                  Set.filter (flip (lesserKind cm) k) k2) k1
    in if Set.null ks then Nothing else
           Just $ ClassInfo r1 ks

diffTypeMap :: ClassMap -> TypeMap -> TypeMap -> TypeMap
diffTypeMap = Map.differenceWith . diffType

-- | compute difference of type infos
diffType :: ClassMap -> TypeInfo -> TypeInfo -> Maybe TypeInfo
diffType cm ti1 ti2 =
    let k1 = otherTypeKinds ti1
        k2 = otherTypeKinds ti2
        ks = Set.filter (\ k -> Set.null $
                  Set.filter (flip (lesserKind cm) k) k2) k1
        sups = Set.difference (superTypes ti1) $ superTypes ti2
    in if Set.null ks && Set.null sups then Nothing else
       Just $ ti1 { otherTypeKinds = ks
                  , superTypes = sups }
