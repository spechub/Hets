{- |
Module      :  $Header$
Description :  pretty printing signatures
Copyright   :  (c) Christian Maeder, Uni Bremen, DFKI GmbH 2002-2009
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

pretty printing a HasCASL environment
-}

module HasCASL.PrintLe
  ( diffClass
  , diffClassMap
  , mergeClassInfo
  , mergeMap
  , improveDiag
  , diffTypeMap
  , diffType
  , printMap1) where

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
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.Keywords
import Common.Result

import Control.Monad (foldM)
import Data.List

instance Pretty ClassInfo where
    pretty (ClassInfo rk ks) =
        if Set.null ks then less <+> pretty (rawToKind rk) else
        less <+> printList0 (Set.toList ks)

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

isPredOpDefn :: OpDefn -> Bool
isPredOpDefn od = case od of
  NoOpDefn b -> isPred b
  Definition b _ -> isPred b
  _ -> False

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

instance Pretty Env where
    pretty Env
      { classMap = cm
      , typeMap = tm
      , localTypeVars = tvs
      , assumps = ops
      , binders = bs
      , localVars = vs
      , sentences = se
      , envDiags = ds } = let
      oops = foldr Map.delete ops $ map fst bList
      poMap = Map.map (Set.partition (isPredOpDefn . opDefn)) oops
      pMap = Map.map fst poMap
      oMap = Map.map snd poMap
      ocm = diffClassMap cm cpoMap
      otm = diffTypeMap ocm tm bTypes
      ltm = concatMap ( \ (i, ti) -> map ( \ k -> (i, k))
          $ Set.toList $ otherTypeKinds ti) $ Map.toList otm
      stm = concatMap ( \ (i, ti) -> map ( \ s -> (i, s))
          $ Set.toList $ superTypes ti) $ Map.toList otm
      atm = Map.filter ( \ td -> case typeDefn td of
          AliasTypeDefn _ -> True
          _ -> False) otm
      scm = concatMap ( \ (i, ci) -> map ( \ s -> (i, s))
          $ Set.toList $ Set.delete (rawToKind $ rawKind ci) $ classKinds ci)
          $ Map.toList ocm
      bas = map (\ (b, o) -> Unparsed_anno (Annote_word "binder")
             (Line_anno $ " " ++ show b ++ ", " ++ show o) $ posOfId b)
            $ Map.toList bs
      mkPlural s = if last s == 's' then s ++ "es" else s ++ "s"
      header2 l s = keyword $ case l of
        _ : _ : _ -> mkPlural s
        _ -> s
      header m s = keyword $
        if Map.size m < 2 then s else mkPlural s
      in noPrint (Map.null ocm) (header ocm classS)
        $+$ printMap0 (Map.map ( \ ci -> ci { classKinds = Set.empty }) ocm)
        $+$ noPrint (null scm) (header2 scm classS)
        $+$ vcat (punctuate semi $ map ( \ (i, s) ->
            pretty i <+> text lessS <+> pretty s) scm)
        $+$ noPrint (null ltm) (header2 ltm typeS)
        $+$ vcat (punctuate semi $ map ( \ (i, k) ->
            pretty i <+> colon <+> pretty k) ltm)
        $+$ noPrint (null stm) (header2 stm typeS)
        $+$ vcat (punctuate semi $ map ( \ (i, s) ->
            pretty i <+> text lessS <+> pretty s) stm)
        $+$ noPrint (Map.null atm) (header atm typeS)
        $+$ printAliasTypes atm
        $+$ noPrint (Map.null tvs) (header tvs varS)
        $+$ printMap0 tvs
        $+$ vcat (map annoDoc bas)
        $+$ printSetMap (keyword opS) space oMap
        $+$ printSetMap (keyword predS) space pMap
        $+$ noPrint (Map.null vs) (header vs varS)
        $+$ printMap0 vs
        $+$ vcat (map (pretty . fromLabelledSen) $ reverse se)
        $+$ vcat (map pretty $ reverse ds)

printAliasTypes :: Map.Map Id TypeInfo -> Doc
printAliasTypes = ppMap pretty (\ td -> case typeDefn td of
  AliasTypeDefn ty ->
    let (args, t) = getArgsAndType ty in
    fsep $ map (parens . pretty) args ++ [text assignS, pretty t]
  _ -> empty) id (vcat . punctuate semi) $ \ a b -> fsep [a, b]

getArgsAndType :: Type -> ([TypeArg], Type)
getArgsAndType ty = case ty of
  TypeAbs arg t _ -> let (l, r) = getArgsAndType t in (arg : l, r)
  _ -> ([], ty)

printMap0 :: (Pretty a, Ord a, Pretty b) => Map.Map a b -> Doc
printMap0 = printMap id (vcat . punctuate semi) $ \ a b -> fsep [a, b]

printMap1 :: (Pretty a, Ord a, Pretty b) => Map.Map a b -> Doc
printMap1 = printMap id vcat $ \ a b -> fsep [a, mapsto, b]

instance Pretty Morphism where
  pretty m =
      let tm = typeIdMap m
          cm = classIdMap m
          fm = funMap m
          -- the types in funs are already mapped
          -- key und value types only differ wrt. partiality
          ds = Map.foldWithKey ( \ (i, _) (j, t) ->
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

instance Pretty a => Pretty (SymbolType a) where
    pretty t = case t of
      OpAsItemType sc -> pretty sc
      TypeAsItemType k -> pretty k
      ClassAsItemType k -> pretty k

instance Pretty Symbol where
    pretty s = keyword (case symType s of
        OpAsItemType _ -> opS
        TypeAsItemType _ -> typeS
        ClassAsItemType _ -> classS)
            <+> pretty (symName s) <+> colon <+> case symType s of
        OpAsItemType sc -> pretty sc
        TypeAsItemType k -> pretty $ rawToKind k
        ClassAsItemType k -> pretty $ rawToKind k

instance Pretty RawSymbol where
  pretty rs = case rs of
      AnID i -> pretty i
      AKindedId k i -> printSK k [i] <> pretty i
      AQualId i t ->
          printSK (symbTypeToKind t) [i] <> pretty i <+> colon <+> pretty t
      ASymbol s -> pretty s

improveDiag :: (GetRange a, Pretty a) => a -> Diagnosis -> Diagnosis
improveDiag v d = d
  { diagString = let f:l = lines $ diagString d in
      unlines $ (f ++ " of '" ++ showDoc v "'") : l
  , diagPos = getRange v }

mergeMap :: (Ord a, GetRange a, Pretty a) => (b -> b -> Result b)
         -> Map.Map a b -> Map.Map a b -> Result (Map.Map a b)
mergeMap f m1 = foldM ( \ m (k, v) -> case Map.lookup k m of
    Nothing -> return $ Map.insert k v m
    Just w -> let
      Result ds r = do
        u <- f w v
        return $ Map.insert k u m
      in Result (map (improveDiag k) ds) r) m1 . Map.toList

mergeClassInfo :: ClassInfo -> ClassInfo -> Result ClassInfo
mergeClassInfo c1 c2 = do
    k <-  minRawKind "class raw kind" (rawKind c1) $ rawKind c2
    return $ ClassInfo k $ Set.union (classKinds c1) $ classKinds c2

diffClassMap :: ClassMap -> ClassMap -> ClassMap
diffClassMap c1 c2 =
  let Result _ (Just ce) = mergeMap mergeClassInfo c1 c2
  in Map.differenceWith (diffClass ce) c1 c2

-- | compute difference of class infos
diffClass :: ClassMap -> ClassInfo -> ClassInfo -> Maybe ClassInfo
diffClass cm (ClassInfo r1 k1) (ClassInfo _ k2) =
    let ks = Set.filter (\ k -> Set.null $
                  Set.filter (flip (lesserKind cm) k) k2) k1
    in if Set.null ks then Nothing else
           Just $ ClassInfo r1 ks

diffTypeMap :: ClassMap -> TypeMap -> TypeMap -> TypeMap
diffTypeMap cm t1 t2 =
    let t = Map.differenceWith (diffType cm) t1 t2
        r = Set.intersection $ Set.union (Map.keysSet t) $ Map.keysSet bTypes
    in Map.map ( \ ti -> ti { superTypes = r $ superTypes ti }) t

-- | compute difference of type infos
diffType :: ClassMap -> TypeInfo -> TypeInfo -> Maybe TypeInfo
diffType cm ti1 ti2 =
    let k1 = otherTypeKinds ti1
        k2 = otherTypeKinds ti2
        ks = Set.filter (\ k -> Set.null $
                  Set.filter (flip (lesserKind cm) k) k2) k1
    in if Set.null ks then Nothing else
       Just $ ti1 { otherTypeKinds = ks
                  , superTypes = Set.difference (superTypes ti1) $
                                 superTypes ti2 }
