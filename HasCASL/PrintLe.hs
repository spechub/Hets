{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder  and Uni Bremen 2002-2003

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

pretty printing a HasCASL environment
-}

module HasCASL.PrintLe where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs
import HasCASL.Le
import HasCASL.Builtin

import Common.Id
import Common.Doc
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Keywords
import Common.PrettyPrint
import Common.Result

import Data.List

instance PrettyPrint Morphism where
    printText0 ga = toText ga . pretty

instance PrettyPrint Env where
    printText0 ga = toText (addBuiltins ga) . pretty

instance PrettyPrint Sentence where
    printText0 ga = toText (addBuiltins ga) . pretty

instance PrettyPrint SymbMapItems where
    printText0 ga = toText ga . pretty

instance PrettyPrint SymbItems where
    printText0 ga = toText ga . pretty

instance PrettyPrint RawSymbol where
    printText0 ga = toText ga . pretty

instance PrettyPrint Symbol where
    printText0 ga = toText ga . pretty

instance PrintLaTeX Morphism where
    printLatex0 ga = toLatex ga . pretty

instance PrintLaTeX Env where
    printLatex0 ga = toLatex (addBuiltins ga) . pretty

instance PrintLaTeX Sentence where
    printLatex0 ga = toLatex (addBuiltins ga) . pretty

instance PrintLaTeX SymbMapItems where
    printLatex0 ga = toLatex ga . pretty

instance PrintLaTeX SymbItems where
    printLatex0 ga = toLatex ga . pretty

instance PrintLaTeX RawSymbol where
    printLatex0 ga = toLatex ga . pretty

instance PrintLaTeX Symbol where
    printLatex0 ga = toLatex ga . pretty

instance Pretty ClassInfo where
    pretty (ClassInfo rk ks) = case ks of
           [] -> colon <+> pretty rk
           _ -> text lessS <+> printList0 ks

printGenKind :: GenKind -> Doc
printGenKind k = case k of
                Loose -> empty
                Free -> text freeS
                Generated -> text generatedS

instance Pretty TypeDefn where
    pretty td = case td of
        NoTypeDefn -> empty
        PreDatatype -> text "%(data type)%"
        AliasTypeDefn s -> text assignS <+> printPseudoType s
        DatatypeDefn dd -> text " %[" <> pretty dd <> text "]%"

printAltDefn :: Id -> [TypeArg] -> RawKind -> AltDefn -> Doc
printAltDefn dt tArgs rk (Construct mi ts p sels) = case mi of
        Just i -> fcat $ [pretty i <> space, colon <> space,
                          pretty (createConstrType dt tArgs rk p ts)]
                         ++ map (parens . semiDs) sels
        Nothing -> text (typeS ++ sS) <+> commaDs ts

instance Pretty Selector where
    pretty (Select mi t p) =
        (case mi of
        Just i -> pretty i <+> (case p of
                             Partial -> text (colonS++quMark)
                             Total -> colon) <> space
        Nothing -> empty) <> pretty t

instance Pretty TypeInfo where
    pretty (TypeInfo _ ks sups def) =
        fsep $ [colon, printList0 ks]
             ++ (if Set.null sups then []
                 else [less, printList0 $ Set.toList sups])
             ++ case def of 
                  NoTypeDefn -> [] 
                  _ -> [pretty def]

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
        NoOpDefn b -> text $ "%(" ++ shows b ")%"
        ConstructData i -> text $ "%(construct " ++ showId i ")%"
        SelectData c i -> text ("%(select from " ++ showId i " constructed by")
                          $+$ printList0 c <> text ")%"
        Definition b t -> fsep [pretty $ NoOpDefn b, equals, pretty t]

instance Pretty OpInfo where
    pretty o = let l = opAttrs o in
               fsep $ [ colon
                      , pretty (opType o) <> if null l then empty else comma]
                      ++ punctuate comma (map pretty l)
                      ++ [pretty $ opDefn o]

instance Pretty OpInfos where
    pretty (OpInfos l) = vcat $ map pretty l

instance Pretty DataEntry where
    pretty (DataEntry im i k args rk alts) =
        printGenKind k <+> keyword typeS <+>
        fsep ([fcat $ pretty i : map (parens . pretty) args
              , defn, vcat $ map (printAltDefn i args rk) alts]
             ++ if Map.null im then [] 
                else [text withS, text (typeS ++ sS), printMap0 im])

instance Pretty Sentence where
    pretty s = case s of
        Formula t -> pretty t
        DatatypeSen ls -> vcat (map pretty ls)
        ProgEqSen _ _ pe -> keyword programS <+> pretty pe

instance Pretty Env where
    pretty (Env{classMap=cm, typeMap=tm, localTypeVars=tvs,
                       assumps=ops, localVars=vs,
                       sentences=se, envDiags=ds}) =
      let oops = foldr Map.delete ops $ map fst bList
          otm = Map.difference tm $ addUnit Map.empty
          header s =  text "%%" <+> text s
                      <+> text (replicate (70 - length s) '-')      
      in noPrint (Map.null cm) (header "Classes")
        $+$ printMap0 cm
        $+$ noPrint (Map.null otm) (header "Type Constructors")
        $+$ printMap0 otm
        $+$ noPrint (Map.null tvs) (header "Type Variables")
        $+$ printMap0 tvs
        $+$ noPrint (Map.null oops) (header "Assumptions")
        $+$ printMap0 oops
        $+$ noPrint (Map.null vs) (header "Variables")
        $+$ printMap0 vs
        $+$ noPrint (null se) (header "Sentences")
        $+$ vcat (map pretty $ reverse se)
        $+$ noPrint (null ds) (header "Diagnostics")
        $+$ vcat (map pretty $ reverse ds)

printMap0 :: (Pretty a, Ord a, Pretty b) => Map.Map a b -> Doc
printMap0 = printMap []

printMap1 :: (Pretty a, Ord a, Pretty b) => Map.Map a b -> Doc
printMap1 = printMap [mapsto]

printMap :: (Pretty a, Ord a, Pretty b) => [Doc] -> Map.Map a b -> Doc
printMap d m = vcat $ map (\ (a, b) -> fsep $ 
                      pretty a : d ++ [pretty b]) $ Map.toList m

instance Pretty Diagnosis where
    pretty (Diag k s (Range sp)) =
        (if isMessageW
            then empty
            else text (case k of
                  Error -> "***"
                  _ -> "###") <+> text (show k))
        <> (case sp of
             [] | isMessageW -> empty
                | otherwise  -> comma
             _ -> space <> let
                      mi = minimumBy comparePos sp
                      ma = maximumBy comparePos sp
                  in case comparePos mi ma of
                     EQ -> text (showPos ma ",")
                     _ -> text $ showPos mi "-"
                          ++ showPos ma {sourceName = ""} "," )
        <+> text s
        where isMessageW = case k of
                           MessageW -> True
                           _        -> False

instance Pretty Morphism where
  pretty m =
      let tm = typeIdMap m
          fm = funMap m
          ds = Map.foldWithKey ( \ (i, s) (j, t) l ->
                (pretty i <+> colon <+> pretty s
                <+> mapsto <+>
                pretty j <+> colon <+> pretty t) : l)
               [] fm
      in (if Map.null tm then empty
         else keyword (typeS ++ sS) <+> printMap0 tm)
         $+$ (if Map.null fm then empty
             else keyword (opS ++ sS) <+> fsep (punctuate comma ds))
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
                            ClassAsItemType _ -> classS) <+>
                    pretty (symName s) <+> colon <+>
                    pretty (symType s)

instance Pretty RawSymbol where
  pretty rs = case rs of
      AnID i -> pretty i
      AKindedId k i -> printSK k <> pretty i
      AQualId i t -> printSK (symbTypeToKind t) <> pretty i <+> colon
                       <+> pretty t
      ASymbol s -> pretty s
