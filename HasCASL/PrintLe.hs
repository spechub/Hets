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

import Common.Id
import Common.GlobalAnnotations
import Common.PrettyPrint
import Common.PPUtils
import Common.Lib.Pretty as Pretty
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Keywords

instance PrettyPrint ClassInfo where
    printText0 ga (ClassInfo rk ks) = case ks of
           [] -> colon <+> printText0 ga rk
           _ -> text lessS <+> printList0 ga ks

printGenKind :: GenKind -> Doc
printGenKind k = case k of
                Loose -> empty
                Free -> text freeS <> space
                Generated -> text generatedS <> space

instance PrettyPrint TypeDefn where
    printText0 ga td = case td of
        NoTypeDefn -> empty
        PreDatatype -> text "%(data type)%"
        AliasTypeDefn s -> text assignS <+> printPseudoType ga s
        DatatypeDefn dd -> text " %[" <> printText0 ga dd <> text "]%"

printAltDefn :: GlobalAnnos -> Id -> [TypeArg] -> RawKind -> AltDefn -> Doc
printAltDefn ga dt tArgs rk (Construct mi ts p sels) = case mi of
        Just i -> hang (printText0 ga i <+> colon
                        <+> printText0 ga (createConstrType dt tArgs rk p ts))
                  2 $ fcat (map (parens . semiT_text ga) sels)
        Nothing -> text (typeS ++ sS) <+> commaT_text ga ts

instance PrettyPrint Selector where
    printText0 ga (Select mi t p) =
        (case mi of
        Just i -> printText0 ga i <+> (case p of
                             Partial -> text (colonS++quMark)
                             Total -> colon) <> space
        Nothing -> empty) <> printText0 ga t

instance PrettyPrint TypeInfo where
    printText0 ga (TypeInfo _ ks sups defn) =
        hang (colon <+> printList0 ga ks
        <> noPrint (Set.null sups)
           (space <> text lessS <+> printList0 ga (Set.toList sups)))
        2 $ printText0 ga defn

instance PrettyPrint TypeVarDefn where
    printText0 ga (TypeVarDefn v vk _ i) =
        printVarKind ga v vk <+> text ("%(var_" ++ shows i ")%")

instance PrettyPrint VarDefn where
    printText0 ga (VarDefn ty) =
        colon <+> printText0 ga ty

instance PrettyPrint ConstrInfo where
    printText0 ga (ConstrInfo i t) =
        printText0 ga i <+> colon <+> printText0 ga t

instance PrettyPrint OpDefn where
    printText0 ga od = case od of
        NoOpDefn b -> text $ "%(" ++ shows b ")%"
        ConstructData i -> text $ "%(construct " ++ showId i ")%"
        SelectData c i -> text ("%(select from " ++ showId i " constructed by")
                          $$ printList0 ga c <> text ")%"
        Definition b t -> hang (printText0 ga $ NoOpDefn b)
                          2 (text equalS <+> printText0 ga t)

instance PrettyPrint OpInfo where
    printText0 ga o = hang (colon <+> printText0 ga (opType o)
                      <> (case opAttrs o of
                          [] -> empty
                          l -> comma <> commaT_text ga l))
                      2 $ printText0 ga (opDefn o)

instance PrettyPrint OpInfos where
    printText0 ga (OpInfos l) = vcat $ map (printText0 ga) l

instance PrettyPrint DataEntry where
    printText0 ga (DataEntry im i k args rk alts) = hang
        (printGenKind k <> text typeS <+> printText0 ga i
                  <> hcat (map (parens . printText0 ga) args))
          2 (text defnS <+> vcat (map (printAltDefn ga i args rk) alts))
        $$ nest 2 (noPrint (Map.null im)
           (text withS <+> text (typeS ++ sS) <+> printText0 ga im))

instance PrettyPrint Sentence where
    printText0 ga s = case s of
        Formula t -> printText0 ga t
        DatatypeSen ls -> vcat (map (printText0 ga) ls)
        ProgEqSen _ _ pe -> text programS <+> printText0 ga pe

instance PrettyPrint Env where
    printText0 ga (Env{classMap=cm, typeMap=tm, localTypeVars=tvs,
                       assumps=ops, localVars=vs,
                       sentences=se, envDiags=ds}) =
        noPrint (Map.null cm) (header "Classes")
        $$ printMap0 ga cm
        $$ noPrint (Map.null tm) (header "Type Constructors")
        $$ printMap0 ga tm
        $$ noPrint (Map.null tvs) (header "Type Variables")
        $$ printMap0 ga tvs
        $$ noPrint (Map.null ops) (header "Assumptions")
        $$ printMap0 ga ops
        $$ noPrint (Map.null vs) (header "Variables")
        $$ printMap0 ga vs
        $$ noPrint (null se) (header "Sentences")
        $$ vcat (map (printText0 ga) $ reverse se)
        $$ noPrint (null ds) (header "Diagnostics")
        $$ vcat (map (printText0 ga) $ reverse ds)
        where header s =  text "%%" <+> text s
                          <+> text (replicate (70 - length s) '-')
              printMap0 :: (PrettyPrint a, Ord a, PrettyPrint b)
                           => GlobalAnnos -> Map.Map a b -> Doc
              printMap0 g m =
                  let l = Map.toList m in
                          vcat(map (\ (a, b) -> hang (printText0 g a)
                                    2 $ printText0 g b) l)

instance PrettyPrint Morphism where
  printText0 ga m =
      let tm = typeIdMap m
          fm = funMap m
          ds = Map.foldWithKey ( \ (i, s) (j, t) l ->
                (printText0 ga i <+> colon <+> printText0 ga s
                <+> text mapsTo <+>
                printText0 ga j <+> colon <+> printText0 ga t) : l)
               [] fm
      in (if Map.null tm then empty
         else text (typeS ++ sS) <+> printText0 ga tm)
         $$ (if Map.null fm then empty
             else text (opS ++ sS) <+> fsep (punctuate comma ds))
         $$ nest 1 colon <+> braces (printText0 ga $ msource m)
                    $$ nest 1 (text mapsTo)
                    <+> braces (printText0 ga $ mtarget m)

instance PrettyPrint a => PrettyPrint (SymbolType a) where
    printText0 ga t = case t of
      OpAsItemType sc -> printText0 ga sc
      TypeAsItemType k -> printText0 ga k
      ClassAsItemType k -> printText0 ga k

instance PrettyPrint Symbol where
    printText0 ga s = text (case symType s of
                            OpAsItemType _ -> opS
                            TypeAsItemType _ -> typeS
                            ClassAsItemType _ -> classS) <+>
                    printText0 ga (symName s) <+> text colonS <+>
                    printText0 ga (symType s)

instance PrettyPrint RawSymbol where
  printText0 ga rs = case rs of
      AnID i -> printText0 ga i
      AKindedId k i -> printSK k <> printText0 ga i
      AQualId i t -> printSK (symbTypeToKind t) <> printText0 ga i <+> colon
                       <+> printText0 ga t
      ASymbol s -> printText0 ga s
