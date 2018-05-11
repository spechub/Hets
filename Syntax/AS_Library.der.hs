{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Syntax/AS_Library.der.hs
Description :  abstract syntax of DOL documents and CASL specification libraries
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2016
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Abstract syntax of HetCASL specification libraries
   Follows Sect. II:2.2.5 of the CASL Reference Manual.
Abstract syntax of DOL documents
   Follows the DOL OMG standard, clauses 9.3 and M.1
-}

module Syntax.AS_Library where

-- DrIFT command:
{-! global: GetRange !-}

import Common.Id
import Common.IRI
import Common.AS_Annotation
import Common.LibName

import Data.Maybe
import Data.Typeable

import Logic.Grothendieck
import Logic.Logic

import Syntax.AS_Architecture
import Syntax.AS_Structured

import Framework.AS
import Framework.ATC_Framework ()

data LIB_DEFN = Lib_defn LibName [Annoted LIB_ITEM] Range [Annotation]
                {- pos: "library"
                list of annotations is parsed preceding the first LIB_ITEM
                the last LIB_ITEM may be annotated with a following comment
                the first LIB_ITEM cannot be annotated -}
                deriving (Show, Typeable)

{- for information on the list of Pos see the documentation in
   AS_Structured.hs and AS_Architecture.hs -}

data LIB_ITEM = Spec_defn SPEC_NAME GENERICITY (Annoted SPEC) Range
              -- pos: "spec", "=", opt "end"
              | View_defn IRI GENERICITY VIEW_TYPE [G_mapping] Range
              -- pos: "view", ":", opt "=", opt "end"
              | Entail_defn IRI ENTAIL_TYPE Range
              -- pos: "entailment", "=", opt "end"
              | Equiv_defn IRI EQUIV_TYPE OmsOrNetwork Range
              -- pos: "equivalence", ":", "=", opt "end"
              | Align_defn IRI (Maybe ALIGN_ARITIES) VIEW_TYPE
                [CORRESPONDENCE] AlignSem Range
              | Module_defn IRI MODULE_TYPE G_symb_items_list Range
              {- G_symb_items_list is RESTRICTION-SIGNATURE
              TODO: CONSERVATIVE? -}
              | Query_defn IRI G_symb_items_list G_basic_spec (Annoted SPEC)
                (Maybe IRI) Range
              -- pos: "query", "=", "select", "where", "in", "along"
              | Subst_defn IRI VIEW_TYPE G_symb_map_items_list Range
              -- pos: "substitution", ":", "=", opt "end"
              | Result_defn IRI [IRI] IRI Bool Range
              -- pos: "result", commas, "for", "%complete", opt "end"
              | Arch_spec_defn ARCH_SPEC_NAME (Annoted ARCH_SPEC) Range
              -- pos: "arch", "spec", "=", opt "end"
              | Unit_spec_defn SPEC_NAME UNIT_SPEC Range
              -- pos: "unit", "spec", "=", opt "end"
              | Ref_spec_defn SPEC_NAME REF_SPEC Range
              -- pos: "refinement", "=", opt "end"
              | Network_defn IRI Network Range
              -- pos: "network", "=", opt "end"
              | Download_items LibName DownloadItems Range
              -- pos: "from", "get", "|->", commas, opt "end"
              | Logic_decl LogicDescr Range
              -- pos:  "logic", Logic_name
              | Newlogic_defn LogicDef Range
              -- pos:  "newlogic", Logic_name, "=", opt "end"
              | Newcomorphism_defn ComorphismDef Range
              -- pos: "newcomorphism", Comorphism_name, "=", opt "end"
                deriving (Show, Typeable)

data AlignSem = SingleDomain | GlobalDomain | ContextualizedDomain
  deriving (Show, Typeable, Bounded, Enum)

{- Item maps are the documented CASL renamed entities whereas a unique item
contains the new target name of the single arbitrarily named item from the
downloaded library. -}
data DownloadItems =
    ItemMaps [ItemNameMap]
  | UniqueItem IRI
    deriving (Show, Typeable)

addDownload :: Bool -> SPEC_NAME -> Annoted LIB_ITEM
addDownload unique = emptyAnno . addDownloadAux unique

addDownloadAux :: Bool -> SPEC_NAME -> LIB_ITEM
addDownloadAux unique j =
  let libPath = deleteQuery j
      query = iriQuery j -- this used to be the fragment
      i = case query of
        "" -> j
        "?" -> libPath
        _ : r -> fromMaybe libPath $ parseIRICurie r
  in Download_items (iriLibName i)
    (if unique then UniqueItem i else ItemMaps [ItemNameMap i Nothing])
    $ iriPos i

data GENERICITY = Genericity PARAMS IMPORTED Range deriving (Show, Typeable)
                  -- pos: many of "[","]" opt ("given", commas)

emptyGenericity :: GENERICITY
emptyGenericity = Genericity (Params []) (Imported []) nullRange

data PARAMS = Params [Annoted SPEC] deriving (Show, Typeable)

data IMPORTED = Imported [Annoted SPEC] deriving (Show, Typeable)

data VIEW_TYPE = View_type (Annoted SPEC) (Annoted SPEC) Range
  deriving (Show, Typeable)
  -- pos: "to"

data EQUIV_TYPE = Equiv_type OmsOrNetwork OmsOrNetwork Range
  deriving (Show, Typeable)
  -- pos: "<->"

data MODULE_TYPE = Module_type (Annoted SPEC) (Annoted SPEC) Range
  deriving (Show, Typeable)

data ALIGN_ARITIES = Align_arities ALIGN_ARITY ALIGN_ARITY
  deriving (Show, Typeable)

data ALIGN_ARITY = AA_InjectiveAndTotal | AA_Injective | AA_Total
                 | AA_NeitherInjectiveNorTotal
                   deriving (Show, Enum, Bounded, Typeable)

data OmsOrNetwork = MkOms (Annoted SPEC)
  | MkNetwork Network
  deriving (Show, Typeable)

data ENTAIL_TYPE = Entail_type OmsOrNetwork OmsOrNetwork Range
  | OMSInNetwork IRI Network SPEC Range
  deriving (Show, Typeable)
  -- pos "entails"

showAlignArity :: ALIGN_ARITY -> String
showAlignArity ar = case ar of
  AA_InjectiveAndTotal -> "1"
  AA_Injective -> "?"
  AA_Total -> "+"
  AA_NeitherInjectiveNorTotal -> "*"

data ItemNameMap =
    ItemNameMap IRI (Maybe IRI)
    deriving (Show, Eq, Typeable)

makeLogicItem :: Language lid => lid -> Annoted LIB_ITEM
makeLogicItem lid = emptyAnno $ Logic_decl
  (nameToLogicDescr $ Logic_name
   (language_name lid) Nothing Nothing) nullRange

makeSpecItem :: SPEC_NAME -> Annoted SPEC -> Annoted LIB_ITEM
makeSpecItem sn as =
    emptyAnno $ Spec_defn sn emptyGenericity as nullRange

fromBasicSpec :: LibName -> SPEC_NAME -> G_basic_spec -> LIB_DEFN
fromBasicSpec ln sn gbs =
    Lib_defn ln [makeSpecItem sn $ makeSpec gbs] nullRange []

getDeclSpecNames :: LIB_ITEM -> [IRI]
getDeclSpecNames li = case li of
  Spec_defn sn _ _ _ -> [sn]
  Download_items _ di _ -> getImportNames di
  _ -> []

getGenSpecArgNames :: LIB_ITEM -> ([IRI], LIB_ITEM)
getGenSpecArgNames li = case li of
  Spec_defn sn g as r -> let (iris, s') = getActualParams $ item as 
                       in  (iris, Spec_defn sn g as{item = s'} r)
  _ -> ([], li)

getActualParams :: SPEC -> ([IRI], SPEC)
getActualParams sp = 
 let f c aspec r = let (iris, sp') = getActualParams $ item aspec
                   in (iris, c aspec{item = sp'} r)
     fs c aspecs r = let resl = map (getActualParams.item) aspecs
                         iris = concat $ map fst resl
                         aspecs' = map (\(as, s) -> as {item = s}) $ zip aspecs $ map snd resl
                     in (iris, c aspecs' r)
 in case sp of
     Extraction aspec r -> f Extraction aspec r
     Translation aspec r -> f Translation aspec r
     Reduction aspec r -> f Reduction aspec r
     Approximation aspec r -> f Approximation aspec r
     Minimization aspec r -> f Minimization aspec r
     Filtering aspec r -> f Filtering aspec r   
     Bridge aspec1 rens aspec2 r -> let (iris1, sp1) = getActualParams $ item aspec1 
                                        (iris2, sp2) = getActualParams $ item aspec2
                                        aspec1' = aspec1{item = sp1}
                                        aspec2' = aspec2{item = sp2}
                                    in (iris1 ++ iris2, Bridge aspec1' rens aspec2' r) 
     Union aspecs r -> fs Union aspecs r
     Intersection aspecs r -> fs Intersection aspecs r
     Extension aspecs r -> fs Extension aspecs r
     Free_spec aspec r -> f Free_spec aspec r
     Cofree_spec aspec r -> f Cofree_spec aspec r
     Minimize_spec aspec r -> f Minimize_spec aspec r
     Closed_spec aspec r -> f Closed_spec aspec r
     Group aspec r -> f Group aspec r
     Qualified_spec ld aspec r -> f (Qualified_spec ld) aspec r
     Data l1 l2 aspec1 aspec2 r -> let (iris1, sp1) = getActualParams $ item aspec1 
                                       (iris2, sp2) = getActualParams $ item aspec2
                                       aspec1' = aspec1{item = sp1}
                                       aspec2' = aspec2{item = sp2}
                                    in (iris1 ++ iris2, Data l1 l2 aspec1' aspec2' r) 
     Spec_inst sn aargs miri r -> let 
                  resL = map (\p -> case p of 
                                    Fit_spec aspec [] r' -> 
                                     case item aspec of 
                                       Spec_inst x [] Nothing _ -> ([x], Fit_spec (aspec{item=Unsolved_IRI x}) [] r')
                                       _ -> ([], p)
                                    _ -> ([],p)) $ map item aargs
                                  in (concat $ map fst resL, Spec_inst sn (map (\(as, s) -> as {item = s}) $ zip aargs $ map snd resL) miri r)    
     _-> ([], sp) 

getImportNames :: DownloadItems -> [IRI]
getImportNames di = case di of
  ItemMaps im -> map (\ (ItemNameMap i mi) -> fromMaybe i mi) im
  UniqueItem i -> [i]

getOms :: OmsOrNetwork -> [SPEC]
getOms o = case o of
  MkOms s -> [item s]
  MkNetwork _ -> []

getSpecDef :: LIB_ITEM -> [SPEC]
getSpecDef li = case li of
  Spec_defn _ _ as _ -> [item as]
  View_defn _ _ (View_type s1 s2 _) _ _ -> [item s1, item s2]
  Entail_defn _ (Entail_type s1 s2 _) _ -> getOms s1 ++ getOms s2
  Equiv_defn _ (Equiv_type s1 s2 _) as _ ->
    getOms s1 ++ getOms s2 ++ getOms as
  Align_defn _ _ (View_type s1 s2 _) _ _ _ -> [item s1, item s2]
  Module_defn _ (Module_type s1 s2 _) _ _ -> [item s1, item s2]
  _ -> []
