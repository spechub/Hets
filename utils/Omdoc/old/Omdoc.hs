module Omdoc where

import Text.XML.HaXml.Xml2Haskell
import Text.XML.HaXml.OneOfN

import MoreOfN

import Char (isSpace)


{-Type decls-}

data Omdoc = Omdoc Omdoc_Attrs (Maybe Metadata) (Maybe Catalogue)
		   [(OneOf21 Omtext Type Assertion Alternative Example Proof Proofobject Exercise Solution Omlet Private Code Presentation Omstyle Theory Omgroup Ignore Ref Theory_inclusion Decomposition Axiom_inclusion)]
	   deriving (Eq,Show)
data Omdoc_Attrs = Omdoc_Attrs
    { omdocId :: String
    , omdocStyle :: (Maybe String)
    , omdocMid :: (Maybe String)
    , omdocXmlns :: (Defaultable String)
    , omdocXmlns'xsi :: (Defaultable String)
    , omdocXsi'schemaLocation :: (Defaultable String)
    , omdocType :: (Maybe Omdoc_type)
    , omdocCatalogue :: (Maybe String)
    , omdocVersion :: (Defaultable String)
    } deriving (Eq,Show)
data Omdoc_type = Omdoc_type_enumeration  |  Omdoc_type_sequence
		   |  Omdoc_type_itemize  |  Omdoc_type_narrative  | 
		  Omdoc_type_dataset  |  Omdoc_type_labeled_dataset  | 
		  Omdoc_type_theory_collection
		deriving (Eq,Show)
newtype Catalogue = Catalogue [Loc] 		deriving (Eq,Show)
data Loc = Loc
    { locTheory :: String
    , locOmdoc :: (Maybe String)
    , locCd :: (Maybe String)
    } deriving (Eq,Show)
data Omtext = Omtext Omtext_Attrs (Maybe Metadata) (List1 CMP)
		     (Maybe FMP)
	    deriving (Eq,Show)
data Omtext_Attrs = Omtext_Attrs
    { omtextId :: String
    , omtextStyle :: (Maybe String)
    , omtextMid :: (Maybe String)
    , omtextType :: (Maybe Omtext_type)
    , omtextFor :: (Maybe String)
    } deriving (Eq,Show)
data Omtext_type = Omtext_type_abstract  | 
		   Omtext_type_introduction  |  Omtext_type_conclusion  | 
		   Omtext_type_thesis  |  Omtext_type_antithesis  | 
		   Omtext_type_elaboration  |  Omtext_type_motivation  | 
		   Omtext_type_evidence  |  Omtext_type_note  |  Omtext_type_annote
		    |  Omtext_type_comment
		 deriving (Eq,Show)
data CMP = CMP CMP_Attrs [CMP_]
	 deriving (Eq,Show)
data CMP_Attrs = CMP_Attrs
    { cMPXml'lang :: (Defaultable CMP_xml'lang)
    } deriving (Eq,Show)
data CMP_ = CMP_Str String
	  | CMP_OMOBJ OMOBJ
	  | CMP_Omlet Omlet
	  | CMP_With With
	  | CMP_Ref Ref
	  | CMP_Ignore Ignore
	  deriving (Eq,Show)
data CMP_xml'lang = CMP_xml'lang_aa  |  CMP_xml'lang_ab  | 
		    CMP_xml'lang_af  |  CMP_xml'lang_am  |  CMP_xml'lang_ar  | 
		    CMP_xml'lang_as  |  CMP_xml'lang_ay  |  CMP_xml'lang_az  | 
		    CMP_xml'lang_ba  |  CMP_xml'lang_be  |  CMP_xml'lang_bg  | 
		    CMP_xml'lang_bh  |  CMP_xml'lang_bi  |  CMP_xml'lang_bn  | 
		    CMP_xml'lang_bo  |  CMP_xml'lang_br  |  CMP_xml'lang_ca  | 
		    CMP_xml'lang_co  |  CMP_xml'lang_cs  |  CMP_xml'lang_cy  | 
		    CMP_xml'lang_da  |  CMP_xml'lang_de  |  CMP_xml'lang_dz  | 
		    CMP_xml'lang_el  |  CMP_xml'lang_en  |  CMP_xml'lang_eo  | 
		    CMP_xml'lang_es  |  CMP_xml'lang_et  |  CMP_xml'lang_eu  | 
		    CMP_xml'lang_fa  |  CMP_xml'lang_fi  |  CMP_xml'lang_fj  | 
		    CMP_xml'lang_fo  |  CMP_xml'lang_fr  |  CMP_xml'lang_fy  | 
		    CMP_xml'lang_ga  |  CMP_xml'lang_gd  |  CMP_xml'lang_gl  | 
		    CMP_xml'lang_gn  |  CMP_xml'lang_gu  |  CMP_xml'lang_ha  | 
		    CMP_xml'lang_he  |  CMP_xml'lang_hi  |  CMP_xml'lang_hr  | 
		    CMP_xml'lang_hu  |  CMP_xml'lang_hy  |  CMP_xml'lang_ia  | 
		    CMP_xml'lang_ie  |  CMP_xml'lang_ik  |  CMP_xml'lang_id  | 
		    CMP_xml'lang_is  |  CMP_xml'lang_it  |  CMP_xml'lang_iu  | 
		    CMP_xml'lang_ja  |  CMP_xml'lang_jv  |  CMP_xml'lang_ka  | 
		    CMP_xml'lang_kk  |  CMP_xml'lang_kl  |  CMP_xml'lang_km  | 
		    CMP_xml'lang_kn  |  CMP_xml'lang_ko  |  CMP_xml'lang_ks  | 
		    CMP_xml'lang_ku  |  CMP_xml'lang_ky  |  CMP_xml'lang_la  | 
		    CMP_xml'lang_ln  |  CMP_xml'lang_lo  |  CMP_xml'lang_lt  | 
		    CMP_xml'lang_lv  |  CMP_xml'lang_mg  |  CMP_xml'lang_mi  | 
		    CMP_xml'lang_mk  |  CMP_xml'lang_ml  |  CMP_xml'lang_mn  | 
		    CMP_xml'lang_mo  |  CMP_xml'lang_mr  |  CMP_xml'lang_ms  | 
		    CMP_xml'lang_mt  |  CMP_xml'lang_my  |  CMP_xml'lang_na  | 
		    CMP_xml'lang_ne  |  CMP_xml'lang_nl  |  CMP_xml'lang_no  | 
		    CMP_xml'lang_oc  |  CMP_xml'lang_om  |  CMP_xml'lang_or  | 
		    CMP_xml'lang_pa  |  CMP_xml'lang_pl  |  CMP_xml'lang_ps  | 
		    CMP_xml'lang_pt  |  CMP_xml'lang_qu  |  CMP_xml'lang_rm  | 
		    CMP_xml'lang_rn  |  CMP_xml'lang_ro  |  CMP_xml'lang_ru  | 
		    CMP_xml'lang_rw  |  CMP_xml'lang_sa  |  CMP_xml'lang_sd  | 
		    CMP_xml'lang_sg  |  CMP_xml'lang_sh  |  CMP_xml'lang_si  | 
		    CMP_xml'lang_sk  |  CMP_xml'lang_sl  |  CMP_xml'lang_sm  | 
		    CMP_xml'lang_sn  |  CMP_xml'lang_so  |  CMP_xml'lang_sq  | 
		    CMP_xml'lang_sr  |  CMP_xml'lang_ss  |  CMP_xml'lang_st  | 
		    CMP_xml'lang_su  |  CMP_xml'lang_sv  |  CMP_xml'lang_sw  | 
		    CMP_xml'lang_ta  |  CMP_xml'lang_te  |  CMP_xml'lang_tg  | 
		    CMP_xml'lang_th  |  CMP_xml'lang_ti  |  CMP_xml'lang_tk  | 
		    CMP_xml'lang_tl  |  CMP_xml'lang_tn  |  CMP_xml'lang_to  | 
		    CMP_xml'lang_tr  |  CMP_xml'lang_ts  |  CMP_xml'lang_tt  | 
		    CMP_xml'lang_tw  |  CMP_xml'lang_ug  |  CMP_xml'lang_uk  | 
		    CMP_xml'lang_ur  |  CMP_xml'lang_uz  |  CMP_xml'lang_vi  | 
		    CMP_xml'lang_vo  |  CMP_xml'lang_wo  |  CMP_xml'lang_xh  | 
		    CMP_xml'lang_yi  |  CMP_xml'lang_yo  |  CMP_xml'lang_za  | 
		    CMP_xml'lang_zh  |  CMP_xml'lang_zu
		  deriving (Eq,Show)
data With = With With_Attrs [With_]
	  deriving (Eq,Show)
data With_Attrs = With_Attrs
    { withId :: (Maybe String)
    , withStyle :: (Maybe String)
    , withXmlns :: (Defaultable String)
    , withXmlns'xsi :: (Defaultable String)
    , withXsi'schemaLocation :: (Defaultable String)
    } deriving (Eq,Show)
data With_ = With_Str String
	   | With_OMOBJ OMOBJ
	   | With_Omlet Omlet
	   | With_With With
	   | With_Ref Ref
	   | With_Ignore Ignore
	   deriving (Eq,Show)
data Omgroup = Omgroup Omgroup_Attrs (Maybe Metadata)
		       [(OneOf24 Symbol Axiom Definition Adt Imports Inclusion Omtext Type Assertion Alternative Example Proof Proofobject Exercise Solution Omlet Private Code Presentation Omstyle Theory Omgroup Ignore Ref)]
	     deriving (Eq,Show)
data Omgroup_Attrs = Omgroup_Attrs
    { omgroupId :: (Maybe String)
    , omgroupStyle :: (Maybe String)
    , omgroupMid :: (Maybe String)
    , omgroupType :: (Maybe Omgroup_type)
    } deriving (Eq,Show)
data Omgroup_type = Omgroup_type_enumeration  | 
		    Omgroup_type_sequence  |  Omgroup_type_itemize  | 
		    Omgroup_type_narrative  |  Omgroup_type_dataset  | 
		    Omgroup_type_labeled_dataset
		  deriving (Eq,Show)
data Ref = Ref
    { refXref :: String
    , refType :: (Defaultable String)
    } deriving (Eq,Show)
data Symbol = Symbol Symbol_Attrs (Maybe Metadata) [CMP]
		     [(OneOf3 Commonname Type Selector)]
	    deriving (Eq,Show)
data Symbol_Attrs = Symbol_Attrs
    { symbolId :: String
    , symbolStyle :: (Maybe String)
    , symbolMid :: (Maybe String)
    , symbolKind :: (Defaultable Symbol_kind)
    , symbolScope :: (Defaultable Symbol_scope)
    , symbolGenerated_by :: (Maybe String)
    } deriving (Eq,Show)
data Symbol_kind = Symbol_kind_type  |  Symbol_kind_sort  | 
		   Symbol_kind_object
		 deriving (Eq,Show)
data Symbol_scope = Symbol_scope_global  |  Symbol_scope_local
		  deriving (Eq,Show)
data Commonname = Commonname Commonname_Attrs [Commonname_]
		deriving (Eq,Show)
data Commonname_Attrs = Commonname_Attrs
    { commonnameXml'lang :: (Defaultable Commonname_xml'lang)
    , commonnameMid :: (Maybe String)
    } deriving (Eq,Show)
data Commonname_ = Commonname_Str String
		 | Commonname_OMOBJ OMOBJ
		 | Commonname_Omlet Omlet
		 | Commonname_With With
		 | Commonname_Ref Ref
		 | Commonname_Ignore Ignore
		 deriving (Eq,Show)
data Commonname_xml'lang = Commonname_xml'lang_aa  | 
			   Commonname_xml'lang_ab  |  Commonname_xml'lang_af  | 
			   Commonname_xml'lang_am  |  Commonname_xml'lang_ar  | 
			   Commonname_xml'lang_as  |  Commonname_xml'lang_ay  | 
			   Commonname_xml'lang_az  |  Commonname_xml'lang_ba  | 
			   Commonname_xml'lang_be  |  Commonname_xml'lang_bg  | 
			   Commonname_xml'lang_bh  |  Commonname_xml'lang_bi  | 
			   Commonname_xml'lang_bn  |  Commonname_xml'lang_bo  | 
			   Commonname_xml'lang_br  |  Commonname_xml'lang_ca  | 
			   Commonname_xml'lang_co  |  Commonname_xml'lang_cs  | 
			   Commonname_xml'lang_cy  |  Commonname_xml'lang_da  | 
			   Commonname_xml'lang_de  |  Commonname_xml'lang_dz  | 
			   Commonname_xml'lang_el  |  Commonname_xml'lang_en  | 
			   Commonname_xml'lang_eo  |  Commonname_xml'lang_es  | 
			   Commonname_xml'lang_et  |  Commonname_xml'lang_eu  | 
			   Commonname_xml'lang_fa  |  Commonname_xml'lang_fi  | 
			   Commonname_xml'lang_fj  |  Commonname_xml'lang_fo  | 
			   Commonname_xml'lang_fr  |  Commonname_xml'lang_fy  | 
			   Commonname_xml'lang_ga  |  Commonname_xml'lang_gd  | 
			   Commonname_xml'lang_gl  |  Commonname_xml'lang_gn  | 
			   Commonname_xml'lang_gu  |  Commonname_xml'lang_ha  | 
			   Commonname_xml'lang_he  |  Commonname_xml'lang_hi  | 
			   Commonname_xml'lang_hr  |  Commonname_xml'lang_hu  | 
			   Commonname_xml'lang_hy  |  Commonname_xml'lang_ia  | 
			   Commonname_xml'lang_ie  |  Commonname_xml'lang_ik  | 
			   Commonname_xml'lang_id  |  Commonname_xml'lang_is  | 
			   Commonname_xml'lang_it  |  Commonname_xml'lang_iu  | 
			   Commonname_xml'lang_ja  |  Commonname_xml'lang_jv  | 
			   Commonname_xml'lang_ka  |  Commonname_xml'lang_kk  | 
			   Commonname_xml'lang_kl  |  Commonname_xml'lang_km  | 
			   Commonname_xml'lang_kn  |  Commonname_xml'lang_ko  | 
			   Commonname_xml'lang_ks  |  Commonname_xml'lang_ku  | 
			   Commonname_xml'lang_ky  |  Commonname_xml'lang_la  | 
			   Commonname_xml'lang_ln  |  Commonname_xml'lang_lo  | 
			   Commonname_xml'lang_lt  |  Commonname_xml'lang_lv  | 
			   Commonname_xml'lang_mg  |  Commonname_xml'lang_mi  | 
			   Commonname_xml'lang_mk  |  Commonname_xml'lang_ml  | 
			   Commonname_xml'lang_mn  |  Commonname_xml'lang_mo  | 
			   Commonname_xml'lang_mr  |  Commonname_xml'lang_ms  | 
			   Commonname_xml'lang_mt  |  Commonname_xml'lang_my  | 
			   Commonname_xml'lang_na  |  Commonname_xml'lang_ne  | 
			   Commonname_xml'lang_nl  |  Commonname_xml'lang_no  | 
			   Commonname_xml'lang_oc  |  Commonname_xml'lang_om  | 
			   Commonname_xml'lang_or  |  Commonname_xml'lang_pa  | 
			   Commonname_xml'lang_pl  |  Commonname_xml'lang_ps  | 
			   Commonname_xml'lang_pt  |  Commonname_xml'lang_qu  | 
			   Commonname_xml'lang_rm  |  Commonname_xml'lang_rn  | 
			   Commonname_xml'lang_ro  |  Commonname_xml'lang_ru  | 
			   Commonname_xml'lang_rw  |  Commonname_xml'lang_sa  | 
			   Commonname_xml'lang_sd  |  Commonname_xml'lang_sg  | 
			   Commonname_xml'lang_sh  |  Commonname_xml'lang_si  | 
			   Commonname_xml'lang_sk  |  Commonname_xml'lang_sl  | 
			   Commonname_xml'lang_sm  |  Commonname_xml'lang_sn  | 
			   Commonname_xml'lang_so  |  Commonname_xml'lang_sq  | 
			   Commonname_xml'lang_sr  |  Commonname_xml'lang_ss  | 
			   Commonname_xml'lang_st  |  Commonname_xml'lang_su  | 
			   Commonname_xml'lang_sv  |  Commonname_xml'lang_sw  | 
			   Commonname_xml'lang_ta  |  Commonname_xml'lang_te  | 
			   Commonname_xml'lang_tg  |  Commonname_xml'lang_th  | 
			   Commonname_xml'lang_ti  |  Commonname_xml'lang_tk  | 
			   Commonname_xml'lang_tl  |  Commonname_xml'lang_tn  | 
			   Commonname_xml'lang_to  |  Commonname_xml'lang_tr  | 
			   Commonname_xml'lang_ts  |  Commonname_xml'lang_tt  | 
			   Commonname_xml'lang_tw  |  Commonname_xml'lang_ug  | 
			   Commonname_xml'lang_uk  |  Commonname_xml'lang_ur  | 
			   Commonname_xml'lang_uz  |  Commonname_xml'lang_vi  | 
			   Commonname_xml'lang_vo  |  Commonname_xml'lang_wo  | 
			   Commonname_xml'lang_xh  |  Commonname_xml'lang_yi  | 
			   Commonname_xml'lang_yo  |  Commonname_xml'lang_za  | 
			   Commonname_xml'lang_zh  |  Commonname_xml'lang_zu
			 deriving (Eq,Show)
data Type = Type Type_Attrs [CMP] OMOBJ
	  deriving (Eq,Show)
data Type_Attrs = Type_Attrs
    { typeId :: (Maybe String)
    , typeStyle :: (Maybe String)
    , typeMid :: (Maybe String)
    , typeFor :: (Maybe String)
    , typeSystem :: String
    } deriving (Eq,Show)
data FMP = FMPAssumption_Conclusion FMP_Attrs
				    ([Assumption],[Conclusion])
	 | FMPOMOBJ FMP_Attrs OMOBJ
	 deriving (Eq,Show)
data FMP_Attrs = FMP_Attrs
    { fMPLogic :: (Maybe String)
    , fMPMid :: (Maybe String)
    } deriving (Eq,Show)
data Assumption = Assumption Assumption_Attrs [CMP] (Maybe (OMOBJ))
		deriving (Eq,Show)
data Assumption_Attrs = Assumption_Attrs
    { assumptionId :: String
    , assumptionStyle :: (Maybe String)
    , assumptionMid :: (Maybe String)
    } deriving (Eq,Show)
data Conclusion = Conclusion Conclusion_Attrs [CMP] (Maybe (OMOBJ))
		deriving (Eq,Show)
data Conclusion_Attrs = Conclusion_Attrs
    { conclusionId :: String
    , conclusionStyle :: (Maybe String)
    , conclusionMid :: (Maybe String)
    } deriving (Eq,Show)
data Axiom = Axiom Axiom_Attrs (Maybe Metadata) [Symbol] [CMP]
		   [FMP]
	   deriving (Eq,Show)
data Axiom_Attrs = Axiom_Attrs
    { axiomId :: String
    , axiomStyle :: (Maybe String)
    , axiomMid :: (Maybe String)
    , axiomGenerated_by :: (Maybe String)
    } deriving (Eq,Show)
data Definition = Definition Definition_Attrs (Maybe Metadata)
			     [CMP] [FMP] (Maybe (OneOf2 (List1 Requation) OMOBJ))
			     (Maybe Measure) (Maybe Omdoc.Ordering)
		deriving (Eq,Show)
data Definition_Attrs = Definition_Attrs
    { definitionJust_by :: (Maybe String)
    , definitionType :: (Defaultable Definition_type)
    , definitionGenerated_by :: (Maybe String)
    , definitionId :: String
    , definitionStyle :: (Maybe String)
    , definitionMid :: (Maybe String)
    , definitionFor :: String
    } deriving (Eq,Show)
data Definition_type = Definition_type_simple  | 
		       Definition_type_inductive  |  Definition_type_implicit  | 
		       Definition_type_recursive  |  Definition_type_obj
		     deriving (Eq,Show)
data Requation = Requation Requation_Attrs Pattern Value
	       deriving (Eq,Show)
data Requation_Attrs = Requation_Attrs
    { requationId :: (Maybe String)
    , requationStyle :: (Maybe String)
    , requationMid :: (Maybe String)
    } deriving (Eq,Show)
newtype Pattern = Pattern OMOBJ 		deriving (Eq,Show)
newtype Value = Value OMOBJ 		deriving (Eq,Show)
data Measure = Measure Measure_Attrs OMOBJ
	     deriving (Eq,Show)
data Measure_Attrs = Measure_Attrs
    { measureMid :: (Maybe String)
    } deriving (Eq,Show)
data Omdoc.Ordering = Omdoc.Ordering Ordering_Attrs OMOBJ
	      deriving (Eq,Show)
data Ordering_Attrs = Ordering_Attrs
    { orderingMid :: (Maybe String)
    } deriving (Eq,Show)
data Adt = Adt Adt_Attrs (Maybe Metadata) [Commonname] [CMP]
	       (List1 Sortdef)
	 deriving (Eq,Show)
data Adt_Attrs = Adt_Attrs
    { adtType :: (Defaultable Adt_type)
    , adtId :: String
    , adtStyle :: (Maybe String)
    , adtMid :: (Maybe String)
    } deriving (Eq,Show)
data Adt_type = Adt_type_loose  |  Adt_type_generated  | 
		Adt_type_free
	      deriving (Eq,Show)
data Sortdef = Sortdef Sortdef_Attrs [Commonname]
		       [(OneOf2 Constructor Insort)] (Maybe Recognizer)
	     deriving (Eq,Show)
data Sortdef_Attrs = Sortdef_Attrs
    { sortdefId :: String
    , sortdefStyle :: (Maybe String)
    , sortdefMid :: (Maybe String)
    , sortdefScope :: (Defaultable Sortdef_scope)
    } deriving (Eq,Show)
data Sortdef_scope = Sortdef_scope_global  |  Sortdef_scope_local
		   deriving (Eq,Show)
data Insort = Insort
    { insortFor :: String
    } deriving (Eq,Show)
data Constructor = Constructor Constructor_Attrs [Commonname]
			       [Argument]
		 deriving (Eq,Show)
data Constructor_Attrs = Constructor_Attrs
    { constructorId :: String
    , constructorStyle :: (Maybe String)
    , constructorMid :: (Maybe String)
    , constructorKind :: (Defaultable Constructor_kind)
    , constructorScope :: (Defaultable Constructor_scope)
    } deriving (Eq,Show)
data Constructor_kind = Constructor_kind_type  | 
			Constructor_kind_sort  |  Constructor_kind_object
		      deriving (Eq,Show)
data Constructor_scope = Constructor_scope_global  | 
			 Constructor_scope_local
		       deriving (Eq,Show)
data Recognizer = Recognizer Recognizer_Attrs [Commonname]
		deriving (Eq,Show)
data Recognizer_Attrs = Recognizer_Attrs
    { recognizerId :: String
    , recognizerStyle :: (Maybe String)
    , recognizerMid :: (Maybe String)
    , recognizerKind :: (Defaultable Recognizer_kind)
    , recognizerScope :: (Defaultable Recognizer_scope)
    } deriving (Eq,Show)
data Recognizer_kind = Recognizer_kind_type  | 
		       Recognizer_kind_sort  |  Recognizer_kind_object
		     deriving (Eq,Show)
data Recognizer_scope = Recognizer_scope_global  | 
			Recognizer_scope_local
		      deriving (Eq,Show)
data Argument = Argument Argument_Attrs (Maybe Selector)
	      deriving (Eq,Show)
data Argument_Attrs = Argument_Attrs
    { argumentSort :: String
    } deriving (Eq,Show)
data Selector = Selector Selector_Attrs [Commonname]
	      deriving (Eq,Show)
data Selector_Attrs = Selector_Attrs
    { selectorId :: String
    , selectorStyle :: (Maybe String)
    , selectorMid :: (Maybe String)
    , selectorKind :: (Defaultable Selector_kind)
    , selectorScope :: (Defaultable Selector_scope)
    , selectorTotal :: (Defaultable Selector_total)
    } deriving (Eq,Show)
data Selector_kind = Selector_kind_type  |  Selector_kind_sort  | 
		     Selector_kind_object
		   deriving (Eq,Show)
data Selector_scope = Selector_scope_global  | 
		      Selector_scope_local
		    deriving (Eq,Show)
data Selector_total = Selector_total_yes  |  Selector_total_no
		    deriving (Eq,Show)
data Assertion = Assertion Assertion_Attrs (Maybe Metadata)
			   [Symbol] [CMP] [FMP]
	       deriving (Eq,Show)
data Assertion_Attrs = Assertion_Attrs
    { assertionId :: String
    , assertionStyle :: (Maybe String)
    , assertionMid :: (Maybe String)
    , assertionGenerated_by :: (Maybe String)
    , assertionTheory :: (Maybe String)
    , assertionType :: (Defaultable Assertion_type)
    , assertionProofs :: (Maybe String)
    } deriving (Eq,Show)
data Assertion_type = Assertion_type_theorem  | 
		      Assertion_type_lemma  |  Assertion_type_corollary  | 
		      Assertion_type_conjecture  |  Assertion_type_false_conjecture  | 
		      Assertion_type_obligation  |  Assertion_type_postulate  | 
		      Assertion_type_formula  |  Assertion_type_assumption  | 
		      Assertion_type_proposition
		    deriving (Eq,Show)
data Alternative = Alternative Alternative_Attrs (Maybe Metadata)
			       [CMP] (OneOf3 FMP [Requation] OMOBJ)
		 deriving (Eq,Show)
data Alternative_Attrs = Alternative_Attrs
    { alternativeTheory :: String
    , alternativeType :: (Defaultable Alternative_type)
    , alternativeGenerated_by :: (Maybe String)
    , alternativeJust_by :: (Maybe String)
    , alternativeEntailed_by :: String
    , alternativeEntails :: String
    , alternativeEntailed_by_thm :: String
    , alternativeEntails_thm :: String
    , alternativeId :: String
    , alternativeStyle :: (Maybe String)
    , alternativeMid :: (Maybe String)
    , alternativeFor :: String
    } deriving (Eq,Show)
data Alternative_type = Alternative_type_simple  | 
			Alternative_type_inductive  |  Alternative_type_implicit  | 
			Alternative_type_recursive  |  Alternative_type_obj
		      deriving (Eq,Show)
data Proof = Proof Proof_Attrs (Maybe Metadata) [Symbol] [CMP]
		   [(OneOf3 Metacomment Derive Hypothesis)] Conclude
	   deriving (Eq,Show)
data Proof_Attrs = Proof_Attrs
    { proofTheory :: (Maybe String)
    , proofId :: String
    , proofStyle :: (Maybe String)
    , proofMid :: (Maybe String)
    , proofFor :: String
    } deriving (Eq,Show)
data Proofobject = Proofobject Proofobject_Attrs (Maybe Metadata)
			       [CMP] OMOBJ
		 deriving (Eq,Show)
data Proofobject_Attrs = Proofobject_Attrs
    { proofobjectTheory :: (Maybe String)
    , proofobjectId :: String
    , proofobjectStyle :: (Maybe String)
    , proofobjectMid :: (Maybe String)
    , proofobjectFor :: String
    } deriving (Eq,Show)
data Metacomment = Metacomment Metacomment_Attrs [CMP]
		 deriving (Eq,Show)
data Metacomment_Attrs = Metacomment_Attrs
    { metacommentId :: (Maybe String)
    , metacommentStyle :: (Maybe String)
    , metacommentMid :: (Maybe String)
    } deriving (Eq,Show)
data Derive = Derive Derive_Attrs [CMP] (Maybe FMP) (Maybe Method)
		     [Premise] (Maybe (OneOf2 Proof Proofobject))
	    deriving (Eq,Show)
data Derive_Attrs = Derive_Attrs
    { deriveId :: String
    , deriveStyle :: (Maybe String)
    , deriveMid :: (Maybe String)
    } deriving (Eq,Show)
data Conclude = Conclude Conclude_Attrs [CMP] (Maybe Method)
			 [Premise] (Maybe (OneOf2 Proof Proofobject))
	      deriving (Eq,Show)
data Conclude_Attrs = Conclude_Attrs
    { concludeId :: (Maybe String)
    , concludeStyle :: (Maybe String)
    , concludeMid :: (Maybe String)
    } deriving (Eq,Show)
data Hypothesis = Hypothesis Hypothesis_Attrs [Symbol] [CMP]
			     (Maybe FMP)
		deriving (Eq,Show)
data Hypothesis_Attrs = Hypothesis_Attrs
    { hypothesisId :: String
    , hypothesisStyle :: (Maybe String)
    , hypothesisMid :: (Maybe String)
    , hypothesisDischarged_in :: String
    } deriving (Eq,Show)
data Method = Method Method_Attrs [(OMOBJ)]
	    deriving (Eq,Show)
data Method_Attrs = Method_Attrs
    { methodXref :: String
    } deriving (Eq,Show)
data Premise = Premise
    { premiseXref :: String
    , premiseRank :: (Defaultable String)
    } deriving (Eq,Show)
data Example = Example Example_Attrs (Maybe Metadata) [Symbol]
		       [CMP] [(OMOBJ)]
	     deriving (Eq,Show)
data Example_Attrs = Example_Attrs
    { exampleType :: (Maybe Example_type)
    , exampleAssertion :: (Maybe String)
    , exampleId :: String
    , exampleStyle :: (Maybe String)
    , exampleMid :: (Maybe String)
    , exampleFor :: String
    } deriving (Eq,Show)
data Example_type = Example_type_for  |  Example_type_against
		  deriving (Eq,Show)
data Theory = Theory Theory_Attrs (Maybe Metadata) [Commonname]
		     [CMP]
		     [(OneOf24 Symbol Axiom Definition Adt Imports Inclusion Omtext Type Assertion Alternative Example Proof Proofobject Exercise Solution Omlet Private Code Presentation Omstyle Theory Omgroup Ignore Ref)]
	    deriving (Eq,Show)
data Theory_Attrs = Theory_Attrs
    { theoryId :: String
    , theoryStyle :: (Maybe String)
    } deriving (Eq,Show)
data Imports = Imports Imports_Attrs [CMP] (Maybe Morphism)
	     deriving (Eq,Show)
data Imports_Attrs = Imports_Attrs
    { importsId :: String
    , importsStyle :: (Maybe String)
    , importsMid :: (Maybe String)
    , importsFrom :: String
    , importsHiding :: (Maybe String)
    , importsType :: (Defaultable Imports_type)
    } deriving (Eq,Show)
data Imports_type = Imports_type_local  |  Imports_type_global
		  deriving (Eq,Show)
data Morphism = Morphism Morphism_Attrs [Requation]
	      deriving (Eq,Show)
data Morphism_Attrs = Morphism_Attrs
    { morphismId :: (Maybe String)
    , morphismStyle :: (Maybe String)
    , morphismMid :: (Maybe String)
    , morphismBase :: (Maybe String)
    } deriving (Eq,Show)
data Inclusion = Inclusion
    { inclusionVia :: String
    , inclusionMid :: (Maybe String)
    } deriving (Eq,Show)
data Theory_inclusion = Theory_inclusion Theory_inclusion_Attrs
					 ((Maybe Metadata),[Symbol],[CMP],[FMP]) (Maybe Morphism)
		      deriving (Eq,Show)
data Theory_inclusion_Attrs = Theory_inclusion_Attrs
    { theory_inclusionId :: String
    , theory_inclusionStyle :: (Maybe String)
    , theory_inclusionMid :: (Maybe String)
    , theory_inclusionFrom :: String
    , theory_inclusionTo :: String
    } deriving (Eq,Show)
data Decomposition = Decomposition
    { decompositionId :: String
    , decompositionStyle :: (Maybe String)
    , decompositionMid :: (Maybe String)
    , decompositionFor :: String
    , decompositionLinks :: String
    } deriving (Eq,Show)
data Axiom_inclusion = Axiom_inclusion Axiom_inclusion_Attrs
				       ((Maybe Metadata),[Symbol],[CMP],[FMP]) (Maybe Morphism)
				       (OneOf2 Path_just [Obligation])
		     deriving (Eq,Show)
data Axiom_inclusion_Attrs = Axiom_inclusion_Attrs
    { axiom_inclusionId :: String
    , axiom_inclusionStyle :: (Maybe String)
    , axiom_inclusionMid :: (Maybe String)
    , axiom_inclusionFrom :: String
    , axiom_inclusionTo :: String
    } deriving (Eq,Show)
data Path_just = Path_just
    { path_justLocal :: String
    , path_justGlobals :: String
    , path_justMid :: (Maybe String)
    } deriving (Eq,Show)
data Obligation = Obligation
    { obligationInduced_by :: String
    , obligationAssertion :: String
    , obligationMid :: (Maybe String)
    } deriving (Eq,Show)
data Exercise = Exercise Exercise_Attrs
			 ((Maybe Metadata),[Symbol],[CMP],[FMP]) (Maybe Hint)
			 (OneOf2 [Solution] [Mc])
	      deriving (Eq,Show)
data Exercise_Attrs = Exercise_Attrs
    { exerciseId :: String
    , exerciseStyle :: (Maybe String)
    , exerciseMid :: (Maybe String)
    , exerciseFor :: (Maybe String)
    } deriving (Eq,Show)
data Hint = Hint Hint_Attrs (Maybe Metadata) [Symbol] [CMP] [FMP]
	  deriving (Eq,Show)
data Hint_Attrs = Hint_Attrs
    { hintId :: (Maybe String)
    , hintStyle :: (Maybe String)
    , hintMid :: (Maybe String)
    } deriving (Eq,Show)
data Solution = Solution Solution_Attrs
			 ((Maybe Metadata),[Symbol],[CMP],[FMP])
			 (Maybe (OneOf2 Proof Proofobject))
	      deriving (Eq,Show)
data Solution_Attrs = Solution_Attrs
    { solutionFor :: (Maybe String)
    , solutionId :: (Maybe String)
    , solutionStyle :: (Maybe String)
    , solutionMid :: (Maybe String)
    } deriving (Eq,Show)
data Mc = Mc Mc_Attrs [Symbol] Choice (Maybe Hint) Answer
	deriving (Eq,Show)
data Mc_Attrs = Mc_Attrs
    { mcId :: (Maybe String)
    , mcStyle :: (Maybe String)
    , mcMid :: (Maybe String)
    } deriving (Eq,Show)
data Choice = Choice Choice_Attrs (Maybe Metadata) [Symbol] [CMP]
		     [FMP]
	    deriving (Eq,Show)
data Choice_Attrs = Choice_Attrs
    { choiceId :: (Maybe String)
    , choiceStyle :: (Maybe String)
    , choiceMid :: (Maybe String)
    } deriving (Eq,Show)
data Answer = Answer Answer_Attrs (Maybe Metadata) [Symbol] [CMP]
		     [FMP]
	    deriving (Eq,Show)
data Answer_Attrs = Answer_Attrs
    { answerVerdict :: Answer_verdict
    , answerId :: (Maybe String)
    , answerStyle :: (Maybe String)
    , answerMid :: (Maybe String)
    } deriving (Eq,Show)
data Answer_verdict = Answer_verdict_true  |  Answer_verdict_false
		    deriving (Eq,Show)
data Omlet = Omlet Omlet_Attrs [Omlet_]
	   deriving (Eq,Show)
data Omlet_Attrs = Omlet_Attrs
    { omletId :: (Maybe String)
    , omletStyle :: (Maybe String)
    , omletMid :: (Maybe String)
    , omletAction :: (Maybe String)
    , omletType :: (Maybe String)
    , omletData :: (Maybe String)
    , omletArgstr :: (Maybe String)
    , omletFunction :: (Maybe String)
    , omletWidth :: (Maybe String)
    , omletHeight :: (Maybe String)
    , omletXmlns :: (Defaultable String)
    , omletXmlns'xsi :: (Defaultable String)
    , omletXsi'schemaLocation :: (Defaultable String)
    } deriving (Eq,Show)
data Omlet_ = Omlet_Str String
	    | Omlet_OMOBJ OMOBJ
	    | Omlet_Omlet Omlet
	    | Omlet_With With
	    | Omlet_Ref Ref
	    | Omlet_Ignore Ignore
	    deriving (Eq,Show)
data Private = Private Private_Attrs (Maybe Metadata) (List1 Data)
	     deriving (Eq,Show)
data Private_Attrs = Private_Attrs
    { privateId :: String
    , privateStyle :: (Maybe String)
    , privateMid :: (Maybe String)
    , privateFor :: (Maybe String)
    , privateTheory :: (Maybe String)
    , privatePto :: (Maybe String)
    , privatePto_version :: (Maybe String)
    , privateType :: (Maybe String)
    , privateRequires :: (Maybe String)
    , privateReplaces :: (Maybe String)
    } deriving (Eq,Show)
data Code = Code Code_Attrs (Maybe Metadata) (List1 Data)
		 (Maybe Input) (Maybe Output) (Maybe Effect)
	  deriving (Eq,Show)
data Code_Attrs = Code_Attrs
    { codeId :: String
    , codeStyle :: (Maybe String)
    , codeMid :: (Maybe String)
    , codeFor :: (Maybe String)
    , codeTheory :: (Maybe String)
    , codePto :: (Maybe String)
    , codePto_version :: (Maybe String)
    , codeType :: (Maybe String)
    , codeRequires :: (Maybe String)
    , codeClassid :: (Maybe String)
    , codeCodebase :: (Maybe String)
    } deriving (Eq,Show)
data Input = Input Input_Attrs [CMP] [FMP]
	   deriving (Eq,Show)
data Input_Attrs = Input_Attrs
    { inputMid :: (Maybe String)
    } deriving (Eq,Show)
data Output = Output Output_Attrs [CMP] [FMP]
	    deriving (Eq,Show)
data Output_Attrs = Output_Attrs
    { outputMid :: (Maybe String)
    } deriving (Eq,Show)
data Effect = Effect Effect_Attrs [CMP] [FMP]
	    deriving (Eq,Show)
data Effect_Attrs = Effect_Attrs
    { effectMid :: (Maybe String)
    } deriving (Eq,Show)
data Data = Data Data_Attrs ANYContent
	  deriving (Eq,Show)
data Data_Attrs = Data_Attrs
    { dataMid :: (Maybe String)
    , dataFormat :: (Maybe String)
    , dataHref :: (Maybe String)
    , dataSize :: (Maybe String)
    } deriving (Eq,Show)
data Ignore = Ignore Ignore_Attrs ANYContent
	    deriving (Eq,Show)
data Ignore_Attrs = Ignore_Attrs
    { ignoreType :: (Maybe String)
    , ignoreComment :: (Maybe String)
    } deriving (Eq,Show)
data Presentation = Presentation Presentation_Attrs [Presentation_]
		  deriving (Eq,Show)
data Presentation_Attrs = Presentation_Attrs
    { presentationId :: (Maybe String)
    , presentationStyle :: (Maybe String)
    , presentationMid :: (Maybe String)
    , presentationXref :: (Maybe String)
    , presentationFor :: String
    , presentationParent :: (Maybe Presentation_parent)
    , presentationFixity :: (Defaultable Presentation_fixity)
    , presentationLbrack :: (Defaultable String)
    , presentationRbrack :: (Defaultable String)
    , presentationSeparator :: (Defaultable String)
    , presentationBracket_style :: (Defaultable Presentation_bracket_style)
    , presentationPrecedence :: (Defaultable String)
    , presentationCrossref_symbol :: (Defaultable Presentation_crossref_symbol)
    , presentationTheory :: (Maybe String)
    } deriving (Eq,Show)
data Presentation_ = Presentation_Use Use
		   | Presentation_Xslt Xslt
		   | Presentation_Style Style
		   deriving (Eq,Show)
data Presentation_parent = Presentation_parent_OMA  | 
			   Presentation_parent_OMBIND  |  Presentation_parent_OMATTR
			 deriving (Eq,Show)
data Presentation_fixity = Presentation_fixity_prefix  | 
			   Presentation_fixity_infix  |  Presentation_fixity_postfix  | 
			   Presentation_fixity_assoc
			 deriving (Eq,Show)
data Presentation_bracket_style = Presentation_bracket_style_lisp
				   |  Presentation_bracket_style_math
				deriving (Eq,Show)
data Presentation_crossref_symbol = Presentation_crossref_symbol_no
				     |  Presentation_crossref_symbol_yes  | 
				    Presentation_crossref_symbol_brackets  | 
				    Presentation_crossref_symbol_separator  | 
				    Presentation_crossref_symbol_lbrack  | 
				    Presentation_crossref_symbol_rbrack  | 
				    Presentation_crossref_symbol_all
				  deriving (Eq,Show)
data Use = Use Use_Attrs String
	 deriving (Eq,Show)
data Use_Attrs = Use_Attrs
    { useFormat :: String
    , useRequires :: (Maybe String)
    , useXml'lang :: (Maybe String)
    , useBracket_style :: (Maybe Use_bracket_style)
    , useFixity :: (Maybe Use_fixity)
    , useLbrack :: (Maybe String)
    , useRbrack :: (Maybe String)
    , useLarg_group :: (Maybe String)
    , useRarg_group :: (Maybe String)
    , useSeparator :: (Maybe String)
    , useElement :: (Maybe String)
    , useAttributes :: (Maybe String)
    , useCrossref_symbol :: (Maybe Use_crossref_symbol)
    } deriving (Eq,Show)
data Use_bracket_style = Use_bracket_style_lisp  | 
			 Use_bracket_style_math
		       deriving (Eq,Show)
data Use_fixity = Use_fixity_prefix  |  Use_fixity_infix  | 
		  Use_fixity_postfix  |  Use_fixity_assoc
		deriving (Eq,Show)
data Use_crossref_symbol = Use_crossref_symbol_no  | 
			   Use_crossref_symbol_yes  |  Use_crossref_symbol_brackets  | 
			   Use_crossref_symbol_separator  |  Use_crossref_symbol_lbrack  | 
			   Use_crossref_symbol_rbrack  |  Use_crossref_symbol_all
			 deriving (Eq,Show)
data Omstyle = Omstyle Omstyle_Attrs [Omstyle_]
	     deriving (Eq,Show)
data Omstyle_Attrs = Omstyle_Attrs
    { omstyleId :: (Maybe String)
    , omstyleStyle :: (Maybe String)
    , omstyleMid :: (Maybe String)
    , omstyleXref :: (Maybe String)
    , omstyleFor :: (Maybe String)
    , omstyleElement :: String
    } deriving (Eq,Show)
data Omstyle_ = Omstyle_Xslt Xslt
	      | Omstyle_Style Style
	      deriving (Eq,Show)
data Xslt = Xslt Xslt_Attrs String
	  deriving (Eq,Show)
data Xslt_Attrs = Xslt_Attrs
    { xsltFormat :: String
    , xsltRequires :: (Maybe String)
    , xsltXml'lang :: (Maybe String)
    } deriving (Eq,Show)
data Style = Style Style_Attrs [Style_]
	   deriving (Eq,Show)
data Style_Attrs = Style_Attrs
    { styleFormat :: String
    , styleRequires :: (Maybe String)
    , styleXml'lang :: (Maybe String)
    } deriving (Eq,Show)
data Style_ = Style_Element Omdoc.Element
	    | Style_Text Text
	    | Style_Recurse Recurse
	    | Style_Value_of Value_of
	    deriving (Eq,Show)
data Omdoc.Element = Omdoc.Element Element_Attrs [Element_]
	     deriving (Eq,Show)
data Element_Attrs = Element_Attrs
    { elementName :: String
    } deriving (Eq,Show)
data Element_ = Element_Attribute Attribute
	      | Element_Element Omdoc.Element
	      | Element_Text Text
	      | Element_Recurse Recurse
	      | Element_Value_of Value_of
	      deriving (Eq,Show)
data Attribute = Attribute Attribute_Attrs [Attribute_]
	       deriving (Eq,Show)
data Attribute_Attrs = Attribute_Attrs
    { attributeName :: String
    } deriving (Eq,Show)
data Attribute_ = Attribute_Str String
		| Attribute_Value_of Value_of
		| Attribute_Text Text
		deriving (Eq,Show)
newtype Text = Text String 		deriving (Eq,Show)
data Value_of = Value_of
    { value_ofSelect :: String
    } deriving (Eq,Show)
data Recurse = Recurse
    { recurseSelect :: (Maybe String)
    } deriving (Eq,Show)
data OMS = OMS
    { oMSName :: String
    , oMSCd :: String
    , oMSStyle :: (Maybe String)
    } deriving (Eq,Show)
data OMV = OMV
    { oMVName :: String
    , oMVStyle :: (Maybe String)
    } deriving (Eq,Show)
data OMI = OMI OMI_Attrs String
	 deriving (Eq,Show)
data OMI_Attrs = OMI_Attrs
    { oMIMid :: (Maybe String)
    , oMIStyle :: (Maybe String)
    , oMIId :: (Maybe String)
    , oMIXref :: (Maybe String)
    } deriving (Eq,Show)
data OMB = OMB OMB_Attrs String
	 deriving (Eq,Show)
data OMB_Attrs = OMB_Attrs
    { oMBMid :: (Maybe String)
    , oMBStyle :: (Maybe String)
    , oMBId :: (Maybe String)
    , oMBXref :: (Maybe String)
    } deriving (Eq,Show)
data OMSTR = OMSTR OMSTR_Attrs String
	   deriving (Eq,Show)
data OMSTR_Attrs = OMSTR_Attrs
    { oMSTRMid :: (Maybe String)
    , oMSTRStyle :: (Maybe String)
    , oMSTRId :: (Maybe String)
    , oMSTRXref :: (Maybe String)
    } deriving (Eq,Show)
data OMF = OMF
    { oMFDec :: (Maybe String)
    , oMFHex :: (Maybe String)
    , oMFMid :: (Maybe String)
    , oMFStyle :: (Maybe String)
    , oMFId :: (Maybe String)
    , oMFXref :: (Maybe String)
    } deriving (Eq,Show)
data OMA = OMA OMA_Attrs [OMA_]
	 deriving (Eq,Show)
data OMA_Attrs = OMA_Attrs
    { oMAMid :: (Maybe String)
    , oMAStyle :: (Maybe String)
    , oMAId :: (Maybe String)
    , oMAXref :: (Maybe String)
    } deriving (Eq,Show)
data OMA_ = OMA_OMS OMS
	  | OMA_OMV OMV
	  | OMA_OMI OMI
	  | OMA_OMB OMB
	  | OMA_OMSTR OMSTR
	  | OMA_OMF OMF
	  | OMA_OMA OMA
	  | OMA_OMBIND OMBIND
	  | OMA_OME OME
	  | OMA_OMATTR OMATTR
	  deriving (Eq,Show)
data OMBIND = OMBIND OMBIND_Attrs (Maybe OMBIND_)
	    deriving (Eq,Show)
data OMBIND_Attrs = OMBIND_Attrs
    { oMBINDMid :: (Maybe String)
    , oMBINDStyle :: (Maybe String)
    , oMBINDId :: (Maybe String)
    , oMBINDXref :: (Maybe String)
    } deriving (Eq,Show)
data OMBIND_ = OMBIND_ (OneOf10 OMS OMV OMI OMB OMSTR OMF OMA OMBIND OME OMATTR)
		       OMBVAR (OneOf10 OMS OMV OMI OMB OMSTR OMF OMA OMBIND OME OMATTR)
	     deriving (Eq,Show)
newtype OMBVAR = OMBVAR (List1 OMBVAR_) 		deriving (Eq,Show)
data OMBVAR_ = OMBVAR_OMV OMV
	     | OMBVAR_OMATTR OMATTR
	     deriving (Eq,Show)
data OME = OME OMS
	       [(OneOf10 OMS OMV OMI OMB OMSTR OMF OMA OMBIND OME OMATTR)]
	 deriving (Eq,Show)
data OMATTR = OMATTR OMATTR_Attrs (Maybe OMATTR_)
	    deriving (Eq,Show)
data OMATTR_Attrs = OMATTR_Attrs
    { oMATTRMid :: (Maybe String)
    , oMATTRStyle :: (Maybe String)
    , oMATTRId :: (Maybe String)
    , oMATTRXref :: (Maybe String)
    } deriving (Eq,Show)
data OMATTR_ = OMATTR_ OMATP
		       (OneOf10 OMS OMV OMI OMB OMSTR OMF OMA OMBIND OME OMATTR)
	     deriving (Eq,Show)
newtype OMATP = OMATP (List1 OMATP_) 		deriving (Eq,Show)
data OMATP_ = OMATP_ OMS
		     (OneOf10 OMS OMV OMI OMB OMSTR OMF OMA OMBIND OME OMATTR)
	    deriving (Eq,Show)
data OMOBJ = OMOBJ OMOBJ_Attrs (Maybe OMOBJ_)
	   deriving (Eq,Show)
data OMOBJ_Attrs = OMOBJ_Attrs
    { oMOBJXmlns :: (Defaultable String)
    , oMOBJMid :: (Maybe String)
    , oMOBJStyle :: (Maybe String)
    , oMOBJId :: (Maybe String)
    , oMOBJXref :: (Maybe String)
    } deriving (Eq,Show)
data OMOBJ_ = OMOBJ_OMS OMS
	    | OMOBJ_OMV OMV
	    | OMOBJ_OMI OMI
	    | OMOBJ_OMB OMB
	    | OMOBJ_OMSTR OMSTR
	    | OMOBJ_OMF OMF
	    | OMOBJ_OMA OMA
	    | OMOBJ_OMBIND OMBIND
	    | OMOBJ_OME OME
	    | OMOBJ_OMATTR OMATTR
	    deriving (Eq,Show)
data Metadata = Metadata Metadata_Attrs
			 [(OneOf14 Contributor Creator Subject Title Description Publisher Date TypeMeta Format Identifier Source Language Relation Rights)]
			 (Maybe Extradata)
	      deriving (Eq,Show)
data Metadata_Attrs = Metadata_Attrs
    { metadataId :: (Maybe String)
    , metadataStyle :: (Maybe String)
    , metadataMid :: (Maybe String)
    , metadataInherits :: (Maybe String)
    } deriving (Eq,Show)
data Contributor = Contributor Contributor_Attrs String
		 deriving (Eq,Show)
data Contributor_Attrs = Contributor_Attrs
    { contributorXmlns :: (Defaultable String)
    , contributorId :: (Maybe String)
    , contributorStyle :: (Maybe String)
    , contributorMid :: (Maybe String)
    , contributorXml'lang :: (Defaultable Contributor_xml'lang)
    , contributorRole :: (Defaultable Contributor_role)
    } deriving (Eq,Show)
data Contributor_xml'lang = Contributor_xml'lang_aa  | 
			    Contributor_xml'lang_ab  |  Contributor_xml'lang_af  | 
			    Contributor_xml'lang_am  |  Contributor_xml'lang_ar  | 
			    Contributor_xml'lang_as  |  Contributor_xml'lang_ay  | 
			    Contributor_xml'lang_az  |  Contributor_xml'lang_ba  | 
			    Contributor_xml'lang_be  |  Contributor_xml'lang_bg  | 
			    Contributor_xml'lang_bh  |  Contributor_xml'lang_bi  | 
			    Contributor_xml'lang_bn  |  Contributor_xml'lang_bo  | 
			    Contributor_xml'lang_br  |  Contributor_xml'lang_ca  | 
			    Contributor_xml'lang_co  |  Contributor_xml'lang_cs  | 
			    Contributor_xml'lang_cy  |  Contributor_xml'lang_da  | 
			    Contributor_xml'lang_de  |  Contributor_xml'lang_dz  | 
			    Contributor_xml'lang_el  |  Contributor_xml'lang_en  | 
			    Contributor_xml'lang_eo  |  Contributor_xml'lang_es  | 
			    Contributor_xml'lang_et  |  Contributor_xml'lang_eu  | 
			    Contributor_xml'lang_fa  |  Contributor_xml'lang_fi  | 
			    Contributor_xml'lang_fj  |  Contributor_xml'lang_fo  | 
			    Contributor_xml'lang_fr  |  Contributor_xml'lang_fy  | 
			    Contributor_xml'lang_ga  |  Contributor_xml'lang_gd  | 
			    Contributor_xml'lang_gl  |  Contributor_xml'lang_gn  | 
			    Contributor_xml'lang_gu  |  Contributor_xml'lang_ha  | 
			    Contributor_xml'lang_he  |  Contributor_xml'lang_hi  | 
			    Contributor_xml'lang_hr  |  Contributor_xml'lang_hu  | 
			    Contributor_xml'lang_hy  |  Contributor_xml'lang_ia  | 
			    Contributor_xml'lang_ie  |  Contributor_xml'lang_ik  | 
			    Contributor_xml'lang_id  |  Contributor_xml'lang_is  | 
			    Contributor_xml'lang_it  |  Contributor_xml'lang_iu  | 
			    Contributor_xml'lang_ja  |  Contributor_xml'lang_jv  | 
			    Contributor_xml'lang_ka  |  Contributor_xml'lang_kk  | 
			    Contributor_xml'lang_kl  |  Contributor_xml'lang_km  | 
			    Contributor_xml'lang_kn  |  Contributor_xml'lang_ko  | 
			    Contributor_xml'lang_ks  |  Contributor_xml'lang_ku  | 
			    Contributor_xml'lang_ky  |  Contributor_xml'lang_la  | 
			    Contributor_xml'lang_ln  |  Contributor_xml'lang_lo  | 
			    Contributor_xml'lang_lt  |  Contributor_xml'lang_lv  | 
			    Contributor_xml'lang_mg  |  Contributor_xml'lang_mi  | 
			    Contributor_xml'lang_mk  |  Contributor_xml'lang_ml  | 
			    Contributor_xml'lang_mn  |  Contributor_xml'lang_mo  | 
			    Contributor_xml'lang_mr  |  Contributor_xml'lang_ms  | 
			    Contributor_xml'lang_mt  |  Contributor_xml'lang_my  | 
			    Contributor_xml'lang_na  |  Contributor_xml'lang_ne  | 
			    Contributor_xml'lang_nl  |  Contributor_xml'lang_no  | 
			    Contributor_xml'lang_oc  |  Contributor_xml'lang_om  | 
			    Contributor_xml'lang_or  |  Contributor_xml'lang_pa  | 
			    Contributor_xml'lang_pl  |  Contributor_xml'lang_ps  | 
			    Contributor_xml'lang_pt  |  Contributor_xml'lang_qu  | 
			    Contributor_xml'lang_rm  |  Contributor_xml'lang_rn  | 
			    Contributor_xml'lang_ro  |  Contributor_xml'lang_ru  | 
			    Contributor_xml'lang_rw  |  Contributor_xml'lang_sa  | 
			    Contributor_xml'lang_sd  |  Contributor_xml'lang_sg  | 
			    Contributor_xml'lang_sh  |  Contributor_xml'lang_si  | 
			    Contributor_xml'lang_sk  |  Contributor_xml'lang_sl  | 
			    Contributor_xml'lang_sm  |  Contributor_xml'lang_sn  | 
			    Contributor_xml'lang_so  |  Contributor_xml'lang_sq  | 
			    Contributor_xml'lang_sr  |  Contributor_xml'lang_ss  | 
			    Contributor_xml'lang_st  |  Contributor_xml'lang_su  | 
			    Contributor_xml'lang_sv  |  Contributor_xml'lang_sw  | 
			    Contributor_xml'lang_ta  |  Contributor_xml'lang_te  | 
			    Contributor_xml'lang_tg  |  Contributor_xml'lang_th  | 
			    Contributor_xml'lang_ti  |  Contributor_xml'lang_tk  | 
			    Contributor_xml'lang_tl  |  Contributor_xml'lang_tn  | 
			    Contributor_xml'lang_to  |  Contributor_xml'lang_tr  | 
			    Contributor_xml'lang_ts  |  Contributor_xml'lang_tt  | 
			    Contributor_xml'lang_tw  |  Contributor_xml'lang_ug  | 
			    Contributor_xml'lang_uk  |  Contributor_xml'lang_ur  | 
			    Contributor_xml'lang_uz  |  Contributor_xml'lang_vi  | 
			    Contributor_xml'lang_vo  |  Contributor_xml'lang_wo  | 
			    Contributor_xml'lang_xh  |  Contributor_xml'lang_yi  | 
			    Contributor_xml'lang_yo  |  Contributor_xml'lang_za  | 
			    Contributor_xml'lang_zh  |  Contributor_xml'lang_zu
			  deriving (Eq,Show)
data Contributor_role = Contributor_role_aut  | 
			Contributor_role_ant  |  Contributor_role_clb  | 
			Contributor_role_edt  |  Contributor_role_ths  | 
			Contributor_role_trc  |  Contributor_role_trl
		      deriving (Eq,Show)
data Creator = Creator Creator_Attrs String
	     deriving (Eq,Show)
data Creator_Attrs = Creator_Attrs
    { creatorXmlns :: (Defaultable String)
    , creatorId :: (Maybe String)
    , creatorStyle :: (Maybe String)
    , creatorMid :: (Maybe String)
    , creatorXml'lang :: (Defaultable Creator_xml'lang)
    , creatorRole :: (Defaultable Creator_role)
    } deriving (Eq,Show)
data Creator_xml'lang = Creator_xml'lang_aa  |  Creator_xml'lang_ab
			 |  Creator_xml'lang_af  |  Creator_xml'lang_am  | 
			Creator_xml'lang_ar  |  Creator_xml'lang_as  |  Creator_xml'lang_ay
			 |  Creator_xml'lang_az  |  Creator_xml'lang_ba  | 
			Creator_xml'lang_be  |  Creator_xml'lang_bg  |  Creator_xml'lang_bh
			 |  Creator_xml'lang_bi  |  Creator_xml'lang_bn  | 
			Creator_xml'lang_bo  |  Creator_xml'lang_br  |  Creator_xml'lang_ca
			 |  Creator_xml'lang_co  |  Creator_xml'lang_cs  | 
			Creator_xml'lang_cy  |  Creator_xml'lang_da  |  Creator_xml'lang_de
			 |  Creator_xml'lang_dz  |  Creator_xml'lang_el  | 
			Creator_xml'lang_en  |  Creator_xml'lang_eo  |  Creator_xml'lang_es
			 |  Creator_xml'lang_et  |  Creator_xml'lang_eu  | 
			Creator_xml'lang_fa  |  Creator_xml'lang_fi  |  Creator_xml'lang_fj
			 |  Creator_xml'lang_fo  |  Creator_xml'lang_fr  | 
			Creator_xml'lang_fy  |  Creator_xml'lang_ga  |  Creator_xml'lang_gd
			 |  Creator_xml'lang_gl  |  Creator_xml'lang_gn  | 
			Creator_xml'lang_gu  |  Creator_xml'lang_ha  |  Creator_xml'lang_he
			 |  Creator_xml'lang_hi  |  Creator_xml'lang_hr  | 
			Creator_xml'lang_hu  |  Creator_xml'lang_hy  |  Creator_xml'lang_ia
			 |  Creator_xml'lang_ie  |  Creator_xml'lang_ik  | 
			Creator_xml'lang_id  |  Creator_xml'lang_is  |  Creator_xml'lang_it
			 |  Creator_xml'lang_iu  |  Creator_xml'lang_ja  | 
			Creator_xml'lang_jv  |  Creator_xml'lang_ka  |  Creator_xml'lang_kk
			 |  Creator_xml'lang_kl  |  Creator_xml'lang_km  | 
			Creator_xml'lang_kn  |  Creator_xml'lang_ko  |  Creator_xml'lang_ks
			 |  Creator_xml'lang_ku  |  Creator_xml'lang_ky  | 
			Creator_xml'lang_la  |  Creator_xml'lang_ln  |  Creator_xml'lang_lo
			 |  Creator_xml'lang_lt  |  Creator_xml'lang_lv  | 
			Creator_xml'lang_mg  |  Creator_xml'lang_mi  |  Creator_xml'lang_mk
			 |  Creator_xml'lang_ml  |  Creator_xml'lang_mn  | 
			Creator_xml'lang_mo  |  Creator_xml'lang_mr  |  Creator_xml'lang_ms
			 |  Creator_xml'lang_mt  |  Creator_xml'lang_my  | 
			Creator_xml'lang_na  |  Creator_xml'lang_ne  |  Creator_xml'lang_nl
			 |  Creator_xml'lang_no  |  Creator_xml'lang_oc  | 
			Creator_xml'lang_om  |  Creator_xml'lang_or  |  Creator_xml'lang_pa
			 |  Creator_xml'lang_pl  |  Creator_xml'lang_ps  | 
			Creator_xml'lang_pt  |  Creator_xml'lang_qu  |  Creator_xml'lang_rm
			 |  Creator_xml'lang_rn  |  Creator_xml'lang_ro  | 
			Creator_xml'lang_ru  |  Creator_xml'lang_rw  |  Creator_xml'lang_sa
			 |  Creator_xml'lang_sd  |  Creator_xml'lang_sg  | 
			Creator_xml'lang_sh  |  Creator_xml'lang_si  |  Creator_xml'lang_sk
			 |  Creator_xml'lang_sl  |  Creator_xml'lang_sm  | 
			Creator_xml'lang_sn  |  Creator_xml'lang_so  |  Creator_xml'lang_sq
			 |  Creator_xml'lang_sr  |  Creator_xml'lang_ss  | 
			Creator_xml'lang_st  |  Creator_xml'lang_su  |  Creator_xml'lang_sv
			 |  Creator_xml'lang_sw  |  Creator_xml'lang_ta  | 
			Creator_xml'lang_te  |  Creator_xml'lang_tg  |  Creator_xml'lang_th
			 |  Creator_xml'lang_ti  |  Creator_xml'lang_tk  | 
			Creator_xml'lang_tl  |  Creator_xml'lang_tn  |  Creator_xml'lang_to
			 |  Creator_xml'lang_tr  |  Creator_xml'lang_ts  | 
			Creator_xml'lang_tt  |  Creator_xml'lang_tw  |  Creator_xml'lang_ug
			 |  Creator_xml'lang_uk  |  Creator_xml'lang_ur  | 
			Creator_xml'lang_uz  |  Creator_xml'lang_vi  |  Creator_xml'lang_vo
			 |  Creator_xml'lang_wo  |  Creator_xml'lang_xh  | 
			Creator_xml'lang_yi  |  Creator_xml'lang_yo  |  Creator_xml'lang_za
			 |  Creator_xml'lang_zh  |  Creator_xml'lang_zu
		      deriving (Eq,Show)
data Creator_role = Creator_role_aut  |  Creator_role_ant  | 
		    Creator_role_clb  |  Creator_role_edt  |  Creator_role_ths  | 
		    Creator_role_trc  |  Creator_role_trl
		  deriving (Eq,Show)
data Title = Title Title_Attrs [Title_]
	   deriving (Eq,Show)
data Title_Attrs = Title_Attrs
    { titleXmlns :: (Defaultable String)
    , titleXml'lang :: (Defaultable Title_xml'lang)
    } deriving (Eq,Show)
data Title_ = Title_Str String
	    | Title_OMOBJ OMOBJ
	    | Title_Omlet Omlet
	    | Title_With With
	    | Title_Ref Ref
	    | Title_Ignore Ignore
	    deriving (Eq,Show)
data Title_xml'lang = Title_xml'lang_aa  |  Title_xml'lang_ab  | 
		      Title_xml'lang_af  |  Title_xml'lang_am  |  Title_xml'lang_ar  | 
		      Title_xml'lang_as  |  Title_xml'lang_ay  |  Title_xml'lang_az  | 
		      Title_xml'lang_ba  |  Title_xml'lang_be  |  Title_xml'lang_bg  | 
		      Title_xml'lang_bh  |  Title_xml'lang_bi  |  Title_xml'lang_bn  | 
		      Title_xml'lang_bo  |  Title_xml'lang_br  |  Title_xml'lang_ca  | 
		      Title_xml'lang_co  |  Title_xml'lang_cs  |  Title_xml'lang_cy  | 
		      Title_xml'lang_da  |  Title_xml'lang_de  |  Title_xml'lang_dz  | 
		      Title_xml'lang_el  |  Title_xml'lang_en  |  Title_xml'lang_eo  | 
		      Title_xml'lang_es  |  Title_xml'lang_et  |  Title_xml'lang_eu  | 
		      Title_xml'lang_fa  |  Title_xml'lang_fi  |  Title_xml'lang_fj  | 
		      Title_xml'lang_fo  |  Title_xml'lang_fr  |  Title_xml'lang_fy  | 
		      Title_xml'lang_ga  |  Title_xml'lang_gd  |  Title_xml'lang_gl  | 
		      Title_xml'lang_gn  |  Title_xml'lang_gu  |  Title_xml'lang_ha  | 
		      Title_xml'lang_he  |  Title_xml'lang_hi  |  Title_xml'lang_hr  | 
		      Title_xml'lang_hu  |  Title_xml'lang_hy  |  Title_xml'lang_ia  | 
		      Title_xml'lang_ie  |  Title_xml'lang_ik  |  Title_xml'lang_id  | 
		      Title_xml'lang_is  |  Title_xml'lang_it  |  Title_xml'lang_iu  | 
		      Title_xml'lang_ja  |  Title_xml'lang_jv  |  Title_xml'lang_ka  | 
		      Title_xml'lang_kk  |  Title_xml'lang_kl  |  Title_xml'lang_km  | 
		      Title_xml'lang_kn  |  Title_xml'lang_ko  |  Title_xml'lang_ks  | 
		      Title_xml'lang_ku  |  Title_xml'lang_ky  |  Title_xml'lang_la  | 
		      Title_xml'lang_ln  |  Title_xml'lang_lo  |  Title_xml'lang_lt  | 
		      Title_xml'lang_lv  |  Title_xml'lang_mg  |  Title_xml'lang_mi  | 
		      Title_xml'lang_mk  |  Title_xml'lang_ml  |  Title_xml'lang_mn  | 
		      Title_xml'lang_mo  |  Title_xml'lang_mr  |  Title_xml'lang_ms  | 
		      Title_xml'lang_mt  |  Title_xml'lang_my  |  Title_xml'lang_na  | 
		      Title_xml'lang_ne  |  Title_xml'lang_nl  |  Title_xml'lang_no  | 
		      Title_xml'lang_oc  |  Title_xml'lang_om  |  Title_xml'lang_or  | 
		      Title_xml'lang_pa  |  Title_xml'lang_pl  |  Title_xml'lang_ps  | 
		      Title_xml'lang_pt  |  Title_xml'lang_qu  |  Title_xml'lang_rm  | 
		      Title_xml'lang_rn  |  Title_xml'lang_ro  |  Title_xml'lang_ru  | 
		      Title_xml'lang_rw  |  Title_xml'lang_sa  |  Title_xml'lang_sd  | 
		      Title_xml'lang_sg  |  Title_xml'lang_sh  |  Title_xml'lang_si  | 
		      Title_xml'lang_sk  |  Title_xml'lang_sl  |  Title_xml'lang_sm  | 
		      Title_xml'lang_sn  |  Title_xml'lang_so  |  Title_xml'lang_sq  | 
		      Title_xml'lang_sr  |  Title_xml'lang_ss  |  Title_xml'lang_st  | 
		      Title_xml'lang_su  |  Title_xml'lang_sv  |  Title_xml'lang_sw  | 
		      Title_xml'lang_ta  |  Title_xml'lang_te  |  Title_xml'lang_tg  | 
		      Title_xml'lang_th  |  Title_xml'lang_ti  |  Title_xml'lang_tk  | 
		      Title_xml'lang_tl  |  Title_xml'lang_tn  |  Title_xml'lang_to  | 
		      Title_xml'lang_tr  |  Title_xml'lang_ts  |  Title_xml'lang_tt  | 
		      Title_xml'lang_tw  |  Title_xml'lang_ug  |  Title_xml'lang_uk  | 
		      Title_xml'lang_ur  |  Title_xml'lang_uz  |  Title_xml'lang_vi  | 
		      Title_xml'lang_vo  |  Title_xml'lang_wo  |  Title_xml'lang_xh  | 
		      Title_xml'lang_yi  |  Title_xml'lang_yo  |  Title_xml'lang_za  | 
		      Title_xml'lang_zh  |  Title_xml'lang_zu
		    deriving (Eq,Show)
data Subject = Subject Subject_Attrs [Subject_]
	     deriving (Eq,Show)
data Subject_Attrs = Subject_Attrs
    { subjectXmlns :: (Defaultable String)
    , subjectXml'lang :: (Defaultable Subject_xml'lang)
    } deriving (Eq,Show)
data Subject_ = Subject_Str String
	      | Subject_OMOBJ OMOBJ
	      | Subject_Omlet Omlet
	      | Subject_With With
	      | Subject_Ref Ref
	      | Subject_Ignore Ignore
	      deriving (Eq,Show)
data Subject_xml'lang = Subject_xml'lang_aa  |  Subject_xml'lang_ab
			 |  Subject_xml'lang_af  |  Subject_xml'lang_am  | 
			Subject_xml'lang_ar  |  Subject_xml'lang_as  |  Subject_xml'lang_ay
			 |  Subject_xml'lang_az  |  Subject_xml'lang_ba  | 
			Subject_xml'lang_be  |  Subject_xml'lang_bg  |  Subject_xml'lang_bh
			 |  Subject_xml'lang_bi  |  Subject_xml'lang_bn  | 
			Subject_xml'lang_bo  |  Subject_xml'lang_br  |  Subject_xml'lang_ca
			 |  Subject_xml'lang_co  |  Subject_xml'lang_cs  | 
			Subject_xml'lang_cy  |  Subject_xml'lang_da  |  Subject_xml'lang_de
			 |  Subject_xml'lang_dz  |  Subject_xml'lang_el  | 
			Subject_xml'lang_en  |  Subject_xml'lang_eo  |  Subject_xml'lang_es
			 |  Subject_xml'lang_et  |  Subject_xml'lang_eu  | 
			Subject_xml'lang_fa  |  Subject_xml'lang_fi  |  Subject_xml'lang_fj
			 |  Subject_xml'lang_fo  |  Subject_xml'lang_fr  | 
			Subject_xml'lang_fy  |  Subject_xml'lang_ga  |  Subject_xml'lang_gd
			 |  Subject_xml'lang_gl  |  Subject_xml'lang_gn  | 
			Subject_xml'lang_gu  |  Subject_xml'lang_ha  |  Subject_xml'lang_he
			 |  Subject_xml'lang_hi  |  Subject_xml'lang_hr  | 
			Subject_xml'lang_hu  |  Subject_xml'lang_hy  |  Subject_xml'lang_ia
			 |  Subject_xml'lang_ie  |  Subject_xml'lang_ik  | 
			Subject_xml'lang_id  |  Subject_xml'lang_is  |  Subject_xml'lang_it
			 |  Subject_xml'lang_iu  |  Subject_xml'lang_ja  | 
			Subject_xml'lang_jv  |  Subject_xml'lang_ka  |  Subject_xml'lang_kk
			 |  Subject_xml'lang_kl  |  Subject_xml'lang_km  | 
			Subject_xml'lang_kn  |  Subject_xml'lang_ko  |  Subject_xml'lang_ks
			 |  Subject_xml'lang_ku  |  Subject_xml'lang_ky  | 
			Subject_xml'lang_la  |  Subject_xml'lang_ln  |  Subject_xml'lang_lo
			 |  Subject_xml'lang_lt  |  Subject_xml'lang_lv  | 
			Subject_xml'lang_mg  |  Subject_xml'lang_mi  |  Subject_xml'lang_mk
			 |  Subject_xml'lang_ml  |  Subject_xml'lang_mn  | 
			Subject_xml'lang_mo  |  Subject_xml'lang_mr  |  Subject_xml'lang_ms
			 |  Subject_xml'lang_mt  |  Subject_xml'lang_my  | 
			Subject_xml'lang_na  |  Subject_xml'lang_ne  |  Subject_xml'lang_nl
			 |  Subject_xml'lang_no  |  Subject_xml'lang_oc  | 
			Subject_xml'lang_om  |  Subject_xml'lang_or  |  Subject_xml'lang_pa
			 |  Subject_xml'lang_pl  |  Subject_xml'lang_ps  | 
			Subject_xml'lang_pt  |  Subject_xml'lang_qu  |  Subject_xml'lang_rm
			 |  Subject_xml'lang_rn  |  Subject_xml'lang_ro  | 
			Subject_xml'lang_ru  |  Subject_xml'lang_rw  |  Subject_xml'lang_sa
			 |  Subject_xml'lang_sd  |  Subject_xml'lang_sg  | 
			Subject_xml'lang_sh  |  Subject_xml'lang_si  |  Subject_xml'lang_sk
			 |  Subject_xml'lang_sl  |  Subject_xml'lang_sm  | 
			Subject_xml'lang_sn  |  Subject_xml'lang_so  |  Subject_xml'lang_sq
			 |  Subject_xml'lang_sr  |  Subject_xml'lang_ss  | 
			Subject_xml'lang_st  |  Subject_xml'lang_su  |  Subject_xml'lang_sv
			 |  Subject_xml'lang_sw  |  Subject_xml'lang_ta  | 
			Subject_xml'lang_te  |  Subject_xml'lang_tg  |  Subject_xml'lang_th
			 |  Subject_xml'lang_ti  |  Subject_xml'lang_tk  | 
			Subject_xml'lang_tl  |  Subject_xml'lang_tn  |  Subject_xml'lang_to
			 |  Subject_xml'lang_tr  |  Subject_xml'lang_ts  | 
			Subject_xml'lang_tt  |  Subject_xml'lang_tw  |  Subject_xml'lang_ug
			 |  Subject_xml'lang_uk  |  Subject_xml'lang_ur  | 
			Subject_xml'lang_uz  |  Subject_xml'lang_vi  |  Subject_xml'lang_vo
			 |  Subject_xml'lang_wo  |  Subject_xml'lang_xh  | 
			Subject_xml'lang_yi  |  Subject_xml'lang_yo  |  Subject_xml'lang_za
			 |  Subject_xml'lang_zh  |  Subject_xml'lang_zu
		      deriving (Eq,Show)
data Description = Description Description_Attrs [Description_]
		 deriving (Eq,Show)
data Description_Attrs = Description_Attrs
    { descriptionXmlns :: (Defaultable String)
    , descriptionXml'lang :: (Defaultable Description_xml'lang)
    } deriving (Eq,Show)
data Description_ = Description_Str String
		  | Description_OMOBJ OMOBJ
		  | Description_Omlet Omlet
		  | Description_With With
		  | Description_Ref Ref
		  | Description_Ignore Ignore
		  deriving (Eq,Show)
data Description_xml'lang = Description_xml'lang_aa  | 
			    Description_xml'lang_ab  |  Description_xml'lang_af  | 
			    Description_xml'lang_am  |  Description_xml'lang_ar  | 
			    Description_xml'lang_as  |  Description_xml'lang_ay  | 
			    Description_xml'lang_az  |  Description_xml'lang_ba  | 
			    Description_xml'lang_be  |  Description_xml'lang_bg  | 
			    Description_xml'lang_bh  |  Description_xml'lang_bi  | 
			    Description_xml'lang_bn  |  Description_xml'lang_bo  | 
			    Description_xml'lang_br  |  Description_xml'lang_ca  | 
			    Description_xml'lang_co  |  Description_xml'lang_cs  | 
			    Description_xml'lang_cy  |  Description_xml'lang_da  | 
			    Description_xml'lang_de  |  Description_xml'lang_dz  | 
			    Description_xml'lang_el  |  Description_xml'lang_en  | 
			    Description_xml'lang_eo  |  Description_xml'lang_es  | 
			    Description_xml'lang_et  |  Description_xml'lang_eu  | 
			    Description_xml'lang_fa  |  Description_xml'lang_fi  | 
			    Description_xml'lang_fj  |  Description_xml'lang_fo  | 
			    Description_xml'lang_fr  |  Description_xml'lang_fy  | 
			    Description_xml'lang_ga  |  Description_xml'lang_gd  | 
			    Description_xml'lang_gl  |  Description_xml'lang_gn  | 
			    Description_xml'lang_gu  |  Description_xml'lang_ha  | 
			    Description_xml'lang_he  |  Description_xml'lang_hi  | 
			    Description_xml'lang_hr  |  Description_xml'lang_hu  | 
			    Description_xml'lang_hy  |  Description_xml'lang_ia  | 
			    Description_xml'lang_ie  |  Description_xml'lang_ik  | 
			    Description_xml'lang_id  |  Description_xml'lang_is  | 
			    Description_xml'lang_it  |  Description_xml'lang_iu  | 
			    Description_xml'lang_ja  |  Description_xml'lang_jv  | 
			    Description_xml'lang_ka  |  Description_xml'lang_kk  | 
			    Description_xml'lang_kl  |  Description_xml'lang_km  | 
			    Description_xml'lang_kn  |  Description_xml'lang_ko  | 
			    Description_xml'lang_ks  |  Description_xml'lang_ku  | 
			    Description_xml'lang_ky  |  Description_xml'lang_la  | 
			    Description_xml'lang_ln  |  Description_xml'lang_lo  | 
			    Description_xml'lang_lt  |  Description_xml'lang_lv  | 
			    Description_xml'lang_mg  |  Description_xml'lang_mi  | 
			    Description_xml'lang_mk  |  Description_xml'lang_ml  | 
			    Description_xml'lang_mn  |  Description_xml'lang_mo  | 
			    Description_xml'lang_mr  |  Description_xml'lang_ms  | 
			    Description_xml'lang_mt  |  Description_xml'lang_my  | 
			    Description_xml'lang_na  |  Description_xml'lang_ne  | 
			    Description_xml'lang_nl  |  Description_xml'lang_no  | 
			    Description_xml'lang_oc  |  Description_xml'lang_om  | 
			    Description_xml'lang_or  |  Description_xml'lang_pa  | 
			    Description_xml'lang_pl  |  Description_xml'lang_ps  | 
			    Description_xml'lang_pt  |  Description_xml'lang_qu  | 
			    Description_xml'lang_rm  |  Description_xml'lang_rn  | 
			    Description_xml'lang_ro  |  Description_xml'lang_ru  | 
			    Description_xml'lang_rw  |  Description_xml'lang_sa  | 
			    Description_xml'lang_sd  |  Description_xml'lang_sg  | 
			    Description_xml'lang_sh  |  Description_xml'lang_si  | 
			    Description_xml'lang_sk  |  Description_xml'lang_sl  | 
			    Description_xml'lang_sm  |  Description_xml'lang_sn  | 
			    Description_xml'lang_so  |  Description_xml'lang_sq  | 
			    Description_xml'lang_sr  |  Description_xml'lang_ss  | 
			    Description_xml'lang_st  |  Description_xml'lang_su  | 
			    Description_xml'lang_sv  |  Description_xml'lang_sw  | 
			    Description_xml'lang_ta  |  Description_xml'lang_te  | 
			    Description_xml'lang_tg  |  Description_xml'lang_th  | 
			    Description_xml'lang_ti  |  Description_xml'lang_tk  | 
			    Description_xml'lang_tl  |  Description_xml'lang_tn  | 
			    Description_xml'lang_to  |  Description_xml'lang_tr  | 
			    Description_xml'lang_ts  |  Description_xml'lang_tt  | 
			    Description_xml'lang_tw  |  Description_xml'lang_ug  | 
			    Description_xml'lang_uk  |  Description_xml'lang_ur  | 
			    Description_xml'lang_uz  |  Description_xml'lang_vi  | 
			    Description_xml'lang_vo  |  Description_xml'lang_wo  | 
			    Description_xml'lang_xh  |  Description_xml'lang_yi  | 
			    Description_xml'lang_yo  |  Description_xml'lang_za  | 
			    Description_xml'lang_zh  |  Description_xml'lang_zu
			  deriving (Eq,Show)
data Publisher = Publisher Publisher_Attrs ANYContent
	       deriving (Eq,Show)
data Publisher_Attrs = Publisher_Attrs
    { publisherXmlns :: (Defaultable String)
    , publisherId :: (Maybe String)
    , publisherStyle :: (Maybe String)
    , publisherMid :: (Maybe String)
    } deriving (Eq,Show)
data TypeMeta = TypeMeta TypeMeta_Attrs ANYContent
	   deriving (Eq,Show)
data TypeMeta_Attrs = TypeMeta_Attrs
    { typeMetaXmlns :: (Defaultable String)
    } deriving (Eq,Show)
data Format = Format Format_Attrs ANYContent
	    deriving (Eq,Show)
data Format_Attrs = Format_Attrs
    { formatXmlns :: (Defaultable String)
    } deriving (Eq,Show)
data Source = Source Source_Attrs ANYContent
	    deriving (Eq,Show)
data Source_Attrs = Source_Attrs
    { sourceXmlns :: (Defaultable String)
    } deriving (Eq,Show)
data Language = Language Language_Attrs ANYContent
	      deriving (Eq,Show)
data Language_Attrs = Language_Attrs
    { languageXmlns :: (Defaultable String)
    } deriving (Eq,Show)
data Relation = Relation Relation_Attrs ANYContent
	      deriving (Eq,Show)
data Relation_Attrs = Relation_Attrs
    { relationXmlns :: (Defaultable String)
    } deriving (Eq,Show)
data Rights = Rights Rights_Attrs ANYContent
	    deriving (Eq,Show)
data Rights_Attrs = Rights_Attrs
    { rightsXmlns :: (Defaultable String)
    } deriving (Eq,Show)
data Date = Date Date_Attrs String
	  deriving (Eq,Show)
data Date_Attrs = Date_Attrs
    { dateXmlns :: (Defaultable String)
    , dateAction :: (Maybe String)
    , dateWho :: (Maybe String)
    } deriving (Eq,Show)
data Identifier = Identifier Identifier_Attrs String
		deriving (Eq,Show)
data Identifier_Attrs = Identifier_Attrs
    { identifierXmlns :: (Defaultable String)
    , identifierScheme :: (Defaultable String)
    } deriving (Eq,Show)
data Extradata = Extradata 		deriving (Eq,Show)


{-Instance decls-}

instance XmlContent Omdoc where
    fromElem (CElem (Elem "omdoc" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (Just (Omdoc (fromAttrs as) a b c), rest))
	      (many fromElem cb))
	   (fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Omdoc as a b c) =
	[CElem (Elem "omdoc" (toAttrs as) (maybe [] toElem a ++
					   maybe [] toElem b ++ concatMap toElem c))]
instance XmlAttributes Omdoc_Attrs where
    fromAttrs as =
	Omdoc_Attrs
	  { omdocId = definiteA fromAttrToStr "omdoc" "id" as
	  , omdocStyle = possibleA fromAttrToStr "style" as
	  , omdocMid = possibleA fromAttrToStr "mid" as
	  , omdocXmlns = defaultA fromAttrToStr "http://www.mathweb.org/omdoc" "xmlns" as
	  , omdocXmlns'xsi = defaultA fromAttrToStr "http://www.w3.org/2001/XMLSchema-instance" "xmlns:xsi" as
	  , omdocXsi'schemaLocation = defaultA fromAttrToStr "http://www.mathweb.org/omdoc/xsd/omdoc.xsd" "xsi:schemaLocation" as
	  , omdocType = possibleA fromAttrToTyp "type" as
	  , omdocCatalogue = possibleA fromAttrToStr "catalogue" as
	  , omdocVersion = defaultA fromAttrToStr "1.1" "version" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (omdocId v)
	, maybeToAttr toAttrFrStr "style" (omdocStyle v)
	, maybeToAttr toAttrFrStr "mid" (omdocMid v)
	, defaultToAttr toAttrFrStr "xmlns" (omdocXmlns v)
	, defaultToAttr toAttrFrStr "xmlns:xsi" (omdocXmlns'xsi v)
	, defaultToAttr toAttrFrStr "xsi:schemaLocation" (omdocXsi'schemaLocation v)
	, maybeToAttr toAttrFrTyp "type" (omdocType v)
	, maybeToAttr toAttrFrStr "catalogue" (omdocCatalogue v)
	, defaultToAttr toAttrFrStr "version" (omdocVersion v)
	]
instance XmlAttrType Omdoc_type where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "enumeration" = Just Omdoc_type_enumeration
	    translate "sequence" = Just Omdoc_type_sequence
	    translate "itemize" = Just Omdoc_type_itemize
	    translate "narrative" = Just Omdoc_type_narrative
	    translate "dataset" = Just Omdoc_type_dataset
	    translate "labeled-dataset" = Just Omdoc_type_labeled_dataset
	    translate "theory-collection" = Just Omdoc_type_theory_collection
	    translate _ = Nothing
    toAttrFrTyp n Omdoc_type_enumeration = Just (n, str2attr "enumeration")
    toAttrFrTyp n Omdoc_type_sequence = Just (n, str2attr "sequence")
    toAttrFrTyp n Omdoc_type_itemize = Just (n, str2attr "itemize")
    toAttrFrTyp n Omdoc_type_narrative = Just (n, str2attr "narrative")
    toAttrFrTyp n Omdoc_type_dataset = Just (n, str2attr "dataset")
    toAttrFrTyp n Omdoc_type_labeled_dataset = Just (n, str2attr "labeled-dataset")
    toAttrFrTyp n Omdoc_type_theory_collection = Just (n, str2attr "theory-collection")
instance XmlContent Catalogue where
    fromElem (CElem (Elem "catalogue" [] c0):rest) =
	(\(a,ca)->
	   (Just (Catalogue a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Catalogue a) =
	[CElem (Elem "catalogue" [] (concatMap toElem a))]
instance XmlContent Loc where
    fromElem (CElem (Elem "loc" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "loc" (toAttrs as) [])]
instance XmlAttributes Loc where
    fromAttrs as =
	Loc
	  { locTheory = definiteA fromAttrToStr "loc" "theory" as
	  , locOmdoc = possibleA fromAttrToStr "omdoc" as
	  , locCd = possibleA fromAttrToStr "cd" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "theory" (locTheory v)
	, maybeToAttr toAttrFrStr "omdoc" (locOmdoc v)
	, maybeToAttr toAttrFrStr "cd" (locCd v)
	]
instance XmlContent Omtext where
    fromElem (CElem (Elem "omtext" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (Just (Omtext (fromAttrs as) a b c), rest))
	      (fromElem cb))
	   (definite fromElem "CMP+" "omtext" ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Omtext as a b c) =
	[CElem (Elem "omtext" (toAttrs as) (maybe [] toElem a ++ toElem b
					    ++ maybe [] toElem c))]
instance XmlAttributes Omtext_Attrs where
    fromAttrs as =
	Omtext_Attrs
	  { omtextId = definiteA fromAttrToStr "omtext" "id" as
	  , omtextStyle = possibleA fromAttrToStr "style" as
	  , omtextMid = possibleA fromAttrToStr "mid" as
	  , omtextType = possibleA fromAttrToTyp "type" as
	  , omtextFor = possibleA fromAttrToStr "for" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (omtextId v)
	, maybeToAttr toAttrFrStr "style" (omtextStyle v)
	, maybeToAttr toAttrFrStr "mid" (omtextMid v)
	, maybeToAttr toAttrFrTyp "type" (omtextType v)
	, maybeToAttr toAttrFrStr "for" (omtextFor v)
	]
instance XmlAttrType Omtext_type where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "abstract" = Just Omtext_type_abstract
	    translate "introduction" = Just Omtext_type_introduction
	    translate "conclusion" = Just Omtext_type_conclusion
	    translate "thesis" = Just Omtext_type_thesis
	    translate "antithesis" = Just Omtext_type_antithesis
	    translate "elaboration" = Just Omtext_type_elaboration
	    translate "motivation" = Just Omtext_type_motivation
	    translate "evidence" = Just Omtext_type_evidence
	    translate "note" = Just Omtext_type_note
	    translate "annote" = Just Omtext_type_annote
	    translate "comment" = Just Omtext_type_comment
	    translate _ = Nothing
    toAttrFrTyp n Omtext_type_abstract = Just (n, str2attr "abstract")
    toAttrFrTyp n Omtext_type_introduction = Just (n, str2attr "introduction")
    toAttrFrTyp n Omtext_type_conclusion = Just (n, str2attr "conclusion")
    toAttrFrTyp n Omtext_type_thesis = Just (n, str2attr "thesis")
    toAttrFrTyp n Omtext_type_antithesis = Just (n, str2attr "antithesis")
    toAttrFrTyp n Omtext_type_elaboration = Just (n, str2attr "elaboration")
    toAttrFrTyp n Omtext_type_motivation = Just (n, str2attr "motivation")
    toAttrFrTyp n Omtext_type_evidence = Just (n, str2attr "evidence")
    toAttrFrTyp n Omtext_type_note = Just (n, str2attr "note")
    toAttrFrTyp n Omtext_type_annote = Just (n, str2attr "annote")
    toAttrFrTyp n Omtext_type_comment = Just (n, str2attr "comment")
instance XmlContent CMP where
    fromElem (CElem (Elem "CMP" as c0):rest) =
	(\(a,ca)->
	   (Just (CMP (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (CMP as a) =
	[CElem (Elem "CMP" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes CMP_Attrs where
    fromAttrs as =
	CMP_Attrs
	  { cMPXml'lang = defaultA fromAttrToTyp CMP_xml'lang_en "xml:lang" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrTyp "xml:lang" (cMPXml'lang v)
	]
instance XmlContent CMP_ where
    fromElem c0 =
	case (fromText c0) of
	(Just a,rest) -> (Just (CMP_Str a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (CMP_OMOBJ a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (CMP_Omlet a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (CMP_With a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (CMP_Ref a), rest)
					(_,_) ->
						case (fromElem c0) of
						(Just a,rest) -> (Just (CMP_Ignore a), rest)
						(_,_) ->
						    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (CMP_Str a) = toText a
    toElem (CMP_OMOBJ a) = toElem a
    toElem (CMP_Omlet a) = toElem a
    toElem (CMP_With a) = toElem a
    toElem (CMP_Ref a) = toElem a
    toElem (CMP_Ignore a) = toElem a
instance XmlAttrType CMP_xml'lang where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "aa" = Just CMP_xml'lang_aa
	    translate "ab" = Just CMP_xml'lang_ab
	    translate "af" = Just CMP_xml'lang_af
	    translate "am" = Just CMP_xml'lang_am
	    translate "ar" = Just CMP_xml'lang_ar
	    translate "as" = Just CMP_xml'lang_as
	    translate "ay" = Just CMP_xml'lang_ay
	    translate "az" = Just CMP_xml'lang_az
	    translate "ba" = Just CMP_xml'lang_ba
	    translate "be" = Just CMP_xml'lang_be
	    translate "bg" = Just CMP_xml'lang_bg
	    translate "bh" = Just CMP_xml'lang_bh
	    translate "bi" = Just CMP_xml'lang_bi
	    translate "bn" = Just CMP_xml'lang_bn
	    translate "bo" = Just CMP_xml'lang_bo
	    translate "br" = Just CMP_xml'lang_br
	    translate "ca" = Just CMP_xml'lang_ca
	    translate "co" = Just CMP_xml'lang_co
	    translate "cs" = Just CMP_xml'lang_cs
	    translate "cy" = Just CMP_xml'lang_cy
	    translate "da" = Just CMP_xml'lang_da
	    translate "de" = Just CMP_xml'lang_de
	    translate "dz" = Just CMP_xml'lang_dz
	    translate "el" = Just CMP_xml'lang_el
	    translate "en" = Just CMP_xml'lang_en
	    translate "eo" = Just CMP_xml'lang_eo
	    translate "es" = Just CMP_xml'lang_es
	    translate "et" = Just CMP_xml'lang_et
	    translate "eu" = Just CMP_xml'lang_eu
	    translate "fa" = Just CMP_xml'lang_fa
	    translate "fi" = Just CMP_xml'lang_fi
	    translate "fj" = Just CMP_xml'lang_fj
	    translate "fo" = Just CMP_xml'lang_fo
	    translate "fr" = Just CMP_xml'lang_fr
	    translate "fy" = Just CMP_xml'lang_fy
	    translate "ga" = Just CMP_xml'lang_ga
	    translate "gd" = Just CMP_xml'lang_gd
	    translate "gl" = Just CMP_xml'lang_gl
	    translate "gn" = Just CMP_xml'lang_gn
	    translate "gu" = Just CMP_xml'lang_gu
	    translate "ha" = Just CMP_xml'lang_ha
	    translate "he" = Just CMP_xml'lang_he
	    translate "hi" = Just CMP_xml'lang_hi
	    translate "hr" = Just CMP_xml'lang_hr
	    translate "hu" = Just CMP_xml'lang_hu
	    translate "hy" = Just CMP_xml'lang_hy
	    translate "ia" = Just CMP_xml'lang_ia
	    translate "ie" = Just CMP_xml'lang_ie
	    translate "ik" = Just CMP_xml'lang_ik
	    translate "id" = Just CMP_xml'lang_id
	    translate "is" = Just CMP_xml'lang_is
	    translate "it" = Just CMP_xml'lang_it
	    translate "iu" = Just CMP_xml'lang_iu
	    translate "ja" = Just CMP_xml'lang_ja
	    translate "jv" = Just CMP_xml'lang_jv
	    translate "ka" = Just CMP_xml'lang_ka
	    translate "kk" = Just CMP_xml'lang_kk
	    translate "kl" = Just CMP_xml'lang_kl
	    translate "km" = Just CMP_xml'lang_km
	    translate "kn" = Just CMP_xml'lang_kn
	    translate "ko" = Just CMP_xml'lang_ko
	    translate "ks" = Just CMP_xml'lang_ks
	    translate "ku" = Just CMP_xml'lang_ku
	    translate "ky" = Just CMP_xml'lang_ky
	    translate "la" = Just CMP_xml'lang_la
	    translate "ln" = Just CMP_xml'lang_ln
	    translate "lo" = Just CMP_xml'lang_lo
	    translate "lt" = Just CMP_xml'lang_lt
	    translate "lv" = Just CMP_xml'lang_lv
	    translate "mg" = Just CMP_xml'lang_mg
	    translate "mi" = Just CMP_xml'lang_mi
	    translate "mk" = Just CMP_xml'lang_mk
	    translate "ml" = Just CMP_xml'lang_ml
	    translate "mn" = Just CMP_xml'lang_mn
	    translate "mo" = Just CMP_xml'lang_mo
	    translate "mr" = Just CMP_xml'lang_mr
	    translate "ms" = Just CMP_xml'lang_ms
	    translate "mt" = Just CMP_xml'lang_mt
	    translate "my" = Just CMP_xml'lang_my
	    translate "na" = Just CMP_xml'lang_na
	    translate "ne" = Just CMP_xml'lang_ne
	    translate "nl" = Just CMP_xml'lang_nl
	    translate "no" = Just CMP_xml'lang_no
	    translate "oc" = Just CMP_xml'lang_oc
	    translate "om" = Just CMP_xml'lang_om
	    translate "or" = Just CMP_xml'lang_or
	    translate "pa" = Just CMP_xml'lang_pa
	    translate "pl" = Just CMP_xml'lang_pl
	    translate "ps" = Just CMP_xml'lang_ps
	    translate "pt" = Just CMP_xml'lang_pt
	    translate "qu" = Just CMP_xml'lang_qu
	    translate "rm" = Just CMP_xml'lang_rm
	    translate "rn" = Just CMP_xml'lang_rn
	    translate "ro" = Just CMP_xml'lang_ro
	    translate "ru" = Just CMP_xml'lang_ru
	    translate "rw" = Just CMP_xml'lang_rw
	    translate "sa" = Just CMP_xml'lang_sa
	    translate "sd" = Just CMP_xml'lang_sd
	    translate "sg" = Just CMP_xml'lang_sg
	    translate "sh" = Just CMP_xml'lang_sh
	    translate "si" = Just CMP_xml'lang_si
	    translate "sk" = Just CMP_xml'lang_sk
	    translate "sl" = Just CMP_xml'lang_sl
	    translate "sm" = Just CMP_xml'lang_sm
	    translate "sn" = Just CMP_xml'lang_sn
	    translate "so" = Just CMP_xml'lang_so
	    translate "sq" = Just CMP_xml'lang_sq
	    translate "sr" = Just CMP_xml'lang_sr
	    translate "ss" = Just CMP_xml'lang_ss
	    translate "st" = Just CMP_xml'lang_st
	    translate "su" = Just CMP_xml'lang_su
	    translate "sv" = Just CMP_xml'lang_sv
	    translate "sw" = Just CMP_xml'lang_sw
	    translate "ta" = Just CMP_xml'lang_ta
	    translate "te" = Just CMP_xml'lang_te
	    translate "tg" = Just CMP_xml'lang_tg
	    translate "th" = Just CMP_xml'lang_th
	    translate "ti" = Just CMP_xml'lang_ti
	    translate "tk" = Just CMP_xml'lang_tk
	    translate "tl" = Just CMP_xml'lang_tl
	    translate "tn" = Just CMP_xml'lang_tn
	    translate "to" = Just CMP_xml'lang_to
	    translate "tr" = Just CMP_xml'lang_tr
	    translate "ts" = Just CMP_xml'lang_ts
	    translate "tt" = Just CMP_xml'lang_tt
	    translate "tw" = Just CMP_xml'lang_tw
	    translate "ug" = Just CMP_xml'lang_ug
	    translate "uk" = Just CMP_xml'lang_uk
	    translate "ur" = Just CMP_xml'lang_ur
	    translate "uz" = Just CMP_xml'lang_uz
	    translate "vi" = Just CMP_xml'lang_vi
	    translate "vo" = Just CMP_xml'lang_vo
	    translate "wo" = Just CMP_xml'lang_wo
	    translate "xh" = Just CMP_xml'lang_xh
	    translate "yi" = Just CMP_xml'lang_yi
	    translate "yo" = Just CMP_xml'lang_yo
	    translate "za" = Just CMP_xml'lang_za
	    translate "zh" = Just CMP_xml'lang_zh
	    translate "zu" = Just CMP_xml'lang_zu
	    translate _ = Nothing
    toAttrFrTyp n CMP_xml'lang_aa = Just (n, str2attr "aa")
    toAttrFrTyp n CMP_xml'lang_ab = Just (n, str2attr "ab")
    toAttrFrTyp n CMP_xml'lang_af = Just (n, str2attr "af")
    toAttrFrTyp n CMP_xml'lang_am = Just (n, str2attr "am")
    toAttrFrTyp n CMP_xml'lang_ar = Just (n, str2attr "ar")
    toAttrFrTyp n CMP_xml'lang_as = Just (n, str2attr "as")
    toAttrFrTyp n CMP_xml'lang_ay = Just (n, str2attr "ay")
    toAttrFrTyp n CMP_xml'lang_az = Just (n, str2attr "az")
    toAttrFrTyp n CMP_xml'lang_ba = Just (n, str2attr "ba")
    toAttrFrTyp n CMP_xml'lang_be = Just (n, str2attr "be")
    toAttrFrTyp n CMP_xml'lang_bg = Just (n, str2attr "bg")
    toAttrFrTyp n CMP_xml'lang_bh = Just (n, str2attr "bh")
    toAttrFrTyp n CMP_xml'lang_bi = Just (n, str2attr "bi")
    toAttrFrTyp n CMP_xml'lang_bn = Just (n, str2attr "bn")
    toAttrFrTyp n CMP_xml'lang_bo = Just (n, str2attr "bo")
    toAttrFrTyp n CMP_xml'lang_br = Just (n, str2attr "br")
    toAttrFrTyp n CMP_xml'lang_ca = Just (n, str2attr "ca")
    toAttrFrTyp n CMP_xml'lang_co = Just (n, str2attr "co")
    toAttrFrTyp n CMP_xml'lang_cs = Just (n, str2attr "cs")
    toAttrFrTyp n CMP_xml'lang_cy = Just (n, str2attr "cy")
    toAttrFrTyp n CMP_xml'lang_da = Just (n, str2attr "da")
    toAttrFrTyp n CMP_xml'lang_de = Just (n, str2attr "de")
    toAttrFrTyp n CMP_xml'lang_dz = Just (n, str2attr "dz")
    toAttrFrTyp n CMP_xml'lang_el = Just (n, str2attr "el")
    toAttrFrTyp n CMP_xml'lang_en = Just (n, str2attr "en")
    toAttrFrTyp n CMP_xml'lang_eo = Just (n, str2attr "eo")
    toAttrFrTyp n CMP_xml'lang_es = Just (n, str2attr "es")
    toAttrFrTyp n CMP_xml'lang_et = Just (n, str2attr "et")
    toAttrFrTyp n CMP_xml'lang_eu = Just (n, str2attr "eu")
    toAttrFrTyp n CMP_xml'lang_fa = Just (n, str2attr "fa")
    toAttrFrTyp n CMP_xml'lang_fi = Just (n, str2attr "fi")
    toAttrFrTyp n CMP_xml'lang_fj = Just (n, str2attr "fj")
    toAttrFrTyp n CMP_xml'lang_fo = Just (n, str2attr "fo")
    toAttrFrTyp n CMP_xml'lang_fr = Just (n, str2attr "fr")
    toAttrFrTyp n CMP_xml'lang_fy = Just (n, str2attr "fy")
    toAttrFrTyp n CMP_xml'lang_ga = Just (n, str2attr "ga")
    toAttrFrTyp n CMP_xml'lang_gd = Just (n, str2attr "gd")
    toAttrFrTyp n CMP_xml'lang_gl = Just (n, str2attr "gl")
    toAttrFrTyp n CMP_xml'lang_gn = Just (n, str2attr "gn")
    toAttrFrTyp n CMP_xml'lang_gu = Just (n, str2attr "gu")
    toAttrFrTyp n CMP_xml'lang_ha = Just (n, str2attr "ha")
    toAttrFrTyp n CMP_xml'lang_he = Just (n, str2attr "he")
    toAttrFrTyp n CMP_xml'lang_hi = Just (n, str2attr "hi")
    toAttrFrTyp n CMP_xml'lang_hr = Just (n, str2attr "hr")
    toAttrFrTyp n CMP_xml'lang_hu = Just (n, str2attr "hu")
    toAttrFrTyp n CMP_xml'lang_hy = Just (n, str2attr "hy")
    toAttrFrTyp n CMP_xml'lang_ia = Just (n, str2attr "ia")
    toAttrFrTyp n CMP_xml'lang_ie = Just (n, str2attr "ie")
    toAttrFrTyp n CMP_xml'lang_ik = Just (n, str2attr "ik")
    toAttrFrTyp n CMP_xml'lang_id = Just (n, str2attr "id")
    toAttrFrTyp n CMP_xml'lang_is = Just (n, str2attr "is")
    toAttrFrTyp n CMP_xml'lang_it = Just (n, str2attr "it")
    toAttrFrTyp n CMP_xml'lang_iu = Just (n, str2attr "iu")
    toAttrFrTyp n CMP_xml'lang_ja = Just (n, str2attr "ja")
    toAttrFrTyp n CMP_xml'lang_jv = Just (n, str2attr "jv")
    toAttrFrTyp n CMP_xml'lang_ka = Just (n, str2attr "ka")
    toAttrFrTyp n CMP_xml'lang_kk = Just (n, str2attr "kk")
    toAttrFrTyp n CMP_xml'lang_kl = Just (n, str2attr "kl")
    toAttrFrTyp n CMP_xml'lang_km = Just (n, str2attr "km")
    toAttrFrTyp n CMP_xml'lang_kn = Just (n, str2attr "kn")
    toAttrFrTyp n CMP_xml'lang_ko = Just (n, str2attr "ko")
    toAttrFrTyp n CMP_xml'lang_ks = Just (n, str2attr "ks")
    toAttrFrTyp n CMP_xml'lang_ku = Just (n, str2attr "ku")
    toAttrFrTyp n CMP_xml'lang_ky = Just (n, str2attr "ky")
    toAttrFrTyp n CMP_xml'lang_la = Just (n, str2attr "la")
    toAttrFrTyp n CMP_xml'lang_ln = Just (n, str2attr "ln")
    toAttrFrTyp n CMP_xml'lang_lo = Just (n, str2attr "lo")
    toAttrFrTyp n CMP_xml'lang_lt = Just (n, str2attr "lt")
    toAttrFrTyp n CMP_xml'lang_lv = Just (n, str2attr "lv")
    toAttrFrTyp n CMP_xml'lang_mg = Just (n, str2attr "mg")
    toAttrFrTyp n CMP_xml'lang_mi = Just (n, str2attr "mi")
    toAttrFrTyp n CMP_xml'lang_mk = Just (n, str2attr "mk")
    toAttrFrTyp n CMP_xml'lang_ml = Just (n, str2attr "ml")
    toAttrFrTyp n CMP_xml'lang_mn = Just (n, str2attr "mn")
    toAttrFrTyp n CMP_xml'lang_mo = Just (n, str2attr "mo")
    toAttrFrTyp n CMP_xml'lang_mr = Just (n, str2attr "mr")
    toAttrFrTyp n CMP_xml'lang_ms = Just (n, str2attr "ms")
    toAttrFrTyp n CMP_xml'lang_mt = Just (n, str2attr "mt")
    toAttrFrTyp n CMP_xml'lang_my = Just (n, str2attr "my")
    toAttrFrTyp n CMP_xml'lang_na = Just (n, str2attr "na")
    toAttrFrTyp n CMP_xml'lang_ne = Just (n, str2attr "ne")
    toAttrFrTyp n CMP_xml'lang_nl = Just (n, str2attr "nl")
    toAttrFrTyp n CMP_xml'lang_no = Just (n, str2attr "no")
    toAttrFrTyp n CMP_xml'lang_oc = Just (n, str2attr "oc")
    toAttrFrTyp n CMP_xml'lang_om = Just (n, str2attr "om")
    toAttrFrTyp n CMP_xml'lang_or = Just (n, str2attr "or")
    toAttrFrTyp n CMP_xml'lang_pa = Just (n, str2attr "pa")
    toAttrFrTyp n CMP_xml'lang_pl = Just (n, str2attr "pl")
    toAttrFrTyp n CMP_xml'lang_ps = Just (n, str2attr "ps")
    toAttrFrTyp n CMP_xml'lang_pt = Just (n, str2attr "pt")
    toAttrFrTyp n CMP_xml'lang_qu = Just (n, str2attr "qu")
    toAttrFrTyp n CMP_xml'lang_rm = Just (n, str2attr "rm")
    toAttrFrTyp n CMP_xml'lang_rn = Just (n, str2attr "rn")
    toAttrFrTyp n CMP_xml'lang_ro = Just (n, str2attr "ro")
    toAttrFrTyp n CMP_xml'lang_ru = Just (n, str2attr "ru")
    toAttrFrTyp n CMP_xml'lang_rw = Just (n, str2attr "rw")
    toAttrFrTyp n CMP_xml'lang_sa = Just (n, str2attr "sa")
    toAttrFrTyp n CMP_xml'lang_sd = Just (n, str2attr "sd")
    toAttrFrTyp n CMP_xml'lang_sg = Just (n, str2attr "sg")
    toAttrFrTyp n CMP_xml'lang_sh = Just (n, str2attr "sh")
    toAttrFrTyp n CMP_xml'lang_si = Just (n, str2attr "si")
    toAttrFrTyp n CMP_xml'lang_sk = Just (n, str2attr "sk")
    toAttrFrTyp n CMP_xml'lang_sl = Just (n, str2attr "sl")
    toAttrFrTyp n CMP_xml'lang_sm = Just (n, str2attr "sm")
    toAttrFrTyp n CMP_xml'lang_sn = Just (n, str2attr "sn")
    toAttrFrTyp n CMP_xml'lang_so = Just (n, str2attr "so")
    toAttrFrTyp n CMP_xml'lang_sq = Just (n, str2attr "sq")
    toAttrFrTyp n CMP_xml'lang_sr = Just (n, str2attr "sr")
    toAttrFrTyp n CMP_xml'lang_ss = Just (n, str2attr "ss")
    toAttrFrTyp n CMP_xml'lang_st = Just (n, str2attr "st")
    toAttrFrTyp n CMP_xml'lang_su = Just (n, str2attr "su")
    toAttrFrTyp n CMP_xml'lang_sv = Just (n, str2attr "sv")
    toAttrFrTyp n CMP_xml'lang_sw = Just (n, str2attr "sw")
    toAttrFrTyp n CMP_xml'lang_ta = Just (n, str2attr "ta")
    toAttrFrTyp n CMP_xml'lang_te = Just (n, str2attr "te")
    toAttrFrTyp n CMP_xml'lang_tg = Just (n, str2attr "tg")
    toAttrFrTyp n CMP_xml'lang_th = Just (n, str2attr "th")
    toAttrFrTyp n CMP_xml'lang_ti = Just (n, str2attr "ti")
    toAttrFrTyp n CMP_xml'lang_tk = Just (n, str2attr "tk")
    toAttrFrTyp n CMP_xml'lang_tl = Just (n, str2attr "tl")
    toAttrFrTyp n CMP_xml'lang_tn = Just (n, str2attr "tn")
    toAttrFrTyp n CMP_xml'lang_to = Just (n, str2attr "to")
    toAttrFrTyp n CMP_xml'lang_tr = Just (n, str2attr "tr")
    toAttrFrTyp n CMP_xml'lang_ts = Just (n, str2attr "ts")
    toAttrFrTyp n CMP_xml'lang_tt = Just (n, str2attr "tt")
    toAttrFrTyp n CMP_xml'lang_tw = Just (n, str2attr "tw")
    toAttrFrTyp n CMP_xml'lang_ug = Just (n, str2attr "ug")
    toAttrFrTyp n CMP_xml'lang_uk = Just (n, str2attr "uk")
    toAttrFrTyp n CMP_xml'lang_ur = Just (n, str2attr "ur")
    toAttrFrTyp n CMP_xml'lang_uz = Just (n, str2attr "uz")
    toAttrFrTyp n CMP_xml'lang_vi = Just (n, str2attr "vi")
    toAttrFrTyp n CMP_xml'lang_vo = Just (n, str2attr "vo")
    toAttrFrTyp n CMP_xml'lang_wo = Just (n, str2attr "wo")
    toAttrFrTyp n CMP_xml'lang_xh = Just (n, str2attr "xh")
    toAttrFrTyp n CMP_xml'lang_yi = Just (n, str2attr "yi")
    toAttrFrTyp n CMP_xml'lang_yo = Just (n, str2attr "yo")
    toAttrFrTyp n CMP_xml'lang_za = Just (n, str2attr "za")
    toAttrFrTyp n CMP_xml'lang_zh = Just (n, str2attr "zh")
    toAttrFrTyp n CMP_xml'lang_zu = Just (n, str2attr "zu")
instance XmlContent With where
    fromElem (CElem (Elem "with" as c0):rest) =
	(\(a,ca)->
	   (Just (With (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (With as a) =
	[CElem (Elem "with" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes With_Attrs where
    fromAttrs as =
	With_Attrs
	  { withId = possibleA fromAttrToStr "id" as
	  , withStyle = possibleA fromAttrToStr "style" as
	  , withXmlns = defaultA fromAttrToStr "http://www.mathweb.org/omdoc" "xmlns" as
	  , withXmlns'xsi = defaultA fromAttrToStr "http://www.w3.org/2001/XMLSchema-instance" "xmlns:xsi" as
	  , withXsi'schemaLocation = defaultA fromAttrToStr "http://www.mathweb.org/omdoc/xsd/omdoc.xsd" "xsi:schemaLocation" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (withId v)
	, maybeToAttr toAttrFrStr "style" (withStyle v)
	, defaultToAttr toAttrFrStr "xmlns" (withXmlns v)
	, defaultToAttr toAttrFrStr "xmlns:xsi" (withXmlns'xsi v)
	, defaultToAttr toAttrFrStr "xsi:schemaLocation" (withXsi'schemaLocation v)
	]
instance XmlContent With_ where
    fromElem c0 =
	case (fromText c0) of
	(Just a,rest) -> (Just (With_Str a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (With_OMOBJ a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (With_Omlet a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (With_With a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (With_Ref a), rest)
					(_,_) ->
						case (fromElem c0) of
						(Just a,rest) -> (Just (With_Ignore a), rest)
						(_,_) ->
						    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (With_Str a) = toText a
    toElem (With_OMOBJ a) = toElem a
    toElem (With_Omlet a) = toElem a
    toElem (With_With a) = toElem a
    toElem (With_Ref a) = toElem a
    toElem (With_Ignore a) = toElem a
instance XmlContent Omgroup where
    fromElem (CElem (Elem "omgroup" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Omgroup (fromAttrs as) a b), rest))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Omgroup as a b) =
	[CElem (Elem "omgroup" (toAttrs as) (maybe [] toElem a ++
					     concatMap toElem b))]
instance XmlAttributes Omgroup_Attrs where
    fromAttrs as =
	Omgroup_Attrs
	  { omgroupId = possibleA fromAttrToStr "id" as
	  , omgroupStyle = possibleA fromAttrToStr "style" as
	  , omgroupMid = possibleA fromAttrToStr "mid" as
	  , omgroupType = possibleA fromAttrToTyp "type" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (omgroupId v)
	, maybeToAttr toAttrFrStr "style" (omgroupStyle v)
	, maybeToAttr toAttrFrStr "mid" (omgroupMid v)
	, maybeToAttr toAttrFrTyp "type" (omgroupType v)
	]
instance XmlAttrType Omgroup_type where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "enumeration" = Just Omgroup_type_enumeration
	    translate "sequence" = Just Omgroup_type_sequence
	    translate "itemize" = Just Omgroup_type_itemize
	    translate "narrative" = Just Omgroup_type_narrative
	    translate "dataset" = Just Omgroup_type_dataset
	    translate "labeled-dataset" = Just Omgroup_type_labeled_dataset
	    translate _ = Nothing
    toAttrFrTyp n Omgroup_type_enumeration = Just (n, str2attr "enumeration")
    toAttrFrTyp n Omgroup_type_sequence = Just (n, str2attr "sequence")
    toAttrFrTyp n Omgroup_type_itemize = Just (n, str2attr "itemize")
    toAttrFrTyp n Omgroup_type_narrative = Just (n, str2attr "narrative")
    toAttrFrTyp n Omgroup_type_dataset = Just (n, str2attr "dataset")
    toAttrFrTyp n Omgroup_type_labeled_dataset = Just (n, str2attr "labeled-dataset")
instance XmlContent Ref where
    fromElem (CElem (Elem "ref" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "ref" (toAttrs as) [])]
instance XmlAttributes Ref where
    fromAttrs as =
	Ref
	  { refXref = definiteA fromAttrToStr "ref" "xref" as
	  , refType = defaultA fromAttrToStr "include" "type" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "xref" (refXref v)
	, defaultToAttr toAttrFrStr "type" (refType v)
	]
instance XmlContent Symbol where
    fromElem (CElem (Elem "symbol" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (Just (Symbol (fromAttrs as) a b c), rest))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Symbol as a b c) =
	[CElem (Elem "symbol" (toAttrs as) (maybe [] toElem a ++
					    concatMap toElem b ++ concatMap toElem c))]
instance XmlAttributes Symbol_Attrs where
    fromAttrs as =
	Symbol_Attrs
	  { symbolId = definiteA fromAttrToStr "symbol" "id" as
	  , symbolStyle = possibleA fromAttrToStr "style" as
	  , symbolMid = possibleA fromAttrToStr "mid" as
	  , symbolKind = defaultA fromAttrToTyp Symbol_kind_object "kind" as
	  , symbolScope = defaultA fromAttrToTyp Symbol_scope_global "scope" as
	  , symbolGenerated_by = possibleA fromAttrToStr "generated-by" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (symbolId v)
	, maybeToAttr toAttrFrStr "style" (symbolStyle v)
	, maybeToAttr toAttrFrStr "mid" (symbolMid v)
	, defaultToAttr toAttrFrTyp "kind" (symbolKind v)
	, defaultToAttr toAttrFrTyp "scope" (symbolScope v)
	, maybeToAttr toAttrFrStr "generated-by" (symbolGenerated_by v)
	]
instance XmlAttrType Symbol_kind where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "type" = Just Symbol_kind_type
	    translate "sort" = Just Symbol_kind_sort
	    translate "object" = Just Symbol_kind_object
	    translate _ = Nothing
    toAttrFrTyp n Symbol_kind_type = Just (n, str2attr "type")
    toAttrFrTyp n Symbol_kind_sort = Just (n, str2attr "sort")
    toAttrFrTyp n Symbol_kind_object = Just (n, str2attr "object")
instance XmlAttrType Symbol_scope where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "global" = Just Symbol_scope_global
	    translate "local" = Just Symbol_scope_local
	    translate _ = Nothing
    toAttrFrTyp n Symbol_scope_global = Just (n, str2attr "global")
    toAttrFrTyp n Symbol_scope_local = Just (n, str2attr "local")
instance XmlContent Commonname where
    fromElem (CElem (Elem "commonname" as c0):rest) =
	(\(a,ca)->
	   (Just (Commonname (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Commonname as a) =
	[CElem (Elem "commonname" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Commonname_Attrs where
    fromAttrs as =
	Commonname_Attrs
	  { commonnameXml'lang = defaultA fromAttrToTyp Commonname_xml'lang_en "xml:lang" as
	  , commonnameMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrTyp "xml:lang" (commonnameXml'lang v)
	, maybeToAttr toAttrFrStr "mid" (commonnameMid v)
	]
instance XmlContent Commonname_ where
    fromElem c0 =
	case (fromText c0) of
	(Just a,rest) -> (Just (Commonname_Str a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Commonname_OMOBJ a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (Commonname_Omlet a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (Commonname_With a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (Commonname_Ref a), rest)
					(_,_) ->
						case (fromElem c0) of
						(Just a,rest) -> (Just (Commonname_Ignore a), rest)
						(_,_) ->
						    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Commonname_Str a) = toText a
    toElem (Commonname_OMOBJ a) = toElem a
    toElem (Commonname_Omlet a) = toElem a
    toElem (Commonname_With a) = toElem a
    toElem (Commonname_Ref a) = toElem a
    toElem (Commonname_Ignore a) = toElem a
instance XmlAttrType Commonname_xml'lang where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "aa" = Just Commonname_xml'lang_aa
	    translate "ab" = Just Commonname_xml'lang_ab
	    translate "af" = Just Commonname_xml'lang_af
	    translate "am" = Just Commonname_xml'lang_am
	    translate "ar" = Just Commonname_xml'lang_ar
	    translate "as" = Just Commonname_xml'lang_as
	    translate "ay" = Just Commonname_xml'lang_ay
	    translate "az" = Just Commonname_xml'lang_az
	    translate "ba" = Just Commonname_xml'lang_ba
	    translate "be" = Just Commonname_xml'lang_be
	    translate "bg" = Just Commonname_xml'lang_bg
	    translate "bh" = Just Commonname_xml'lang_bh
	    translate "bi" = Just Commonname_xml'lang_bi
	    translate "bn" = Just Commonname_xml'lang_bn
	    translate "bo" = Just Commonname_xml'lang_bo
	    translate "br" = Just Commonname_xml'lang_br
	    translate "ca" = Just Commonname_xml'lang_ca
	    translate "co" = Just Commonname_xml'lang_co
	    translate "cs" = Just Commonname_xml'lang_cs
	    translate "cy" = Just Commonname_xml'lang_cy
	    translate "da" = Just Commonname_xml'lang_da
	    translate "de" = Just Commonname_xml'lang_de
	    translate "dz" = Just Commonname_xml'lang_dz
	    translate "el" = Just Commonname_xml'lang_el
	    translate "en" = Just Commonname_xml'lang_en
	    translate "eo" = Just Commonname_xml'lang_eo
	    translate "es" = Just Commonname_xml'lang_es
	    translate "et" = Just Commonname_xml'lang_et
	    translate "eu" = Just Commonname_xml'lang_eu
	    translate "fa" = Just Commonname_xml'lang_fa
	    translate "fi" = Just Commonname_xml'lang_fi
	    translate "fj" = Just Commonname_xml'lang_fj
	    translate "fo" = Just Commonname_xml'lang_fo
	    translate "fr" = Just Commonname_xml'lang_fr
	    translate "fy" = Just Commonname_xml'lang_fy
	    translate "ga" = Just Commonname_xml'lang_ga
	    translate "gd" = Just Commonname_xml'lang_gd
	    translate "gl" = Just Commonname_xml'lang_gl
	    translate "gn" = Just Commonname_xml'lang_gn
	    translate "gu" = Just Commonname_xml'lang_gu
	    translate "ha" = Just Commonname_xml'lang_ha
	    translate "he" = Just Commonname_xml'lang_he
	    translate "hi" = Just Commonname_xml'lang_hi
	    translate "hr" = Just Commonname_xml'lang_hr
	    translate "hu" = Just Commonname_xml'lang_hu
	    translate "hy" = Just Commonname_xml'lang_hy
	    translate "ia" = Just Commonname_xml'lang_ia
	    translate "ie" = Just Commonname_xml'lang_ie
	    translate "ik" = Just Commonname_xml'lang_ik
	    translate "id" = Just Commonname_xml'lang_id
	    translate "is" = Just Commonname_xml'lang_is
	    translate "it" = Just Commonname_xml'lang_it
	    translate "iu" = Just Commonname_xml'lang_iu
	    translate "ja" = Just Commonname_xml'lang_ja
	    translate "jv" = Just Commonname_xml'lang_jv
	    translate "ka" = Just Commonname_xml'lang_ka
	    translate "kk" = Just Commonname_xml'lang_kk
	    translate "kl" = Just Commonname_xml'lang_kl
	    translate "km" = Just Commonname_xml'lang_km
	    translate "kn" = Just Commonname_xml'lang_kn
	    translate "ko" = Just Commonname_xml'lang_ko
	    translate "ks" = Just Commonname_xml'lang_ks
	    translate "ku" = Just Commonname_xml'lang_ku
	    translate "ky" = Just Commonname_xml'lang_ky
	    translate "la" = Just Commonname_xml'lang_la
	    translate "ln" = Just Commonname_xml'lang_ln
	    translate "lo" = Just Commonname_xml'lang_lo
	    translate "lt" = Just Commonname_xml'lang_lt
	    translate "lv" = Just Commonname_xml'lang_lv
	    translate "mg" = Just Commonname_xml'lang_mg
	    translate "mi" = Just Commonname_xml'lang_mi
	    translate "mk" = Just Commonname_xml'lang_mk
	    translate "ml" = Just Commonname_xml'lang_ml
	    translate "mn" = Just Commonname_xml'lang_mn
	    translate "mo" = Just Commonname_xml'lang_mo
	    translate "mr" = Just Commonname_xml'lang_mr
	    translate "ms" = Just Commonname_xml'lang_ms
	    translate "mt" = Just Commonname_xml'lang_mt
	    translate "my" = Just Commonname_xml'lang_my
	    translate "na" = Just Commonname_xml'lang_na
	    translate "ne" = Just Commonname_xml'lang_ne
	    translate "nl" = Just Commonname_xml'lang_nl
	    translate "no" = Just Commonname_xml'lang_no
	    translate "oc" = Just Commonname_xml'lang_oc
	    translate "om" = Just Commonname_xml'lang_om
	    translate "or" = Just Commonname_xml'lang_or
	    translate "pa" = Just Commonname_xml'lang_pa
	    translate "pl" = Just Commonname_xml'lang_pl
	    translate "ps" = Just Commonname_xml'lang_ps
	    translate "pt" = Just Commonname_xml'lang_pt
	    translate "qu" = Just Commonname_xml'lang_qu
	    translate "rm" = Just Commonname_xml'lang_rm
	    translate "rn" = Just Commonname_xml'lang_rn
	    translate "ro" = Just Commonname_xml'lang_ro
	    translate "ru" = Just Commonname_xml'lang_ru
	    translate "rw" = Just Commonname_xml'lang_rw
	    translate "sa" = Just Commonname_xml'lang_sa
	    translate "sd" = Just Commonname_xml'lang_sd
	    translate "sg" = Just Commonname_xml'lang_sg
	    translate "sh" = Just Commonname_xml'lang_sh
	    translate "si" = Just Commonname_xml'lang_si
	    translate "sk" = Just Commonname_xml'lang_sk
	    translate "sl" = Just Commonname_xml'lang_sl
	    translate "sm" = Just Commonname_xml'lang_sm
	    translate "sn" = Just Commonname_xml'lang_sn
	    translate "so" = Just Commonname_xml'lang_so
	    translate "sq" = Just Commonname_xml'lang_sq
	    translate "sr" = Just Commonname_xml'lang_sr
	    translate "ss" = Just Commonname_xml'lang_ss
	    translate "st" = Just Commonname_xml'lang_st
	    translate "su" = Just Commonname_xml'lang_su
	    translate "sv" = Just Commonname_xml'lang_sv
	    translate "sw" = Just Commonname_xml'lang_sw
	    translate "ta" = Just Commonname_xml'lang_ta
	    translate "te" = Just Commonname_xml'lang_te
	    translate "tg" = Just Commonname_xml'lang_tg
	    translate "th" = Just Commonname_xml'lang_th
	    translate "ti" = Just Commonname_xml'lang_ti
	    translate "tk" = Just Commonname_xml'lang_tk
	    translate "tl" = Just Commonname_xml'lang_tl
	    translate "tn" = Just Commonname_xml'lang_tn
	    translate "to" = Just Commonname_xml'lang_to
	    translate "tr" = Just Commonname_xml'lang_tr
	    translate "ts" = Just Commonname_xml'lang_ts
	    translate "tt" = Just Commonname_xml'lang_tt
	    translate "tw" = Just Commonname_xml'lang_tw
	    translate "ug" = Just Commonname_xml'lang_ug
	    translate "uk" = Just Commonname_xml'lang_uk
	    translate "ur" = Just Commonname_xml'lang_ur
	    translate "uz" = Just Commonname_xml'lang_uz
	    translate "vi" = Just Commonname_xml'lang_vi
	    translate "vo" = Just Commonname_xml'lang_vo
	    translate "wo" = Just Commonname_xml'lang_wo
	    translate "xh" = Just Commonname_xml'lang_xh
	    translate "yi" = Just Commonname_xml'lang_yi
	    translate "yo" = Just Commonname_xml'lang_yo
	    translate "za" = Just Commonname_xml'lang_za
	    translate "zh" = Just Commonname_xml'lang_zh
	    translate "zu" = Just Commonname_xml'lang_zu
	    translate _ = Nothing
    toAttrFrTyp n Commonname_xml'lang_aa = Just (n, str2attr "aa")
    toAttrFrTyp n Commonname_xml'lang_ab = Just (n, str2attr "ab")
    toAttrFrTyp n Commonname_xml'lang_af = Just (n, str2attr "af")
    toAttrFrTyp n Commonname_xml'lang_am = Just (n, str2attr "am")
    toAttrFrTyp n Commonname_xml'lang_ar = Just (n, str2attr "ar")
    toAttrFrTyp n Commonname_xml'lang_as = Just (n, str2attr "as")
    toAttrFrTyp n Commonname_xml'lang_ay = Just (n, str2attr "ay")
    toAttrFrTyp n Commonname_xml'lang_az = Just (n, str2attr "az")
    toAttrFrTyp n Commonname_xml'lang_ba = Just (n, str2attr "ba")
    toAttrFrTyp n Commonname_xml'lang_be = Just (n, str2attr "be")
    toAttrFrTyp n Commonname_xml'lang_bg = Just (n, str2attr "bg")
    toAttrFrTyp n Commonname_xml'lang_bh = Just (n, str2attr "bh")
    toAttrFrTyp n Commonname_xml'lang_bi = Just (n, str2attr "bi")
    toAttrFrTyp n Commonname_xml'lang_bn = Just (n, str2attr "bn")
    toAttrFrTyp n Commonname_xml'lang_bo = Just (n, str2attr "bo")
    toAttrFrTyp n Commonname_xml'lang_br = Just (n, str2attr "br")
    toAttrFrTyp n Commonname_xml'lang_ca = Just (n, str2attr "ca")
    toAttrFrTyp n Commonname_xml'lang_co = Just (n, str2attr "co")
    toAttrFrTyp n Commonname_xml'lang_cs = Just (n, str2attr "cs")
    toAttrFrTyp n Commonname_xml'lang_cy = Just (n, str2attr "cy")
    toAttrFrTyp n Commonname_xml'lang_da = Just (n, str2attr "da")
    toAttrFrTyp n Commonname_xml'lang_de = Just (n, str2attr "de")
    toAttrFrTyp n Commonname_xml'lang_dz = Just (n, str2attr "dz")
    toAttrFrTyp n Commonname_xml'lang_el = Just (n, str2attr "el")
    toAttrFrTyp n Commonname_xml'lang_en = Just (n, str2attr "en")
    toAttrFrTyp n Commonname_xml'lang_eo = Just (n, str2attr "eo")
    toAttrFrTyp n Commonname_xml'lang_es = Just (n, str2attr "es")
    toAttrFrTyp n Commonname_xml'lang_et = Just (n, str2attr "et")
    toAttrFrTyp n Commonname_xml'lang_eu = Just (n, str2attr "eu")
    toAttrFrTyp n Commonname_xml'lang_fa = Just (n, str2attr "fa")
    toAttrFrTyp n Commonname_xml'lang_fi = Just (n, str2attr "fi")
    toAttrFrTyp n Commonname_xml'lang_fj = Just (n, str2attr "fj")
    toAttrFrTyp n Commonname_xml'lang_fo = Just (n, str2attr "fo")
    toAttrFrTyp n Commonname_xml'lang_fr = Just (n, str2attr "fr")
    toAttrFrTyp n Commonname_xml'lang_fy = Just (n, str2attr "fy")
    toAttrFrTyp n Commonname_xml'lang_ga = Just (n, str2attr "ga")
    toAttrFrTyp n Commonname_xml'lang_gd = Just (n, str2attr "gd")
    toAttrFrTyp n Commonname_xml'lang_gl = Just (n, str2attr "gl")
    toAttrFrTyp n Commonname_xml'lang_gn = Just (n, str2attr "gn")
    toAttrFrTyp n Commonname_xml'lang_gu = Just (n, str2attr "gu")
    toAttrFrTyp n Commonname_xml'lang_ha = Just (n, str2attr "ha")
    toAttrFrTyp n Commonname_xml'lang_he = Just (n, str2attr "he")
    toAttrFrTyp n Commonname_xml'lang_hi = Just (n, str2attr "hi")
    toAttrFrTyp n Commonname_xml'lang_hr = Just (n, str2attr "hr")
    toAttrFrTyp n Commonname_xml'lang_hu = Just (n, str2attr "hu")
    toAttrFrTyp n Commonname_xml'lang_hy = Just (n, str2attr "hy")
    toAttrFrTyp n Commonname_xml'lang_ia = Just (n, str2attr "ia")
    toAttrFrTyp n Commonname_xml'lang_ie = Just (n, str2attr "ie")
    toAttrFrTyp n Commonname_xml'lang_ik = Just (n, str2attr "ik")
    toAttrFrTyp n Commonname_xml'lang_id = Just (n, str2attr "id")
    toAttrFrTyp n Commonname_xml'lang_is = Just (n, str2attr "is")
    toAttrFrTyp n Commonname_xml'lang_it = Just (n, str2attr "it")
    toAttrFrTyp n Commonname_xml'lang_iu = Just (n, str2attr "iu")
    toAttrFrTyp n Commonname_xml'lang_ja = Just (n, str2attr "ja")
    toAttrFrTyp n Commonname_xml'lang_jv = Just (n, str2attr "jv")
    toAttrFrTyp n Commonname_xml'lang_ka = Just (n, str2attr "ka")
    toAttrFrTyp n Commonname_xml'lang_kk = Just (n, str2attr "kk")
    toAttrFrTyp n Commonname_xml'lang_kl = Just (n, str2attr "kl")
    toAttrFrTyp n Commonname_xml'lang_km = Just (n, str2attr "km")
    toAttrFrTyp n Commonname_xml'lang_kn = Just (n, str2attr "kn")
    toAttrFrTyp n Commonname_xml'lang_ko = Just (n, str2attr "ko")
    toAttrFrTyp n Commonname_xml'lang_ks = Just (n, str2attr "ks")
    toAttrFrTyp n Commonname_xml'lang_ku = Just (n, str2attr "ku")
    toAttrFrTyp n Commonname_xml'lang_ky = Just (n, str2attr "ky")
    toAttrFrTyp n Commonname_xml'lang_la = Just (n, str2attr "la")
    toAttrFrTyp n Commonname_xml'lang_ln = Just (n, str2attr "ln")
    toAttrFrTyp n Commonname_xml'lang_lo = Just (n, str2attr "lo")
    toAttrFrTyp n Commonname_xml'lang_lt = Just (n, str2attr "lt")
    toAttrFrTyp n Commonname_xml'lang_lv = Just (n, str2attr "lv")
    toAttrFrTyp n Commonname_xml'lang_mg = Just (n, str2attr "mg")
    toAttrFrTyp n Commonname_xml'lang_mi = Just (n, str2attr "mi")
    toAttrFrTyp n Commonname_xml'lang_mk = Just (n, str2attr "mk")
    toAttrFrTyp n Commonname_xml'lang_ml = Just (n, str2attr "ml")
    toAttrFrTyp n Commonname_xml'lang_mn = Just (n, str2attr "mn")
    toAttrFrTyp n Commonname_xml'lang_mo = Just (n, str2attr "mo")
    toAttrFrTyp n Commonname_xml'lang_mr = Just (n, str2attr "mr")
    toAttrFrTyp n Commonname_xml'lang_ms = Just (n, str2attr "ms")
    toAttrFrTyp n Commonname_xml'lang_mt = Just (n, str2attr "mt")
    toAttrFrTyp n Commonname_xml'lang_my = Just (n, str2attr "my")
    toAttrFrTyp n Commonname_xml'lang_na = Just (n, str2attr "na")
    toAttrFrTyp n Commonname_xml'lang_ne = Just (n, str2attr "ne")
    toAttrFrTyp n Commonname_xml'lang_nl = Just (n, str2attr "nl")
    toAttrFrTyp n Commonname_xml'lang_no = Just (n, str2attr "no")
    toAttrFrTyp n Commonname_xml'lang_oc = Just (n, str2attr "oc")
    toAttrFrTyp n Commonname_xml'lang_om = Just (n, str2attr "om")
    toAttrFrTyp n Commonname_xml'lang_or = Just (n, str2attr "or")
    toAttrFrTyp n Commonname_xml'lang_pa = Just (n, str2attr "pa")
    toAttrFrTyp n Commonname_xml'lang_pl = Just (n, str2attr "pl")
    toAttrFrTyp n Commonname_xml'lang_ps = Just (n, str2attr "ps")
    toAttrFrTyp n Commonname_xml'lang_pt = Just (n, str2attr "pt")
    toAttrFrTyp n Commonname_xml'lang_qu = Just (n, str2attr "qu")
    toAttrFrTyp n Commonname_xml'lang_rm = Just (n, str2attr "rm")
    toAttrFrTyp n Commonname_xml'lang_rn = Just (n, str2attr "rn")
    toAttrFrTyp n Commonname_xml'lang_ro = Just (n, str2attr "ro")
    toAttrFrTyp n Commonname_xml'lang_ru = Just (n, str2attr "ru")
    toAttrFrTyp n Commonname_xml'lang_rw = Just (n, str2attr "rw")
    toAttrFrTyp n Commonname_xml'lang_sa = Just (n, str2attr "sa")
    toAttrFrTyp n Commonname_xml'lang_sd = Just (n, str2attr "sd")
    toAttrFrTyp n Commonname_xml'lang_sg = Just (n, str2attr "sg")
    toAttrFrTyp n Commonname_xml'lang_sh = Just (n, str2attr "sh")
    toAttrFrTyp n Commonname_xml'lang_si = Just (n, str2attr "si")
    toAttrFrTyp n Commonname_xml'lang_sk = Just (n, str2attr "sk")
    toAttrFrTyp n Commonname_xml'lang_sl = Just (n, str2attr "sl")
    toAttrFrTyp n Commonname_xml'lang_sm = Just (n, str2attr "sm")
    toAttrFrTyp n Commonname_xml'lang_sn = Just (n, str2attr "sn")
    toAttrFrTyp n Commonname_xml'lang_so = Just (n, str2attr "so")
    toAttrFrTyp n Commonname_xml'lang_sq = Just (n, str2attr "sq")
    toAttrFrTyp n Commonname_xml'lang_sr = Just (n, str2attr "sr")
    toAttrFrTyp n Commonname_xml'lang_ss = Just (n, str2attr "ss")
    toAttrFrTyp n Commonname_xml'lang_st = Just (n, str2attr "st")
    toAttrFrTyp n Commonname_xml'lang_su = Just (n, str2attr "su")
    toAttrFrTyp n Commonname_xml'lang_sv = Just (n, str2attr "sv")
    toAttrFrTyp n Commonname_xml'lang_sw = Just (n, str2attr "sw")
    toAttrFrTyp n Commonname_xml'lang_ta = Just (n, str2attr "ta")
    toAttrFrTyp n Commonname_xml'lang_te = Just (n, str2attr "te")
    toAttrFrTyp n Commonname_xml'lang_tg = Just (n, str2attr "tg")
    toAttrFrTyp n Commonname_xml'lang_th = Just (n, str2attr "th")
    toAttrFrTyp n Commonname_xml'lang_ti = Just (n, str2attr "ti")
    toAttrFrTyp n Commonname_xml'lang_tk = Just (n, str2attr "tk")
    toAttrFrTyp n Commonname_xml'lang_tl = Just (n, str2attr "tl")
    toAttrFrTyp n Commonname_xml'lang_tn = Just (n, str2attr "tn")
    toAttrFrTyp n Commonname_xml'lang_to = Just (n, str2attr "to")
    toAttrFrTyp n Commonname_xml'lang_tr = Just (n, str2attr "tr")
    toAttrFrTyp n Commonname_xml'lang_ts = Just (n, str2attr "ts")
    toAttrFrTyp n Commonname_xml'lang_tt = Just (n, str2attr "tt")
    toAttrFrTyp n Commonname_xml'lang_tw = Just (n, str2attr "tw")
    toAttrFrTyp n Commonname_xml'lang_ug = Just (n, str2attr "ug")
    toAttrFrTyp n Commonname_xml'lang_uk = Just (n, str2attr "uk")
    toAttrFrTyp n Commonname_xml'lang_ur = Just (n, str2attr "ur")
    toAttrFrTyp n Commonname_xml'lang_uz = Just (n, str2attr "uz")
    toAttrFrTyp n Commonname_xml'lang_vi = Just (n, str2attr "vi")
    toAttrFrTyp n Commonname_xml'lang_vo = Just (n, str2attr "vo")
    toAttrFrTyp n Commonname_xml'lang_wo = Just (n, str2attr "wo")
    toAttrFrTyp n Commonname_xml'lang_xh = Just (n, str2attr "xh")
    toAttrFrTyp n Commonname_xml'lang_yi = Just (n, str2attr "yi")
    toAttrFrTyp n Commonname_xml'lang_yo = Just (n, str2attr "yo")
    toAttrFrTyp n Commonname_xml'lang_za = Just (n, str2attr "za")
    toAttrFrTyp n Commonname_xml'lang_zh = Just (n, str2attr "zh")
    toAttrFrTyp n Commonname_xml'lang_zu = Just (n, str2attr "zu")
instance XmlContent Type where
    fromElem (CElem (Elem "type" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Type (fromAttrs as) a b), rest))
	   (definite fromElem "<OMOBJ>" "type" ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Type as a b) =
	[CElem (Elem "type" (toAttrs as) (concatMap toElem a ++ toElem b))]
instance XmlAttributes Type_Attrs where
    fromAttrs as =
	Type_Attrs
	  { typeId = possibleA fromAttrToStr "id" as
	  , typeStyle = possibleA fromAttrToStr "style" as
	  , typeMid = possibleA fromAttrToStr "mid" as
	  , typeFor = possibleA fromAttrToStr "for" as
	  , typeSystem = definiteA fromAttrToStr "type" "system" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (typeId v)
	, maybeToAttr toAttrFrStr "style" (typeStyle v)
	, maybeToAttr toAttrFrStr "mid" (typeMid v)
	, maybeToAttr toAttrFrStr "for" (typeFor v)
	, toAttrFrStr "system" (typeSystem v)
	]
instance XmlContent FMP where
    fromElem (CElem (Elem "FMP" as c0):rest) =
	case (fromElem c0) of
	(Just a,_) -> (Just (FMPAssumption_Conclusion (fromAttrs as) a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,_) -> (Just (FMPOMOBJ (fromAttrs as) a), rest)
		(_,_) ->
		    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (FMPAssumption_Conclusion as a) = [CElem (Elem "FMP" (toAttrs as) (toElem a) )]
    toElem (FMPOMOBJ as a) = [CElem (Elem "FMP" (toAttrs as) (toElem a) )]
instance XmlAttributes FMP_Attrs where
    fromAttrs as =
	FMP_Attrs
	  { fMPLogic = possibleA fromAttrToStr "logic" as
	  , fMPMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "logic" (fMPLogic v)
	, maybeToAttr toAttrFrStr "mid" (fMPMid v)
	]
instance XmlContent Assumption where
    fromElem (CElem (Elem "assumption" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Assumption (fromAttrs as) a b), rest))
	   (fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Assumption as a b) =
	[CElem (Elem "assumption" (toAttrs as) (concatMap toElem a ++
						maybe [] toElem b))]
instance XmlAttributes Assumption_Attrs where
    fromAttrs as =
	Assumption_Attrs
	  { assumptionId = definiteA fromAttrToStr "assumption" "id" as
	  , assumptionStyle = possibleA fromAttrToStr "style" as
	  , assumptionMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (assumptionId v)
	, maybeToAttr toAttrFrStr "style" (assumptionStyle v)
	, maybeToAttr toAttrFrStr "mid" (assumptionMid v)
	]
instance XmlContent Conclusion where
    fromElem (CElem (Elem "conclusion" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Conclusion (fromAttrs as) a b), rest))
	   (fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Conclusion as a b) =
	[CElem (Elem "conclusion" (toAttrs as) (concatMap toElem a ++
						maybe [] toElem b))]
instance XmlAttributes Conclusion_Attrs where
    fromAttrs as =
	Conclusion_Attrs
	  { conclusionId = definiteA fromAttrToStr "conclusion" "id" as
	  , conclusionStyle = possibleA fromAttrToStr "style" as
	  , conclusionMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (conclusionId v)
	, maybeToAttr toAttrFrStr "style" (conclusionStyle v)
	, maybeToAttr toAttrFrStr "mid" (conclusionMid v)
	]
instance XmlContent Axiom where
    fromElem (CElem (Elem "axiom" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Axiom (fromAttrs as) a b c d), rest))
		 (many fromElem cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Axiom as a b c d) =
	[CElem (Elem "axiom" (toAttrs as) (maybe [] toElem a ++
					   concatMap toElem b ++ concatMap toElem c ++
					   concatMap toElem d))]
instance XmlAttributes Axiom_Attrs where
    fromAttrs as =
	Axiom_Attrs
	  { axiomId = definiteA fromAttrToStr "axiom" "id" as
	  , axiomStyle = possibleA fromAttrToStr "style" as
	  , axiomMid = possibleA fromAttrToStr "mid" as
	  , axiomGenerated_by = possibleA fromAttrToStr "generated-by" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (axiomId v)
	, maybeToAttr toAttrFrStr "style" (axiomStyle v)
	, maybeToAttr toAttrFrStr "mid" (axiomMid v)
	, maybeToAttr toAttrFrStr "generated-by" (axiomGenerated_by v)
	]
instance XmlContent Definition where
    fromElem (CElem (Elem "definition" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (\(e,ce)->
		       (\(f,cf)->
			  (Just (Definition (fromAttrs as) a b c d e f), rest))
		       (fromElem ce))
		    (fromElem cd))
		 (fromElem cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Definition as a b c d e f) =
	[CElem (Elem "definition" (toAttrs as) (maybe [] toElem a ++
						concatMap toElem b ++ concatMap toElem c ++
						maybe [] toElem d ++ maybe [] toElem e ++
						maybe [] toElem f))]
instance XmlAttributes Definition_Attrs where
    fromAttrs as =
	Definition_Attrs
	  { definitionJust_by = possibleA fromAttrToStr "just-by" as
	  , definitionType = defaultA fromAttrToTyp Definition_type_simple "type" as
	  , definitionGenerated_by = possibleA fromAttrToStr "generated-by" as
	  , definitionId = definiteA fromAttrToStr "definition" "id" as
	  , definitionStyle = possibleA fromAttrToStr "style" as
	  , definitionMid = possibleA fromAttrToStr "mid" as
	  , definitionFor = definiteA fromAttrToStr "definition" "for" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "just-by" (definitionJust_by v)
	, defaultToAttr toAttrFrTyp "type" (definitionType v)
	, maybeToAttr toAttrFrStr "generated-by" (definitionGenerated_by v)
	, toAttrFrStr "id" (definitionId v)
	, maybeToAttr toAttrFrStr "style" (definitionStyle v)
	, maybeToAttr toAttrFrStr "mid" (definitionMid v)
	, toAttrFrStr "for" (definitionFor v)
	]
instance XmlAttrType Definition_type where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "simple" = Just Definition_type_simple
	    translate "inductive" = Just Definition_type_inductive
	    translate "implicit" = Just Definition_type_implicit
	    translate "recursive" = Just Definition_type_recursive
	    translate "obj" = Just Definition_type_obj
	    translate _ = Nothing
    toAttrFrTyp n Definition_type_simple = Just (n, str2attr "simple")
    toAttrFrTyp n Definition_type_inductive = Just (n, str2attr "inductive")
    toAttrFrTyp n Definition_type_implicit = Just (n, str2attr "implicit")
    toAttrFrTyp n Definition_type_recursive = Just (n, str2attr "recursive")
    toAttrFrTyp n Definition_type_obj = Just (n, str2attr "obj")
instance XmlContent Requation where
    fromElem (CElem (Elem "requation" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Requation (fromAttrs as) a b), rest))
	   (definite fromElem "<value>" "requation" ca))
	(definite fromElem "<pattern>" "requation" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Requation as a b) =
	[CElem (Elem "requation" (toAttrs as) (toElem a ++ toElem b))]
instance XmlAttributes Requation_Attrs where
    fromAttrs as =
	Requation_Attrs
	  { requationId = possibleA fromAttrToStr "id" as
	  , requationStyle = possibleA fromAttrToStr "style" as
	  , requationMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (requationId v)
	, maybeToAttr toAttrFrStr "style" (requationStyle v)
	, maybeToAttr toAttrFrStr "mid" (requationMid v)
	]
instance XmlContent Pattern where
    fromElem (CElem (Elem "pattern" [] c0):rest) =
	(\(a,ca)->
	   (Just (Pattern a), rest))
	(definite fromElem "<OMOBJ>" "pattern" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Pattern a) =
	[CElem (Elem "pattern" [] (toElem a))]
instance XmlContent Value where
    fromElem (CElem (Elem "value" [] c0):rest) =
	(\(a,ca)->
	   (Just (Value a), rest))
	(definite fromElem "<OMOBJ>" "value" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Value a) =
	[CElem (Elem "value" [] (toElem a))]
instance XmlContent Measure where
    fromElem (CElem (Elem "measure" as c0):rest) =
	(\(a,ca)->
	   (Just (Measure (fromAttrs as) a), rest))
	(definite fromElem "<OMOBJ>" "measure" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Measure as a) =
	[CElem (Elem "measure" (toAttrs as) (toElem a))]
instance XmlAttributes Measure_Attrs where
    fromAttrs as =
	Measure_Attrs
	  { measureMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (measureMid v)
	]
instance XmlContent Omdoc.Ordering where
    fromElem (CElem (Elem "ordering" as c0):rest) =
	(\(a,ca)->
	   (Just (Ordering (fromAttrs as) a), rest))
	(definite fromElem "<OMOBJ>" "ordering" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Ordering as a) =
	[CElem (Elem "ordering" (toAttrs as) (toElem a))]
instance XmlAttributes Ordering_Attrs where
    fromAttrs as =
	Ordering_Attrs
	  { orderingMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (orderingMid v)
	]
instance XmlContent Adt where
    fromElem (CElem (Elem "adt" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Adt (fromAttrs as) a b c d), rest))
		 (definite fromElem "sortdef+" "adt" cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Adt as a b c d) =
	[CElem (Elem "adt" (toAttrs as) (maybe [] toElem a ++
					 concatMap toElem b ++ concatMap toElem c ++ toElem d))]
instance XmlAttributes Adt_Attrs where
    fromAttrs as =
	Adt_Attrs
	  { adtType = defaultA fromAttrToTyp Adt_type_loose "type" as
	  , adtId = definiteA fromAttrToStr "adt" "id" as
	  , adtStyle = possibleA fromAttrToStr "style" as
	  , adtMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrTyp "type" (adtType v)
	, toAttrFrStr "id" (adtId v)
	, maybeToAttr toAttrFrStr "style" (adtStyle v)
	, maybeToAttr toAttrFrStr "mid" (adtMid v)
	]
instance XmlAttrType Adt_type where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "loose" = Just Adt_type_loose
	    translate "generated" = Just Adt_type_generated
	    translate "free" = Just Adt_type_free
	    translate _ = Nothing
    toAttrFrTyp n Adt_type_loose = Just (n, str2attr "loose")
    toAttrFrTyp n Adt_type_generated = Just (n, str2attr "generated")
    toAttrFrTyp n Adt_type_free = Just (n, str2attr "free")
instance XmlContent Sortdef where
    fromElem (CElem (Elem "sortdef" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (Just (Sortdef (fromAttrs as) a b c), rest))
	      (fromElem cb))
	   (many fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Sortdef as a b c) =
	[CElem (Elem "sortdef" (toAttrs as) (concatMap toElem a ++
					     concatMap toElem b ++ maybe [] toElem c))]
instance XmlAttributes Sortdef_Attrs where
    fromAttrs as =
	Sortdef_Attrs
	  { sortdefId = definiteA fromAttrToStr "sortdef" "id" as
	  , sortdefStyle = possibleA fromAttrToStr "style" as
	  , sortdefMid = possibleA fromAttrToStr "mid" as
	  , sortdefScope = defaultA fromAttrToTyp Sortdef_scope_global "scope" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (sortdefId v)
	, maybeToAttr toAttrFrStr "style" (sortdefStyle v)
	, maybeToAttr toAttrFrStr "mid" (sortdefMid v)
	, defaultToAttr toAttrFrTyp "scope" (sortdefScope v)
	]
instance XmlAttrType Sortdef_scope where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "global" = Just Sortdef_scope_global
	    translate "local" = Just Sortdef_scope_local
	    translate _ = Nothing
    toAttrFrTyp n Sortdef_scope_global = Just (n, str2attr "global")
    toAttrFrTyp n Sortdef_scope_local = Just (n, str2attr "local")
instance XmlContent Insort where
    fromElem (CElem (Elem "insort" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "insort" (toAttrs as) [])]
instance XmlAttributes Insort where
    fromAttrs as =
	Insort
	  { insortFor = definiteA fromAttrToStr "insort" "for" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "for" (insortFor v)
	]
instance XmlContent Constructor where
    fromElem (CElem (Elem "constructor" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Constructor (fromAttrs as) a b), rest))
	   (many fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Constructor as a b) =
	[CElem (Elem "constructor" (toAttrs as) (concatMap toElem a ++
						 concatMap toElem b))]
instance XmlAttributes Constructor_Attrs where
    fromAttrs as =
	Constructor_Attrs
	  { constructorId = definiteA fromAttrToStr "constructor" "id" as
	  , constructorStyle = possibleA fromAttrToStr "style" as
	  , constructorMid = possibleA fromAttrToStr "mid" as
	  , constructorKind = defaultA fromAttrToTyp Constructor_kind_object "kind" as
	  , constructorScope = defaultA fromAttrToTyp Constructor_scope_global "scope" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (constructorId v)
	, maybeToAttr toAttrFrStr "style" (constructorStyle v)
	, maybeToAttr toAttrFrStr "mid" (constructorMid v)
	, defaultToAttr toAttrFrTyp "kind" (constructorKind v)
	, defaultToAttr toAttrFrTyp "scope" (constructorScope v)
	]
instance XmlAttrType Constructor_kind where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "type" = Just Constructor_kind_type
	    translate "sort" = Just Constructor_kind_sort
	    translate "object" = Just Constructor_kind_object
	    translate _ = Nothing
    toAttrFrTyp n Constructor_kind_type = Just (n, str2attr "type")
    toAttrFrTyp n Constructor_kind_sort = Just (n, str2attr "sort")
    toAttrFrTyp n Constructor_kind_object = Just (n, str2attr "object")
instance XmlAttrType Constructor_scope where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "global" = Just Constructor_scope_global
	    translate "local" = Just Constructor_scope_local
	    translate _ = Nothing
    toAttrFrTyp n Constructor_scope_global = Just (n, str2attr "global")
    toAttrFrTyp n Constructor_scope_local = Just (n, str2attr "local")
instance XmlContent Recognizer where
    fromElem (CElem (Elem "recognizer" as c0):rest) =
	(\(a,ca)->
	   (Just (Recognizer (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Recognizer as a) =
	[CElem (Elem "recognizer" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Recognizer_Attrs where
    fromAttrs as =
	Recognizer_Attrs
	  { recognizerId = definiteA fromAttrToStr "recognizer" "id" as
	  , recognizerStyle = possibleA fromAttrToStr "style" as
	  , recognizerMid = possibleA fromAttrToStr "mid" as
	  , recognizerKind = defaultA fromAttrToTyp Recognizer_kind_object "kind" as
	  , recognizerScope = defaultA fromAttrToTyp Recognizer_scope_global "scope" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (recognizerId v)
	, maybeToAttr toAttrFrStr "style" (recognizerStyle v)
	, maybeToAttr toAttrFrStr "mid" (recognizerMid v)
	, defaultToAttr toAttrFrTyp "kind" (recognizerKind v)
	, defaultToAttr toAttrFrTyp "scope" (recognizerScope v)
	]
instance XmlAttrType Recognizer_kind where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "type" = Just Recognizer_kind_type
	    translate "sort" = Just Recognizer_kind_sort
	    translate "object" = Just Recognizer_kind_object
	    translate _ = Nothing
    toAttrFrTyp n Recognizer_kind_type = Just (n, str2attr "type")
    toAttrFrTyp n Recognizer_kind_sort = Just (n, str2attr "sort")
    toAttrFrTyp n Recognizer_kind_object = Just (n, str2attr "object")
instance XmlAttrType Recognizer_scope where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "global" = Just Recognizer_scope_global
	    translate "local" = Just Recognizer_scope_local
	    translate _ = Nothing
    toAttrFrTyp n Recognizer_scope_global = Just (n, str2attr "global")
    toAttrFrTyp n Recognizer_scope_local = Just (n, str2attr "local")
instance XmlContent Argument where
    fromElem (CElem (Elem "argument" as c0):rest) =
	(\(a,ca)->
	   (Just (Argument (fromAttrs as) a), rest))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Argument as a) =
	[CElem (Elem "argument" (toAttrs as) (maybe [] toElem a))]
instance XmlAttributes Argument_Attrs where
    fromAttrs as =
	Argument_Attrs
	  { argumentSort = definiteA fromAttrToStr "argument" "sort" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "sort" (argumentSort v)
	]
instance XmlContent Selector where
    fromElem (CElem (Elem "selector" as c0):rest) =
	(\(a,ca)->
	   (Just (Selector (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Selector as a) =
	[CElem (Elem "selector" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Selector_Attrs where
    fromAttrs as =
	Selector_Attrs
	  { selectorId = definiteA fromAttrToStr "selector" "id" as
	  , selectorStyle = possibleA fromAttrToStr "style" as
	  , selectorMid = possibleA fromAttrToStr "mid" as
	  , selectorKind = defaultA fromAttrToTyp Selector_kind_object "kind" as
	  , selectorScope = defaultA fromAttrToTyp Selector_scope_global "scope" as
	  , selectorTotal = defaultA fromAttrToTyp Selector_total_no "total" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (selectorId v)
	, maybeToAttr toAttrFrStr "style" (selectorStyle v)
	, maybeToAttr toAttrFrStr "mid" (selectorMid v)
	, defaultToAttr toAttrFrTyp "kind" (selectorKind v)
	, defaultToAttr toAttrFrTyp "scope" (selectorScope v)
	, defaultToAttr toAttrFrTyp "total" (selectorTotal v)
	]
instance XmlAttrType Selector_kind where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "type" = Just Selector_kind_type
	    translate "sort" = Just Selector_kind_sort
	    translate "object" = Just Selector_kind_object
	    translate _ = Nothing
    toAttrFrTyp n Selector_kind_type = Just (n, str2attr "type")
    toAttrFrTyp n Selector_kind_sort = Just (n, str2attr "sort")
    toAttrFrTyp n Selector_kind_object = Just (n, str2attr "object")
instance XmlAttrType Selector_scope where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "global" = Just Selector_scope_global
	    translate "local" = Just Selector_scope_local
	    translate _ = Nothing
    toAttrFrTyp n Selector_scope_global = Just (n, str2attr "global")
    toAttrFrTyp n Selector_scope_local = Just (n, str2attr "local")
instance XmlAttrType Selector_total where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "yes" = Just Selector_total_yes
	    translate "no" = Just Selector_total_no
	    translate _ = Nothing
    toAttrFrTyp n Selector_total_yes = Just (n, str2attr "yes")
    toAttrFrTyp n Selector_total_no = Just (n, str2attr "no")
instance XmlContent Assertion where
    fromElem (CElem (Elem "assertion" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Assertion (fromAttrs as) a b c d), rest))
		 (many fromElem cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Assertion as a b c d) =
	[CElem (Elem "assertion" (toAttrs as) (maybe [] toElem a ++
					       concatMap toElem b ++ concatMap toElem c ++
					       concatMap toElem d))]
instance XmlAttributes Assertion_Attrs where
    fromAttrs as =
	Assertion_Attrs
	  { assertionId = definiteA fromAttrToStr "assertion" "id" as
	  , assertionStyle = possibleA fromAttrToStr "style" as
	  , assertionMid = possibleA fromAttrToStr "mid" as
	  , assertionGenerated_by = possibleA fromAttrToStr "generated-by" as
	  , assertionTheory = possibleA fromAttrToStr "theory" as
	  , assertionType = defaultA fromAttrToTyp Assertion_type_conjecture "type" as
	  , assertionProofs = possibleA fromAttrToStr "proofs" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (assertionId v)
	, maybeToAttr toAttrFrStr "style" (assertionStyle v)
	, maybeToAttr toAttrFrStr "mid" (assertionMid v)
	, maybeToAttr toAttrFrStr "generated-by" (assertionGenerated_by v)
	, maybeToAttr toAttrFrStr "theory" (assertionTheory v)
	, defaultToAttr toAttrFrTyp "type" (assertionType v)
	, maybeToAttr toAttrFrStr "proofs" (assertionProofs v)
	]
instance XmlAttrType Assertion_type where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "theorem" = Just Assertion_type_theorem
	    translate "lemma" = Just Assertion_type_lemma
	    translate "corollary" = Just Assertion_type_corollary
	    translate "conjecture" = Just Assertion_type_conjecture
	    translate "false-conjecture" = Just Assertion_type_false_conjecture
	    translate "obligation" = Just Assertion_type_obligation
	    translate "postulate" = Just Assertion_type_postulate
	    translate "formula" = Just Assertion_type_formula
	    translate "assumption" = Just Assertion_type_assumption
	    translate "proposition" = Just Assertion_type_proposition
	    translate _ = Nothing
    toAttrFrTyp n Assertion_type_theorem = Just (n, str2attr "theorem")
    toAttrFrTyp n Assertion_type_lemma = Just (n, str2attr "lemma")
    toAttrFrTyp n Assertion_type_corollary = Just (n, str2attr "corollary")
    toAttrFrTyp n Assertion_type_conjecture = Just (n, str2attr "conjecture")
    toAttrFrTyp n Assertion_type_false_conjecture = Just (n, str2attr "false-conjecture")
    toAttrFrTyp n Assertion_type_obligation = Just (n, str2attr "obligation")
    toAttrFrTyp n Assertion_type_postulate = Just (n, str2attr "postulate")
    toAttrFrTyp n Assertion_type_formula = Just (n, str2attr "formula")
    toAttrFrTyp n Assertion_type_assumption = Just (n, str2attr "assumption")
    toAttrFrTyp n Assertion_type_proposition = Just (n, str2attr "proposition")
instance XmlContent Alternative where
    fromElem (CElem (Elem "alternative" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (Just (Alternative (fromAttrs as) a b c), rest))
	      (definite fromElem "OneOf" "alternative" cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Alternative as a b c) =
	[CElem (Elem "alternative" (toAttrs as) (maybe [] toElem a ++
						 concatMap toElem b ++ toElem c))]
instance XmlAttributes Alternative_Attrs where
    fromAttrs as =
	Alternative_Attrs
	  { alternativeTheory = definiteA fromAttrToStr "alternative" "theory" as
	  , alternativeType = defaultA fromAttrToTyp Alternative_type_simple "type" as
	  , alternativeGenerated_by = possibleA fromAttrToStr "generated-by" as
	  , alternativeJust_by = possibleA fromAttrToStr "just-by" as
	  , alternativeEntailed_by = definiteA fromAttrToStr "alternative" "entailed-by" as
	  , alternativeEntails = definiteA fromAttrToStr "alternative" "entails" as
	  , alternativeEntailed_by_thm = definiteA fromAttrToStr "alternative" "entailed-by-thm" as
	  , alternativeEntails_thm = definiteA fromAttrToStr "alternative" "entails-thm" as
	  , alternativeId = definiteA fromAttrToStr "alternative" "id" as
	  , alternativeStyle = possibleA fromAttrToStr "style" as
	  , alternativeMid = possibleA fromAttrToStr "mid" as
	  , alternativeFor = definiteA fromAttrToStr "alternative" "for" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "theory" (alternativeTheory v)
	, defaultToAttr toAttrFrTyp "type" (alternativeType v)
	, maybeToAttr toAttrFrStr "generated-by" (alternativeGenerated_by v)
	, maybeToAttr toAttrFrStr "just-by" (alternativeJust_by v)
	, toAttrFrStr "entailed-by" (alternativeEntailed_by v)
	, toAttrFrStr "entails" (alternativeEntails v)
	, toAttrFrStr "entailed-by-thm" (alternativeEntailed_by_thm v)
	, toAttrFrStr "entails-thm" (alternativeEntails_thm v)
	, toAttrFrStr "id" (alternativeId v)
	, maybeToAttr toAttrFrStr "style" (alternativeStyle v)
	, maybeToAttr toAttrFrStr "mid" (alternativeMid v)
	, toAttrFrStr "for" (alternativeFor v)
	]
instance XmlAttrType Alternative_type where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "simple" = Just Alternative_type_simple
	    translate "inductive" = Just Alternative_type_inductive
	    translate "implicit" = Just Alternative_type_implicit
	    translate "recursive" = Just Alternative_type_recursive
	    translate "obj" = Just Alternative_type_obj
	    translate _ = Nothing
    toAttrFrTyp n Alternative_type_simple = Just (n, str2attr "simple")
    toAttrFrTyp n Alternative_type_inductive = Just (n, str2attr "inductive")
    toAttrFrTyp n Alternative_type_implicit = Just (n, str2attr "implicit")
    toAttrFrTyp n Alternative_type_recursive = Just (n, str2attr "recursive")
    toAttrFrTyp n Alternative_type_obj = Just (n, str2attr "obj")
instance XmlContent Proof where
    fromElem (CElem (Elem "proof" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (\(e,ce)->
		       (Just (Proof (fromAttrs as) a b c d e), rest))
		    (definite fromElem "<conclude>" "proof" cd))
		 (many fromElem cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Proof as a b c d e) =
	[CElem (Elem "proof" (toAttrs as) (maybe [] toElem a ++
					   concatMap toElem b ++ concatMap toElem c ++
					   concatMap toElem d ++ toElem e))]
instance XmlAttributes Proof_Attrs where
    fromAttrs as =
	Proof_Attrs
	  { proofTheory = possibleA fromAttrToStr "theory" as
	  , proofId = definiteA fromAttrToStr "proof" "id" as
	  , proofStyle = possibleA fromAttrToStr "style" as
	  , proofMid = possibleA fromAttrToStr "mid" as
	  , proofFor = definiteA fromAttrToStr "proof" "for" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "theory" (proofTheory v)
	, toAttrFrStr "id" (proofId v)
	, maybeToAttr toAttrFrStr "style" (proofStyle v)
	, maybeToAttr toAttrFrStr "mid" (proofMid v)
	, toAttrFrStr "for" (proofFor v)
	]
instance XmlContent Proofobject where
    fromElem (CElem (Elem "proofobject" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (Just (Proofobject (fromAttrs as) a b c), rest))
	      (definite fromElem "<OMOBJ>" "proofobject" cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Proofobject as a b c) =
	[CElem (Elem "proofobject" (toAttrs as) (maybe [] toElem a ++
						 concatMap toElem b ++ toElem c))]
instance XmlAttributes Proofobject_Attrs where
    fromAttrs as =
	Proofobject_Attrs
	  { proofobjectTheory = possibleA fromAttrToStr "theory" as
	  , proofobjectId = definiteA fromAttrToStr "proofobject" "id" as
	  , proofobjectStyle = possibleA fromAttrToStr "style" as
	  , proofobjectMid = possibleA fromAttrToStr "mid" as
	  , proofobjectFor = definiteA fromAttrToStr "proofobject" "for" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "theory" (proofobjectTheory v)
	, toAttrFrStr "id" (proofobjectId v)
	, maybeToAttr toAttrFrStr "style" (proofobjectStyle v)
	, maybeToAttr toAttrFrStr "mid" (proofobjectMid v)
	, toAttrFrStr "for" (proofobjectFor v)
	]
instance XmlContent Metacomment where
    fromElem (CElem (Elem "metacomment" as c0):rest) =
	(\(a,ca)->
	   (Just (Metacomment (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Metacomment as a) =
	[CElem (Elem "metacomment" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Metacomment_Attrs where
    fromAttrs as =
	Metacomment_Attrs
	  { metacommentId = possibleA fromAttrToStr "id" as
	  , metacommentStyle = possibleA fromAttrToStr "style" as
	  , metacommentMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (metacommentId v)
	, maybeToAttr toAttrFrStr "style" (metacommentStyle v)
	, maybeToAttr toAttrFrStr "mid" (metacommentMid v)
	]
instance XmlContent Derive where
    fromElem (CElem (Elem "derive" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (\(e,ce)->
		       (Just (Derive (fromAttrs as) a b c d e), rest))
		    (fromElem cd))
		 (many fromElem cc))
	      (fromElem cb))
	   (fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Derive as a b c d e) =
	[CElem (Elem "derive" (toAttrs as) (concatMap toElem a ++
					    maybe [] toElem b ++ maybe [] toElem c ++
					    concatMap toElem d ++ maybe [] toElem e))]
instance XmlAttributes Derive_Attrs where
    fromAttrs as =
	Derive_Attrs
	  { deriveId = definiteA fromAttrToStr "derive" "id" as
	  , deriveStyle = possibleA fromAttrToStr "style" as
	  , deriveMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (deriveId v)
	, maybeToAttr toAttrFrStr "style" (deriveStyle v)
	, maybeToAttr toAttrFrStr "mid" (deriveMid v)
	]
instance XmlContent Conclude where
    fromElem (CElem (Elem "conclude" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Conclude (fromAttrs as) a b c d), rest))
		 (fromElem cc))
	      (many fromElem cb))
	   (fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Conclude as a b c d) =
	[CElem (Elem "conclude" (toAttrs as) (concatMap toElem a ++
					      maybe [] toElem b ++ concatMap toElem c ++
					      maybe [] toElem d))]
instance XmlAttributes Conclude_Attrs where
    fromAttrs as =
	Conclude_Attrs
	  { concludeId = possibleA fromAttrToStr "id" as
	  , concludeStyle = possibleA fromAttrToStr "style" as
	  , concludeMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (concludeId v)
	, maybeToAttr toAttrFrStr "style" (concludeStyle v)
	, maybeToAttr toAttrFrStr "mid" (concludeMid v)
	]
instance XmlContent Hypothesis where
    fromElem (CElem (Elem "hypothesis" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (Just (Hypothesis (fromAttrs as) a b c), rest))
	      (fromElem cb))
	   (many fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Hypothesis as a b c) =
	[CElem (Elem "hypothesis" (toAttrs as) (concatMap toElem a ++
						concatMap toElem b ++ maybe [] toElem c))]
instance XmlAttributes Hypothesis_Attrs where
    fromAttrs as =
	Hypothesis_Attrs
	  { hypothesisId = definiteA fromAttrToStr "hypothesis" "id" as
	  , hypothesisStyle = possibleA fromAttrToStr "style" as
	  , hypothesisMid = possibleA fromAttrToStr "mid" as
	  , hypothesisDischarged_in = definiteA fromAttrToStr "hypothesis" "discharged-in" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (hypothesisId v)
	, maybeToAttr toAttrFrStr "style" (hypothesisStyle v)
	, maybeToAttr toAttrFrStr "mid" (hypothesisMid v)
	, toAttrFrStr "discharged-in" (hypothesisDischarged_in v)
	]
instance XmlContent Method where
    fromElem (CElem (Elem "method" as c0):rest) =
	(\(a,ca)->
	   (Just (Method (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Method as a) =
	[CElem (Elem "method" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Method_Attrs where
    fromAttrs as =
	Method_Attrs
	  { methodXref = definiteA fromAttrToStr "method" "xref" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "xref" (methodXref v)
	]
instance XmlContent Premise where
    fromElem (CElem (Elem "premise" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "premise" (toAttrs as) [])]
instance XmlAttributes Premise where
    fromAttrs as =
	Premise
	  { premiseXref = definiteA fromAttrToStr "premise" "xref" as
	  , premiseRank = defaultA fromAttrToStr "0" "rank" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "xref" (premiseXref v)
	, defaultToAttr toAttrFrStr "rank" (premiseRank v)
	]
instance XmlContent Example where
    fromElem (CElem (Elem "example" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Example (fromAttrs as) a b c d), rest))
		 (many fromElem cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Example as a b c d) =
	[CElem (Elem "example" (toAttrs as) (maybe [] toElem a ++
					     concatMap toElem b ++ concatMap toElem c ++
					     concatMap toElem d))]
instance XmlAttributes Example_Attrs where
    fromAttrs as =
	Example_Attrs
	  { exampleType = possibleA fromAttrToTyp "type" as
	  , exampleAssertion = possibleA fromAttrToStr "assertion" as
	  , exampleId = definiteA fromAttrToStr "example" "id" as
	  , exampleStyle = possibleA fromAttrToStr "style" as
	  , exampleMid = possibleA fromAttrToStr "mid" as
	  , exampleFor = definiteA fromAttrToStr "example" "for" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrTyp "type" (exampleType v)
	, maybeToAttr toAttrFrStr "assertion" (exampleAssertion v)
	, toAttrFrStr "id" (exampleId v)
	, maybeToAttr toAttrFrStr "style" (exampleStyle v)
	, maybeToAttr toAttrFrStr "mid" (exampleMid v)
	, toAttrFrStr "for" (exampleFor v)
	]
instance XmlAttrType Example_type where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "for" = Just Example_type_for
	    translate "against" = Just Example_type_against
	    translate _ = Nothing
    toAttrFrTyp n Example_type_for = Just (n, str2attr "for")
    toAttrFrTyp n Example_type_against = Just (n, str2attr "against")
instance XmlContent Theory where
    fromElem (CElem (Elem "theory" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Theory (fromAttrs as) a b c d), rest))
		 (many fromElem cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Theory as a b c d) =
	[CElem (Elem "theory" (toAttrs as) (maybe [] toElem a ++
					    concatMap toElem b ++ concatMap toElem c ++
					    concatMap toElem d))]
instance XmlAttributes Theory_Attrs where
    fromAttrs as =
	Theory_Attrs
	  { theoryId = definiteA fromAttrToStr "theory" "id" as
	  , theoryStyle = possibleA fromAttrToStr "style" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (theoryId v)
	, maybeToAttr toAttrFrStr "style" (theoryStyle v)
	]
instance XmlContent Imports where
    fromElem (CElem (Elem "imports" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Imports (fromAttrs as) a b), rest))
	   (fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Imports as a b) =
	[CElem (Elem "imports" (toAttrs as) (concatMap toElem a ++
					     maybe [] toElem b))]
instance XmlAttributes Imports_Attrs where
    fromAttrs as =
	Imports_Attrs
	  { importsId = definiteA fromAttrToStr "imports" "id" as
	  , importsStyle = possibleA fromAttrToStr "style" as
	  , importsMid = possibleA fromAttrToStr "mid" as
	  , importsFrom = definiteA fromAttrToStr "imports" "from" as
	  , importsHiding = possibleA fromAttrToStr "hiding" as
	  , importsType = defaultA fromAttrToTyp Imports_type_global "type" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (importsId v)
	, maybeToAttr toAttrFrStr "style" (importsStyle v)
	, maybeToAttr toAttrFrStr "mid" (importsMid v)
	, toAttrFrStr "from" (importsFrom v)
	, maybeToAttr toAttrFrStr "hiding" (importsHiding v)
	, defaultToAttr toAttrFrTyp "type" (importsType v)
	]
instance XmlAttrType Imports_type where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "local" = Just Imports_type_local
	    translate "global" = Just Imports_type_global
	    translate _ = Nothing
    toAttrFrTyp n Imports_type_local = Just (n, str2attr "local")
    toAttrFrTyp n Imports_type_global = Just (n, str2attr "global")
instance XmlContent Morphism where
    fromElem (CElem (Elem "morphism" as c0):rest) =
	(\(a,ca)->
	   (Just (Morphism (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Morphism as a) =
	[CElem (Elem "morphism" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Morphism_Attrs where
    fromAttrs as =
	Morphism_Attrs
	  { morphismId = possibleA fromAttrToStr "id" as
	  , morphismStyle = possibleA fromAttrToStr "style" as
	  , morphismMid = possibleA fromAttrToStr "mid" as
	  , morphismBase = possibleA fromAttrToStr "base" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (morphismId v)
	, maybeToAttr toAttrFrStr "style" (morphismStyle v)
	, maybeToAttr toAttrFrStr "mid" (morphismMid v)
	, maybeToAttr toAttrFrStr "base" (morphismBase v)
	]
instance XmlContent Inclusion where
    fromElem (CElem (Elem "inclusion" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "inclusion" (toAttrs as) [])]
instance XmlAttributes Inclusion where
    fromAttrs as =
	Inclusion
	  { inclusionVia = definiteA fromAttrToStr "inclusion" "via" as
	  , inclusionMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "via" (inclusionVia v)
	, maybeToAttr toAttrFrStr "mid" (inclusionMid v)
	]
-- XmlContent (Maybe Metadata, [Symbol], [CMP], [FMP]) where
instance XmlContent Theory_inclusion where
    fromElem (CElem (Elem "theory-inclusion" as c0):rest) =
	(\(mm, s, c, f, r)->
	   (\(b,cb)->
	      (Just (Theory_inclusion (fromAttrs as)
	        (mm, s, c, f)
		b), rest))
	   (fromElem r))
      	(foldr (\e (mm, s, c, f, r) -> case e of
		CElem (Elem "metadata" eas ec) -> ( ((\(Just p, _)->Just p)(fromElem [e])), s, c, f, r)
		CElem (Elem "symbol" eas ec) -> (mm, ((\(Just p, _)->p)(fromElem [e])):s, c, f, r)
		CElem (Elem "CMP" eas ec) -> (mm, s, ((\(Just p, _)->p)(fromElem [e])):c, f, r)
		CElem (Elem "FMP" eas ec) -> (mm, s, c, ((\(Just p, _)->p)(fromElem [e])):f, r)
		_ -> (mm, s, c, f, e:r)
		) (Nothing, [], [], [], []) c0)
	--(definite fromElem "(metadata?,symbol*,CMP*,FMP*)" "theory-inclusion" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Theory_inclusion as (u,v,w,x) b) =
	[CElem (Elem "theory-inclusion" (toAttrs as) (toElem u ++ toElem v ++ toElem w ++ toElem x ++
						      maybe [] toElem b))]
instance XmlAttributes Theory_inclusion_Attrs where
    fromAttrs as =
	Theory_inclusion_Attrs
	  { theory_inclusionId = definiteA fromAttrToStr "theory-inclusion" "id" as
	  , theory_inclusionStyle = possibleA fromAttrToStr "style" as
	  , theory_inclusionMid = possibleA fromAttrToStr "mid" as
	  , theory_inclusionFrom = definiteA fromAttrToStr "theory-inclusion" "from" as
	  , theory_inclusionTo = definiteA fromAttrToStr "theory-inclusion" "to" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (theory_inclusionId v)
	, maybeToAttr toAttrFrStr "style" (theory_inclusionStyle v)
	, maybeToAttr toAttrFrStr "mid" (theory_inclusionMid v)
	, toAttrFrStr "from" (theory_inclusionFrom v)
	, toAttrFrStr "to" (theory_inclusionTo v)
	]
instance XmlContent Decomposition where
    fromElem (CElem (Elem "decomposition" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "decomposition" (toAttrs as) [])]
instance XmlAttributes Decomposition where
    fromAttrs as =
	Decomposition
	  { decompositionId = definiteA fromAttrToStr "decomposition" "id" as
	  , decompositionStyle = possibleA fromAttrToStr "style" as
	  , decompositionMid = possibleA fromAttrToStr "mid" as
	  , decompositionFor = definiteA fromAttrToStr "decomposition" "for" as
	  , decompositionLinks = definiteA fromAttrToStr "decomposition" "links" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (decompositionId v)
	, maybeToAttr toAttrFrStr "style" (decompositionStyle v)
	, maybeToAttr toAttrFrStr "mid" (decompositionMid v)
	, toAttrFrStr "for" (decompositionFor v)
	, toAttrFrStr "links" (decompositionLinks v)
	]
instance XmlContent Axiom_inclusion where
    fromElem (CElem (Elem "axiom-inclusion" as c0):rest) =
	(\(mm, s, ec, f, r)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (Just (Axiom_inclusion (fromAttrs as) (mm, s, ec, f) b c), rest))
	      (definite fromElem "OneOf" "axiom-inclusion" cb))
	   (fromElem r))
       	(foldr (\e (mm, s, c, f, r) -> case e of
		CElem (Elem "metadata" eas ec) -> ( ((\(Just p, _)->Just p)(fromElem [e])), s, c, f, r)
		CElem (Elem "symbol" eas ec) -> (mm, ((\(Just p, _)->p)(fromElem [e])):s, c, f, r)
		CElem (Elem "CMP" eas ec) -> (mm, s, ((\(Just p, _)->p)(fromElem [e])):c, f, r)
		CElem (Elem "FMP" eas ec) -> (mm, s, c, ((\(Just p, _)->p)(fromElem [e])):f, r)
		_ -> (mm, s, c, f, e:r)
		) (Nothing, [], [], [], []) c0)
--	(definite fromElem "(metadata?,symbol*,CMP*,FMP*)" "axiom-inclusion" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Axiom_inclusion as (mm, s, ec, f) b c) =
	[CElem (Elem "axiom-inclusion" (toAttrs as) (toElem mm ++ toElem s ++ toElem ec ++ toElem f ++
						     maybe [] toElem b ++ toElem c))]
instance XmlAttributes Axiom_inclusion_Attrs where
    fromAttrs as =
	Axiom_inclusion_Attrs
	  { axiom_inclusionId = definiteA fromAttrToStr "axiom-inclusion" "id" as
	  , axiom_inclusionStyle = possibleA fromAttrToStr "style" as
	  , axiom_inclusionMid = possibleA fromAttrToStr "mid" as
	  , axiom_inclusionFrom = definiteA fromAttrToStr "axiom-inclusion" "from" as
	  , axiom_inclusionTo = definiteA fromAttrToStr "axiom-inclusion" "to" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (axiom_inclusionId v)
	, maybeToAttr toAttrFrStr "style" (axiom_inclusionStyle v)
	, maybeToAttr toAttrFrStr "mid" (axiom_inclusionMid v)
	, toAttrFrStr "from" (axiom_inclusionFrom v)
	, toAttrFrStr "to" (axiom_inclusionTo v)
	]
instance XmlContent Path_just where
    fromElem (CElem (Elem "path-just" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "path-just" (toAttrs as) [])]
instance XmlAttributes Path_just where
    fromAttrs as =
	Path_just
	  { path_justLocal = definiteA fromAttrToStr "path-just" "local" as
	  , path_justGlobals = definiteA fromAttrToStr "path-just" "globals" as
	  , path_justMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "local" (path_justLocal v)
	, toAttrFrStr "globals" (path_justGlobals v)
	, maybeToAttr toAttrFrStr "mid" (path_justMid v)
	]
instance XmlContent Obligation where
    fromElem (CElem (Elem "obligation" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "obligation" (toAttrs as) [])]
instance XmlAttributes Obligation where
    fromAttrs as =
	Obligation
	  { obligationInduced_by = definiteA fromAttrToStr "obligation" "induced-by" as
	  , obligationAssertion = definiteA fromAttrToStr "obligation" "assertion" as
	  , obligationMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "induced-by" (obligationInduced_by v)
	, toAttrFrStr "assertion" (obligationAssertion v)
	, maybeToAttr toAttrFrStr "mid" (obligationMid v)
	]
instance XmlContent Exercise where
    fromElem (CElem (Elem "exercise" as c0):rest) =
	(\(mm, s, ec, f, r)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (Just (Exercise (fromAttrs as) (mm, s, ec, f) b c), rest))
	      (definite fromElem "OneOf" "exercise" cb))
	   (fromElem r))
       	(foldr (\e (mm, s, c, f, r) -> case e of
		CElem (Elem "metadata" eas ec) -> ( ((\(Just p, _)->Just p)(fromElem [e])), s, c, f, r)
		CElem (Elem "symbol" eas ec) -> (mm, ((\(Just p, _)->p)(fromElem [e])):s, c, f, r)
		CElem (Elem "CMP" eas ec) -> (mm, s, ((\(Just p, _)->p)(fromElem [e])):c, f, r)
		CElem (Elem "FMP" eas ec) -> (mm, s, c, ((\(Just p, _)->p)(fromElem [e])):f, r)
		_ -> (mm, s, c, f, e:r)
		) (Nothing, [], [], [], []) c0)
--	(definite fromElem "(metadata?,symbol*,CMP*,FMP*)" "exercise" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Exercise as (mm, s, ec, f) b c) =
	[CElem (Elem "exercise" (toAttrs as) (toElem mm ++ toElem s ++ toElem ec ++ toElem f ++ maybe [] toElem b
					      ++ toElem c))]
instance XmlAttributes Exercise_Attrs where
    fromAttrs as =
	Exercise_Attrs
	  { exerciseId = definiteA fromAttrToStr "exercise" "id" as
	  , exerciseStyle = possibleA fromAttrToStr "style" as
	  , exerciseMid = possibleA fromAttrToStr "mid" as
	  , exerciseFor = possibleA fromAttrToStr "for" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (exerciseId v)
	, maybeToAttr toAttrFrStr "style" (exerciseStyle v)
	, maybeToAttr toAttrFrStr "mid" (exerciseMid v)
	, maybeToAttr toAttrFrStr "for" (exerciseFor v)
	]
instance XmlContent Hint where
    fromElem (CElem (Elem "hint" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Hint (fromAttrs as) a b c d), rest))
		 (many fromElem cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Hint as a b c d) =
	[CElem (Elem "hint" (toAttrs as) (maybe [] toElem a ++
					  concatMap toElem b ++ concatMap toElem c ++
					  concatMap toElem d))]
instance XmlAttributes Hint_Attrs where
    fromAttrs as =
	Hint_Attrs
	  { hintId = possibleA fromAttrToStr "id" as
	  , hintStyle = possibleA fromAttrToStr "style" as
	  , hintMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (hintId v)
	, maybeToAttr toAttrFrStr "style" (hintStyle v)
	, maybeToAttr toAttrFrStr "mid" (hintMid v)
	]
instance XmlContent Solution where
    fromElem (CElem (Elem "solution" as c0):rest) =
	(\(mm, s, c, f, r)->
	   (\(b,cb)->
	      (Just (Solution (fromAttrs as) (mm, s, c, f) b), rest))
	   (fromElem r))
       	(foldr (\e (mm, s, c, f, r) -> case e of
		CElem (Elem "metadata" eas ec) -> ( ((\(Just p, _)->Just p)(fromElem [e])), s, c, f, r)
		CElem (Elem "symbol" eas ec) -> (mm, ((\(Just p, _)->p)(fromElem [e])):s, c, f, r)
		CElem (Elem "CMP" eas ec) -> (mm, s, ((\(Just p, _)->p)(fromElem [e])):c, f, r)
		CElem (Elem "FMP" eas ec) -> (mm, s, c, ((\(Just p, _)->p)(fromElem [e])):f, r)
		_ -> (mm, s, c, f, e:r)
		) (Nothing, [], [], [], []) c0)
--	(definite fromElem "(metadata?,symbol*,CMP*,FMP*)" "solution" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Solution as (mm, s ,c , f) b) =
	[CElem (Elem "solution" (toAttrs as) (toElem mm ++ toElem s ++ toElem c ++ toElem f ++
					      maybe [] toElem b))]
instance XmlAttributes Solution_Attrs where
    fromAttrs as =
	Solution_Attrs
	  { solutionFor = possibleA fromAttrToStr "for" as
	  , solutionId = possibleA fromAttrToStr "id" as
	  , solutionStyle = possibleA fromAttrToStr "style" as
	  , solutionMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "for" (solutionFor v)
	, maybeToAttr toAttrFrStr "id" (solutionId v)
	, maybeToAttr toAttrFrStr "style" (solutionStyle v)
	, maybeToAttr toAttrFrStr "mid" (solutionMid v)
	]
instance XmlContent Mc where
    fromElem (CElem (Elem "mc" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Mc (fromAttrs as) a b c d), rest))
		 (definite fromElem "<answer>" "mc" cc))
	      (fromElem cb))
	   (definite fromElem "<choice>" "mc" ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Mc as a b c d) =
	[CElem (Elem "mc" (toAttrs as) (concatMap toElem a ++ toElem b ++
					maybe [] toElem c ++ toElem d))]
instance XmlAttributes Mc_Attrs where
    fromAttrs as =
	Mc_Attrs
	  { mcId = possibleA fromAttrToStr "id" as
	  , mcStyle = possibleA fromAttrToStr "style" as
	  , mcMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (mcId v)
	, maybeToAttr toAttrFrStr "style" (mcStyle v)
	, maybeToAttr toAttrFrStr "mid" (mcMid v)
	]
instance XmlContent Choice where
    fromElem (CElem (Elem "choice" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Choice (fromAttrs as) a b c d), rest))
		 (many fromElem cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Choice as a b c d) =
	[CElem (Elem "choice" (toAttrs as) (maybe [] toElem a ++
					    concatMap toElem b ++ concatMap toElem c ++
					    concatMap toElem d))]
instance XmlAttributes Choice_Attrs where
    fromAttrs as =
	Choice_Attrs
	  { choiceId = possibleA fromAttrToStr "id" as
	  , choiceStyle = possibleA fromAttrToStr "style" as
	  , choiceMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (choiceId v)
	, maybeToAttr toAttrFrStr "style" (choiceStyle v)
	, maybeToAttr toAttrFrStr "mid" (choiceMid v)
	]
instance XmlContent Answer where
    fromElem (CElem (Elem "answer" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (Just (Answer (fromAttrs as) a b c d), rest))
		 (many fromElem cc))
	      (many fromElem cb))
	   (many fromElem ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Answer as a b c d) =
	[CElem (Elem "answer" (toAttrs as) (maybe [] toElem a ++
					    concatMap toElem b ++ concatMap toElem c ++
					    concatMap toElem d))]
instance XmlAttributes Answer_Attrs where
    fromAttrs as =
	Answer_Attrs
	  { answerVerdict = definiteA fromAttrToTyp "answer" "verdict" as
	  , answerId = possibleA fromAttrToStr "id" as
	  , answerStyle = possibleA fromAttrToStr "style" as
	  , answerMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrTyp "verdict" (answerVerdict v)
	, maybeToAttr toAttrFrStr "id" (answerId v)
	, maybeToAttr toAttrFrStr "style" (answerStyle v)
	, maybeToAttr toAttrFrStr "mid" (answerMid v)
	]
instance XmlAttrType Answer_verdict where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "true" = Just Answer_verdict_true
	    translate "false" = Just Answer_verdict_false
	    translate _ = Nothing
    toAttrFrTyp n Answer_verdict_true = Just (n, str2attr "true")
    toAttrFrTyp n Answer_verdict_false = Just (n, str2attr "false")
instance XmlContent Omlet where
    fromElem (CElem (Elem "omlet" as c0):rest) =
	(\(a,ca)->
	   (Just (Omlet (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Omlet as a) =
	[CElem (Elem "omlet" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Omlet_Attrs where
    fromAttrs as =
	Omlet_Attrs
	  { omletId = possibleA fromAttrToStr "id" as
	  , omletStyle = possibleA fromAttrToStr "style" as
	  , omletMid = possibleA fromAttrToStr "mid" as
	  , omletAction = possibleA fromAttrToStr "action" as
	  , omletType = possibleA fromAttrToStr "type" as
	  , omletData = possibleA fromAttrToStr "data" as
	  , omletArgstr = possibleA fromAttrToStr "argstr" as
	  , omletFunction = possibleA fromAttrToStr "function" as
	  , omletWidth = possibleA fromAttrToStr "width" as
	  , omletHeight = possibleA fromAttrToStr "height" as
	  , omletXmlns = defaultA fromAttrToStr "http://www.mathweb.org/omdoc" "xmlns" as
	  , omletXmlns'xsi = defaultA fromAttrToStr "http://www.w3.org/2001/XMLSchema-instance" "xmlns:xsi" as
	  , omletXsi'schemaLocation = defaultA fromAttrToStr "http://www.mathweb.org/omdoc/xsd/omdoc.xsd" "xsi:schemaLocation" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (omletId v)
	, maybeToAttr toAttrFrStr "style" (omletStyle v)
	, maybeToAttr toAttrFrStr "mid" (omletMid v)
	, maybeToAttr toAttrFrStr "action" (omletAction v)
	, maybeToAttr toAttrFrStr "type" (omletType v)
	, maybeToAttr toAttrFrStr "data" (omletData v)
	, maybeToAttr toAttrFrStr "argstr" (omletArgstr v)
	, maybeToAttr toAttrFrStr "function" (omletFunction v)
	, maybeToAttr toAttrFrStr "width" (omletWidth v)
	, maybeToAttr toAttrFrStr "height" (omletHeight v)
	, defaultToAttr toAttrFrStr "xmlns" (omletXmlns v)
	, defaultToAttr toAttrFrStr "xmlns:xsi" (omletXmlns'xsi v)
	, defaultToAttr toAttrFrStr "xsi:schemaLocation" (omletXsi'schemaLocation v)
	]
instance XmlContent Omlet_ where
    fromElem c0 =
	case (fromText c0) of
	(Just a,rest) -> (Just (Omlet_Str a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Omlet_OMOBJ a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (Omlet_Omlet a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (Omlet_With a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (Omlet_Ref a), rest)
					(_,_) ->
						case (fromElem c0) of
						(Just a,rest) -> (Just (Omlet_Ignore a), rest)
						(_,_) ->
						    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Omlet_Str a) = toText a
    toElem (Omlet_OMOBJ a) = toElem a
    toElem (Omlet_Omlet a) = toElem a
    toElem (Omlet_With a) = toElem a
    toElem (Omlet_Ref a) = toElem a
    toElem (Omlet_Ignore a) = toElem a
instance XmlContent Private where
    fromElem (CElem (Elem "private" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Private (fromAttrs as) a b), rest))
	   (definite fromElem "data+" "private" ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Private as a b) =
	[CElem (Elem "private" (toAttrs as) (maybe [] toElem a ++
					     toElem b))]
instance XmlAttributes Private_Attrs where
    fromAttrs as =
	Private_Attrs
	  { privateId = definiteA fromAttrToStr "private" "id" as
	  , privateStyle = possibleA fromAttrToStr "style" as
	  , privateMid = possibleA fromAttrToStr "mid" as
	  , privateFor = possibleA fromAttrToStr "for" as
	  , privateTheory = possibleA fromAttrToStr "theory" as
	  , privatePto = possibleA fromAttrToStr "pto" as
	  , privatePto_version = possibleA fromAttrToStr "pto-version" as
	  , privateType = possibleA fromAttrToStr "type" as
	  , privateRequires = possibleA fromAttrToStr "requires" as
	  , privateReplaces = possibleA fromAttrToStr "replaces" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (privateId v)
	, maybeToAttr toAttrFrStr "style" (privateStyle v)
	, maybeToAttr toAttrFrStr "mid" (privateMid v)
	, maybeToAttr toAttrFrStr "for" (privateFor v)
	, maybeToAttr toAttrFrStr "theory" (privateTheory v)
	, maybeToAttr toAttrFrStr "pto" (privatePto v)
	, maybeToAttr toAttrFrStr "pto-version" (privatePto_version v)
	, maybeToAttr toAttrFrStr "type" (privateType v)
	, maybeToAttr toAttrFrStr "requires" (privateRequires v)
	, maybeToAttr toAttrFrStr "replaces" (privateReplaces v)
	]
instance XmlContent Code where
    fromElem (CElem (Elem "code" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (\(c,cc)->
		 (\(d,cd)->
		    (\(e,ce)->
		       (Just (Code (fromAttrs as) a b c d e), rest))
		    (fromElem cd))
		 (fromElem cc))
	      (fromElem cb))
	   (definite fromElem "data+" "code" ca))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Code as a b c d e) =
	[CElem (Elem "code" (toAttrs as) (maybe [] toElem a ++ toElem b ++
					  maybe [] toElem c ++ maybe [] toElem d ++
					  maybe [] toElem e))]
instance XmlAttributes Code_Attrs where
    fromAttrs as =
	Code_Attrs
	  { codeId = definiteA fromAttrToStr "code" "id" as
	  , codeStyle = possibleA fromAttrToStr "style" as
	  , codeMid = possibleA fromAttrToStr "mid" as
	  , codeFor = possibleA fromAttrToStr "for" as
	  , codeTheory = possibleA fromAttrToStr "theory" as
	  , codePto = possibleA fromAttrToStr "pto" as
	  , codePto_version = possibleA fromAttrToStr "pto-version" as
	  , codeType = possibleA fromAttrToStr "type" as
	  , codeRequires = possibleA fromAttrToStr "requires" as
	  , codeClassid = possibleA fromAttrToStr "classid" as
	  , codeCodebase = possibleA fromAttrToStr "codebase" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "id" (codeId v)
	, maybeToAttr toAttrFrStr "style" (codeStyle v)
	, maybeToAttr toAttrFrStr "mid" (codeMid v)
	, maybeToAttr toAttrFrStr "for" (codeFor v)
	, maybeToAttr toAttrFrStr "theory" (codeTheory v)
	, maybeToAttr toAttrFrStr "pto" (codePto v)
	, maybeToAttr toAttrFrStr "pto-version" (codePto_version v)
	, maybeToAttr toAttrFrStr "type" (codeType v)
	, maybeToAttr toAttrFrStr "requires" (codeRequires v)
	, maybeToAttr toAttrFrStr "classid" (codeClassid v)
	, maybeToAttr toAttrFrStr "codebase" (codeCodebase v)
	]
instance XmlContent Input where
    fromElem (CElem (Elem "input" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Input (fromAttrs as) a b), rest))
	   (many fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Input as a b) =
	[CElem (Elem "input" (toAttrs as) (concatMap toElem a ++
					   concatMap toElem b))]
instance XmlAttributes Input_Attrs where
    fromAttrs as =
	Input_Attrs
	  { inputMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (inputMid v)
	]
instance XmlContent Output where
    fromElem (CElem (Elem "output" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Output (fromAttrs as) a b), rest))
	   (many fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Output as a b) =
	[CElem (Elem "output" (toAttrs as) (concatMap toElem a ++
					    concatMap toElem b))]
instance XmlAttributes Output_Attrs where
    fromAttrs as =
	Output_Attrs
	  { outputMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (outputMid v)
	]
instance XmlContent Effect where
    fromElem (CElem (Elem "effect" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Effect (fromAttrs as) a b), rest))
	   (many fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Effect as a b) =
	[CElem (Elem "effect" (toAttrs as) (concatMap toElem a ++
					    concatMap toElem b))]
instance XmlAttributes Effect_Attrs where
    fromAttrs as =
	Effect_Attrs
	  { effectMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (effectMid v)
	]
instance XmlContent Data where
    fromElem (CElem (Elem "data" as c0):rest) =
	(\(a,ca)->
	   (Just (Data (fromAttrs as) a), rest))
	(definite fromElem "ANY" "data" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Data as a) =
	[CElem (Elem "data" (toAttrs as) (toElem a))]
instance XmlAttributes Data_Attrs where
    fromAttrs as =
	Data_Attrs
	  { dataMid = possibleA fromAttrToStr "mid" as
	  , dataFormat = possibleA fromAttrToStr "format" as
	  , dataHref = possibleA fromAttrToStr "href" as
	  , dataSize = possibleA fromAttrToStr "size" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (dataMid v)
	, maybeToAttr toAttrFrStr "format" (dataFormat v)
	, maybeToAttr toAttrFrStr "href" (dataHref v)
	, maybeToAttr toAttrFrStr "size" (dataSize v)
	]
instance XmlContent Ignore where
    fromElem (CElem (Elem "ignore" as c0):rest) =
	(\(a,ca)->
	   (Just (Ignore (fromAttrs as) a), rest))
	(definite fromElem "ANY" "ignore" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Ignore as a) =
	[CElem (Elem "ignore" (toAttrs as) (toElem a))]
instance XmlAttributes Ignore_Attrs where
    fromAttrs as =
	Ignore_Attrs
	  { ignoreType = possibleA fromAttrToStr "type" as
	  , ignoreComment = possibleA fromAttrToStr "comment" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "type" (ignoreType v)
	, maybeToAttr toAttrFrStr "comment" (ignoreComment v)
	]
instance XmlContent Presentation where
    fromElem (CElem (Elem "presentation" as c0):rest) =
	(\(a,ca)->
	   (Just (Presentation (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Presentation as a) =
	[CElem (Elem "presentation" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Presentation_Attrs where
    fromAttrs as =
	Presentation_Attrs
	  { presentationId = possibleA fromAttrToStr "id" as
	  , presentationStyle = possibleA fromAttrToStr "style" as
	  , presentationMid = possibleA fromAttrToStr "mid" as
	  , presentationXref = possibleA fromAttrToStr "xref" as
	  , presentationFor = definiteA fromAttrToStr "presentation" "for" as
	  , presentationParent = possibleA fromAttrToTyp "parent" as
	  , presentationFixity = defaultA fromAttrToTyp Presentation_fixity_prefix "fixity" as
	  , presentationLbrack = defaultA fromAttrToStr "(" "lbrack" as
	  , presentationRbrack = defaultA fromAttrToStr ")" "rbrack" as
	  , presentationSeparator = defaultA fromAttrToStr "," "separator" as
	  , presentationBracket_style = defaultA fromAttrToTyp Presentation_bracket_style_math "bracket-style" as
	  , presentationPrecedence = defaultA fromAttrToStr "1000" "precedence" as
	  , presentationCrossref_symbol = defaultA fromAttrToTyp Presentation_crossref_symbol_yes "crossref-symbol" as
	  , presentationTheory = possibleA fromAttrToStr "theory" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (presentationId v)
	, maybeToAttr toAttrFrStr "style" (presentationStyle v)
	, maybeToAttr toAttrFrStr "mid" (presentationMid v)
	, maybeToAttr toAttrFrStr "xref" (presentationXref v)
	, toAttrFrStr "for" (presentationFor v)
	, maybeToAttr toAttrFrTyp "parent" (presentationParent v)
	, defaultToAttr toAttrFrTyp "fixity" (presentationFixity v)
	, defaultToAttr toAttrFrStr "lbrack" (presentationLbrack v)
	, defaultToAttr toAttrFrStr "rbrack" (presentationRbrack v)
	, defaultToAttr toAttrFrStr "separator" (presentationSeparator v)
	, defaultToAttr toAttrFrTyp "bracket-style" (presentationBracket_style v)
	, defaultToAttr toAttrFrStr "precedence" (presentationPrecedence v)
	, defaultToAttr toAttrFrTyp "crossref-symbol" (presentationCrossref_symbol v)
	, maybeToAttr toAttrFrStr "theory" (presentationTheory v)
	]
instance XmlContent Presentation_ where
    fromElem c0 =
	case (fromElem c0) of
	(Just a,rest) -> (Just (Presentation_Use a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Presentation_Xslt a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (Presentation_Style a), rest)
			(_,_) ->
			    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Presentation_Use a) = toElem a
    toElem (Presentation_Xslt a) = toElem a
    toElem (Presentation_Style a) = toElem a
instance XmlAttrType Presentation_parent where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "OMA" = Just Presentation_parent_OMA
	    translate "OMBIND" = Just Presentation_parent_OMBIND
	    translate "OMATTR" = Just Presentation_parent_OMATTR
	    translate _ = Nothing
    toAttrFrTyp n Presentation_parent_OMA = Just (n, str2attr "OMA")
    toAttrFrTyp n Presentation_parent_OMBIND = Just (n, str2attr "OMBIND")
    toAttrFrTyp n Presentation_parent_OMATTR = Just (n, str2attr "OMATTR")
instance XmlAttrType Presentation_fixity where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "prefix" = Just Presentation_fixity_prefix
	    translate "infix" = Just Presentation_fixity_infix
	    translate "postfix" = Just Presentation_fixity_postfix
	    translate "assoc" = Just Presentation_fixity_assoc
	    translate _ = Nothing
    toAttrFrTyp n Presentation_fixity_prefix = Just (n, str2attr "prefix")
    toAttrFrTyp n Presentation_fixity_infix = Just (n, str2attr "infix")
    toAttrFrTyp n Presentation_fixity_postfix = Just (n, str2attr "postfix")
    toAttrFrTyp n Presentation_fixity_assoc = Just (n, str2attr "assoc")
instance XmlAttrType Presentation_bracket_style where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "lisp" = Just Presentation_bracket_style_lisp
	    translate "math" = Just Presentation_bracket_style_math
	    translate _ = Nothing
    toAttrFrTyp n Presentation_bracket_style_lisp = Just (n, str2attr "lisp")
    toAttrFrTyp n Presentation_bracket_style_math = Just (n, str2attr "math")
instance XmlAttrType Presentation_crossref_symbol where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "no" = Just Presentation_crossref_symbol_no
	    translate "yes" = Just Presentation_crossref_symbol_yes
	    translate "brackets" = Just Presentation_crossref_symbol_brackets
	    translate "separator" = Just Presentation_crossref_symbol_separator
	    translate "lbrack" = Just Presentation_crossref_symbol_lbrack
	    translate "rbrack" = Just Presentation_crossref_symbol_rbrack
	    translate "all" = Just Presentation_crossref_symbol_all
	    translate _ = Nothing
    toAttrFrTyp n Presentation_crossref_symbol_no = Just (n, str2attr "no")
    toAttrFrTyp n Presentation_crossref_symbol_yes = Just (n, str2attr "yes")
    toAttrFrTyp n Presentation_crossref_symbol_brackets = Just (n, str2attr "brackets")
    toAttrFrTyp n Presentation_crossref_symbol_separator = Just (n, str2attr "separator")
    toAttrFrTyp n Presentation_crossref_symbol_lbrack = Just (n, str2attr "lbrack")
    toAttrFrTyp n Presentation_crossref_symbol_rbrack = Just (n, str2attr "rbrack")
    toAttrFrTyp n Presentation_crossref_symbol_all = Just (n, str2attr "all")
instance XmlContent Use where
    fromElem (CElem (Elem "use" as c0):rest) =
	(\(a,ca)->
	   (Just (Use (fromAttrs as) a), rest))
	(definite fromText "text" "use" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Use as a) =
	[CElem (Elem "use" (toAttrs as) (toText a))]
instance XmlAttributes Use_Attrs where
    fromAttrs as =
	Use_Attrs
	  { useFormat = definiteA fromAttrToStr "use" "format" as
	  , useRequires = possibleA fromAttrToStr "requires" as
	  , useXml'lang = possibleA fromAttrToStr "xml:lang" as
	  , useBracket_style = possibleA fromAttrToTyp "bracket-style" as
	  , useFixity = possibleA fromAttrToTyp "fixity" as
	  , useLbrack = possibleA fromAttrToStr "lbrack" as
	  , useRbrack = possibleA fromAttrToStr "rbrack" as
	  , useLarg_group = possibleA fromAttrToStr "larg-group" as
	  , useRarg_group = possibleA fromAttrToStr "rarg-group" as
	  , useSeparator = possibleA fromAttrToStr "separator" as
	  , useElement = possibleA fromAttrToStr "element" as
	  , useAttributes = possibleA fromAttrToStr "attributes" as
	  , useCrossref_symbol = possibleA fromAttrToTyp "crossref-symbol" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "format" (useFormat v)
	, maybeToAttr toAttrFrStr "requires" (useRequires v)
	, maybeToAttr toAttrFrStr "xml:lang" (useXml'lang v)
	, maybeToAttr toAttrFrTyp "bracket-style" (useBracket_style v)
	, maybeToAttr toAttrFrTyp "fixity" (useFixity v)
	, maybeToAttr toAttrFrStr "lbrack" (useLbrack v)
	, maybeToAttr toAttrFrStr "rbrack" (useRbrack v)
	, maybeToAttr toAttrFrStr "larg-group" (useLarg_group v)
	, maybeToAttr toAttrFrStr "rarg-group" (useRarg_group v)
	, maybeToAttr toAttrFrStr "separator" (useSeparator v)
	, maybeToAttr toAttrFrStr "element" (useElement v)
	, maybeToAttr toAttrFrStr "attributes" (useAttributes v)
	, maybeToAttr toAttrFrTyp "crossref-symbol" (useCrossref_symbol v)
	]
instance XmlAttrType Use_bracket_style where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "lisp" = Just Use_bracket_style_lisp
	    translate "math" = Just Use_bracket_style_math
	    translate _ = Nothing
    toAttrFrTyp n Use_bracket_style_lisp = Just (n, str2attr "lisp")
    toAttrFrTyp n Use_bracket_style_math = Just (n, str2attr "math")
instance XmlAttrType Use_fixity where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "prefix" = Just Use_fixity_prefix
	    translate "infix" = Just Use_fixity_infix
	    translate "postfix" = Just Use_fixity_postfix
	    translate "assoc" = Just Use_fixity_assoc
	    translate _ = Nothing
    toAttrFrTyp n Use_fixity_prefix = Just (n, str2attr "prefix")
    toAttrFrTyp n Use_fixity_infix = Just (n, str2attr "infix")
    toAttrFrTyp n Use_fixity_postfix = Just (n, str2attr "postfix")
    toAttrFrTyp n Use_fixity_assoc = Just (n, str2attr "assoc")
instance XmlAttrType Use_crossref_symbol where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "no" = Just Use_crossref_symbol_no
	    translate "yes" = Just Use_crossref_symbol_yes
	    translate "brackets" = Just Use_crossref_symbol_brackets
	    translate "separator" = Just Use_crossref_symbol_separator
	    translate "lbrack" = Just Use_crossref_symbol_lbrack
	    translate "rbrack" = Just Use_crossref_symbol_rbrack
	    translate "all" = Just Use_crossref_symbol_all
	    translate _ = Nothing
    toAttrFrTyp n Use_crossref_symbol_no = Just (n, str2attr "no")
    toAttrFrTyp n Use_crossref_symbol_yes = Just (n, str2attr "yes")
    toAttrFrTyp n Use_crossref_symbol_brackets = Just (n, str2attr "brackets")
    toAttrFrTyp n Use_crossref_symbol_separator = Just (n, str2attr "separator")
    toAttrFrTyp n Use_crossref_symbol_lbrack = Just (n, str2attr "lbrack")
    toAttrFrTyp n Use_crossref_symbol_rbrack = Just (n, str2attr "rbrack")
    toAttrFrTyp n Use_crossref_symbol_all = Just (n, str2attr "all")
instance XmlContent Omstyle where
    fromElem (CElem (Elem "omstyle" as c0):rest) =
	(\(a,ca)->
	   (Just (Omstyle (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Omstyle as a) =
	[CElem (Elem "omstyle" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Omstyle_Attrs where
    fromAttrs as =
	Omstyle_Attrs
	  { omstyleId = possibleA fromAttrToStr "id" as
	  , omstyleStyle = possibleA fromAttrToStr "style" as
	  , omstyleMid = possibleA fromAttrToStr "mid" as
	  , omstyleXref = possibleA fromAttrToStr "xref" as
	  , omstyleFor = possibleA fromAttrToStr "for" as
	  , omstyleElement = definiteA fromAttrToStr "omstyle" "element" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (omstyleId v)
	, maybeToAttr toAttrFrStr "style" (omstyleStyle v)
	, maybeToAttr toAttrFrStr "mid" (omstyleMid v)
	, maybeToAttr toAttrFrStr "xref" (omstyleXref v)
	, maybeToAttr toAttrFrStr "for" (omstyleFor v)
	, toAttrFrStr "element" (omstyleElement v)
	]
instance XmlContent Omstyle_ where
    fromElem c0 =
	case (fromElem c0) of
	(Just a,rest) -> (Just (Omstyle_Xslt a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Omstyle_Style a), rest)
		(_,_) ->
		    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Omstyle_Xslt a) = toElem a
    toElem (Omstyle_Style a) = toElem a
instance XmlContent Xslt where
    fromElem (CElem (Elem "xslt" as c0):rest) =
	(\(a,ca)->
	   (Just (Xslt (fromAttrs as) a), rest))
	(definite fromText "text" "xslt" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Xslt as a) =
	[CElem (Elem "xslt" (toAttrs as) (toText a))]
instance XmlAttributes Xslt_Attrs where
    fromAttrs as =
	Xslt_Attrs
	  { xsltFormat = definiteA fromAttrToStr "xslt" "format" as
	  , xsltRequires = possibleA fromAttrToStr "requires" as
	  , xsltXml'lang = possibleA fromAttrToStr "xml:lang" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "format" (xsltFormat v)
	, maybeToAttr toAttrFrStr "requires" (xsltRequires v)
	, maybeToAttr toAttrFrStr "xml:lang" (xsltXml'lang v)
	]
instance XmlContent Style where
    fromElem (CElem (Elem "style" as c0):rest) =
	(\(a,ca)->
	   (Just (Style (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Style as a) =
	[CElem (Elem "style" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Style_Attrs where
    fromAttrs as =
	Style_Attrs
	  { styleFormat = definiteA fromAttrToStr "style" "format" as
	  , styleRequires = possibleA fromAttrToStr "requires" as
	  , styleXml'lang = possibleA fromAttrToStr "xml:lang" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "format" (styleFormat v)
	, maybeToAttr toAttrFrStr "requires" (styleRequires v)
	, maybeToAttr toAttrFrStr "xml:lang" (styleXml'lang v)
	]
instance XmlContent Style_ where
    fromElem c0 =
	case (fromElem c0) of
	(Just a,rest) -> (Just (Style_Element a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Style_Text a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (Style_Recurse a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (Style_Value_of a), rest)
				(_,_) ->
				    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Style_Element a) = toElem a
    toElem (Style_Text a) = toElem a
    toElem (Style_Recurse a) = toElem a
    toElem (Style_Value_of a) = toElem a
instance XmlContent Omdoc.Element where
    fromElem (CElem (Elem "element" as c0):rest) =
	(\(a,ca)->
	   (Just (Element (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Element as a) =
	[CElem (Elem "element" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Element_Attrs where
    fromAttrs as =
	Element_Attrs
	  { elementName = definiteA fromAttrToStr "element" "name" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "name" (elementName v)
	]
instance XmlContent Element_ where
    fromElem c0 =
	case (fromElem c0) of
	(Just a,rest) -> (Just (Element_Attribute a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Element_Element a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (Element_Text a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (Element_Recurse a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (Element_Value_of a), rest)
					(_,_) ->
					    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Element_Attribute a) = toElem a
    toElem (Element_Element a) = toElem a
    toElem (Element_Text a) = toElem a
    toElem (Element_Recurse a) = toElem a
    toElem (Element_Value_of a) = toElem a
instance XmlContent Attribute where
    fromElem (CElem (Elem "attribute" as c0):rest) =
	(\(a,ca)->
	   (Just (Attribute (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Attribute as a) =
	[CElem (Elem "attribute" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Attribute_Attrs where
    fromAttrs as =
	Attribute_Attrs
	  { attributeName = definiteA fromAttrToStr "attribute" "name" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "name" (attributeName v)
	]
instance XmlContent Attribute_ where
    fromElem c0 =
	case (fromText c0) of
	(Just a,rest) -> (Just (Attribute_Str a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Attribute_Value_of a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (Attribute_Text a), rest)
			(_,_) ->
			    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Attribute_Str a) = toText a
    toElem (Attribute_Value_of a) = toElem a
    toElem (Attribute_Text a) = toElem a
instance XmlContent Text where
    fromElem (CElem (Elem "text" [] c0):rest) =
	(\(a,ca)->
	   (Just (Text a), rest))
	(definite fromText "text" "text" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Text a) =
	[CElem (Elem "text" [] (toText a))]
instance XmlContent Value_of where
    fromElem (CElem (Elem "value-of" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "value-of" (toAttrs as) [])]
instance XmlAttributes Value_of where
    fromAttrs as =
	Value_of
	  { value_ofSelect = definiteA fromAttrToStr "value-of" "select" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "select" (value_ofSelect v)
	]
instance XmlContent Recurse where
    fromElem (CElem (Elem "recurse" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "recurse" (toAttrs as) [])]
instance XmlAttributes Recurse where
    fromAttrs as =
	Recurse
	  { recurseSelect = possibleA fromAttrToStr "select" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "select" (recurseSelect v)
	]
instance XmlContent OMS where
    fromElem (CElem (Elem "OMS" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "OMS" (toAttrs as) [])]
instance XmlAttributes OMS where
    fromAttrs as =
	OMS
	  { oMSName = definiteA fromAttrToStr "OMS" "name" as
	  , oMSCd = definiteA fromAttrToStr "OMS" "cd" as
	  , oMSStyle = possibleA fromAttrToStr "style" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "name" (oMSName v)
	, toAttrFrStr "cd" (oMSCd v)
	, maybeToAttr toAttrFrStr "style" (oMSStyle v)
	]
instance XmlContent OMV where
    fromElem (CElem (Elem "OMV" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "OMV" (toAttrs as) [])]
instance XmlAttributes OMV where
    fromAttrs as =
	OMV
	  { oMVName = definiteA fromAttrToStr "OMV" "name" as
	  , oMVStyle = possibleA fromAttrToStr "style" as
	  }
    toAttrs v = catMaybes 
	[ toAttrFrStr "name" (oMVName v)
	, maybeToAttr toAttrFrStr "style" (oMVStyle v)
	]
instance XmlContent OMI where
    fromElem (CElem (Elem "OMI" as c0):rest) =
	(\(a,ca)->
	   (Just (OMI (fromAttrs as) a), rest))
	(definite fromText "text" "OMI" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMI as a) =
	[CElem (Elem "OMI" (toAttrs as) (toText a))]
instance XmlAttributes OMI_Attrs where
    fromAttrs as =
	OMI_Attrs
	  { oMIMid = possibleA fromAttrToStr "mid" as
	  , oMIStyle = possibleA fromAttrToStr "style" as
	  , oMIId = possibleA fromAttrToStr "id" as
	  , oMIXref = possibleA fromAttrToStr "xref" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (oMIMid v)
	, maybeToAttr toAttrFrStr "style" (oMIStyle v)
	, maybeToAttr toAttrFrStr "id" (oMIId v)
	, maybeToAttr toAttrFrStr "xref" (oMIXref v)
	]
instance XmlContent OMB where
    fromElem (CElem (Elem "OMB" as c0):rest) =
	(\(a,ca)->
	   (Just (OMB (fromAttrs as) a), rest))
	(definite fromText "text" "OMB" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMB as a) =
	[CElem (Elem "OMB" (toAttrs as) (toText a))]
instance XmlAttributes OMB_Attrs where
    fromAttrs as =
	OMB_Attrs
	  { oMBMid = possibleA fromAttrToStr "mid" as
	  , oMBStyle = possibleA fromAttrToStr "style" as
	  , oMBId = possibleA fromAttrToStr "id" as
	  , oMBXref = possibleA fromAttrToStr "xref" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (oMBMid v)
	, maybeToAttr toAttrFrStr "style" (oMBStyle v)
	, maybeToAttr toAttrFrStr "id" (oMBId v)
	, maybeToAttr toAttrFrStr "xref" (oMBXref v)
	]
instance XmlContent OMSTR where
    fromElem (CElem (Elem "OMSTR" as c0):rest) =
	(\(a,ca)->
	   (Just (OMSTR (fromAttrs as) a), rest))
	(definite fromText "text" "OMSTR" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMSTR as a) =
	[CElem (Elem "OMSTR" (toAttrs as) (toText a))]
instance XmlAttributes OMSTR_Attrs where
    fromAttrs as =
	OMSTR_Attrs
	  { oMSTRMid = possibleA fromAttrToStr "mid" as
	  , oMSTRStyle = possibleA fromAttrToStr "style" as
	  , oMSTRId = possibleA fromAttrToStr "id" as
	  , oMSTRXref = possibleA fromAttrToStr "xref" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (oMSTRMid v)
	, maybeToAttr toAttrFrStr "style" (oMSTRStyle v)
	, maybeToAttr toAttrFrStr "id" (oMSTRId v)
	, maybeToAttr toAttrFrStr "xref" (oMSTRXref v)
	]
instance XmlContent OMF where
    fromElem (CElem (Elem "OMF" as []):rest) =
	(Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
	[CElem (Elem "OMF" (toAttrs as) [])]
instance XmlAttributes OMF where
    fromAttrs as =
	OMF
	  { oMFDec = possibleA fromAttrToStr "dec" as
	  , oMFHex = possibleA fromAttrToStr "hex" as
	  , oMFMid = possibleA fromAttrToStr "mid" as
	  , oMFStyle = possibleA fromAttrToStr "style" as
	  , oMFId = possibleA fromAttrToStr "id" as
	  , oMFXref = possibleA fromAttrToStr "xref" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "dec" (oMFDec v)
	, maybeToAttr toAttrFrStr "hex" (oMFHex v)
	, maybeToAttr toAttrFrStr "mid" (oMFMid v)
	, maybeToAttr toAttrFrStr "style" (oMFStyle v)
	, maybeToAttr toAttrFrStr "id" (oMFId v)
	, maybeToAttr toAttrFrStr "xref" (oMFXref v)
	]
instance XmlContent OMA where
    fromElem (CElem (Elem "OMA" as c0):rest) =
	(\(a,ca)->
	   (Just (OMA (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMA as a) =
	[CElem (Elem "OMA" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes OMA_Attrs where
    fromAttrs as =
	OMA_Attrs
	  { oMAMid = possibleA fromAttrToStr "mid" as
	  , oMAStyle = possibleA fromAttrToStr "style" as
	  , oMAId = possibleA fromAttrToStr "id" as
	  , oMAXref = possibleA fromAttrToStr "xref" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (oMAMid v)
	, maybeToAttr toAttrFrStr "style" (oMAStyle v)
	, maybeToAttr toAttrFrStr "id" (oMAId v)
	, maybeToAttr toAttrFrStr "xref" (oMAXref v)
	]
instance XmlContent OMA_ where
    fromElem c0 =
	case (fromElem c0) of
	(Just a,rest) -> (Just (OMA_OMS a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (OMA_OMV a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (OMA_OMI a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (OMA_OMB a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (OMA_OMSTR a), rest)
					(_,_) ->
						case (fromElem c0) of
						(Just a,rest) -> (Just (OMA_OMF a), rest)
						(_,_) ->
							case (fromElem c0) of
							(Just a,rest) -> (Just (OMA_OMA a), rest)
							(_,_) ->
								case (fromElem c0) of
								(Just a,rest) -> (Just (OMA_OMBIND a), rest)
								(_,_) ->
									case (fromElem c0) of
									(Just a,rest) -> (Just (OMA_OME a), rest)
									(_,_) ->
										case (fromElem c0) of
										(Just a,rest) -> (Just (OMA_OMATTR a), rest)
										(_,_) ->
										    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMA_OMS a) = toElem a
    toElem (OMA_OMV a) = toElem a
    toElem (OMA_OMI a) = toElem a
    toElem (OMA_OMB a) = toElem a
    toElem (OMA_OMSTR a) = toElem a
    toElem (OMA_OMF a) = toElem a
    toElem (OMA_OMA a) = toElem a
    toElem (OMA_OMBIND a) = toElem a
    toElem (OMA_OME a) = toElem a
    toElem (OMA_OMATTR a) = toElem a
instance XmlContent OMBIND where
    fromElem (CElem (Elem "OMBIND" as c0):rest) =
	(\(a,ca)->
	   (Just (OMBIND (fromAttrs as) a), rest))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMBIND as a) =
	[CElem (Elem "OMBIND" (toAttrs as) (maybe [] toElem a))]
instance XmlAttributes OMBIND_Attrs where
    fromAttrs as =
	OMBIND_Attrs
	  { oMBINDMid = possibleA fromAttrToStr "mid" as
	  , oMBINDStyle = possibleA fromAttrToStr "style" as
	  , oMBINDId = possibleA fromAttrToStr "id" as
	  , oMBINDXref = possibleA fromAttrToStr "xref" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (oMBINDMid v)
	, maybeToAttr toAttrFrStr "style" (oMBINDStyle v)
	, maybeToAttr toAttrFrStr "id" (oMBINDId v)
	, maybeToAttr toAttrFrStr "xref" (oMBINDXref v)
	]
instance XmlContent OMBIND_ where
    fromElem c0 =
	case (\(a,ca)->
		(\(b,cb)->
		   (\(c,cc)->
		      (a,b,c,cc))
		   (fromElem cb))
		(fromElem ca))
	     (fromElem c0) of
	(Just a,Just b,Just c,rest) -> (Just (OMBIND_ a b c), rest)
	(_,_,_,_) ->
	    (Nothing, c0)
    toElem (OMBIND_ a b c) =
	(toElem a ++ toElem b ++ toElem c)
instance XmlContent OMBVAR where
    fromElem (CElem (Elem "OMBVAR" [] c0):rest) =
	(\(a,ca)->
	   (Just (OMBVAR a), rest))
	(definite fromElem "OMBVAR+" "OMBVAR" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMBVAR a) =
	[CElem (Elem "OMBVAR" [] (toElem a))]
instance XmlContent OMBVAR_ where
    fromElem c0 =
	case (fromElem c0) of
	(Just a,rest) -> (Just (OMBVAR_OMV a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (OMBVAR_OMATTR a), rest)
		(_,_) ->
		    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMBVAR_OMV a) = toElem a
    toElem (OMBVAR_OMATTR a) = toElem a
instance XmlContent OME where
    fromElem (CElem (Elem "OME" [] c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (OME a b), rest))
	   (many fromElem ca))
	(definite fromElem "<OMS>" "OME" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OME a b) =
	[CElem (Elem "OME" [] (toElem a ++ concatMap toElem b))]
instance XmlContent OMATTR where
    fromElem (CElem (Elem "OMATTR" as c0):rest) =
	(\(a,ca)->
	   (Just (OMATTR (fromAttrs as) a), rest))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMATTR as a) =
	[CElem (Elem "OMATTR" (toAttrs as) (maybe [] toElem a))]
instance XmlAttributes OMATTR_Attrs where
    fromAttrs as =
	OMATTR_Attrs
	  { oMATTRMid = possibleA fromAttrToStr "mid" as
	  , oMATTRStyle = possibleA fromAttrToStr "style" as
	  , oMATTRId = possibleA fromAttrToStr "id" as
	  , oMATTRXref = possibleA fromAttrToStr "xref" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "mid" (oMATTRMid v)
	, maybeToAttr toAttrFrStr "style" (oMATTRStyle v)
	, maybeToAttr toAttrFrStr "id" (oMATTRId v)
	, maybeToAttr toAttrFrStr "xref" (oMATTRXref v)
	]
instance XmlContent OMATTR_ where
    fromElem c0 =
	case (\(a,ca)->
		(\(b,cb)->
		   (a,b,cb))
		(fromElem ca))
	     (fromElem c0) of
	(Just a,Just b,rest) -> (Just (OMATTR_ a b), rest)
	(_,_,_) ->
	    (Nothing, c0)
    toElem (OMATTR_ a b) =
	(toElem a ++ toElem b)
instance XmlContent OMATP where
    fromElem (CElem (Elem "OMATP" [] c0):rest) =
	(\(a,ca)->
	   (Just (OMATP a), rest))
	(definite fromElem "OMATP+" "OMATP" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMATP a) =
	[CElem (Elem "OMATP" [] (toElem a))]
instance XmlContent OMATP_ where
    fromElem c0 =
	case (\(a,ca)->
		(\(b,cb)->
		   (a,b,cb))
		(fromElem ca))
	     (fromElem c0) of
	(Just a,Just b,rest) -> (Just (OMATP_ a b), rest)
	(_,_,_) ->
	    (Nothing, c0)
    toElem (OMATP_ a b) =
	(toElem a ++ toElem b)
instance XmlContent OMOBJ where
    fromElem (CElem (Elem "OMOBJ" as c0):rest) =
	(\(a,ca)->
	   (Just (OMOBJ (fromAttrs as) a), rest))
	(fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMOBJ as a) =
	[CElem (Elem "OMOBJ" (toAttrs as) (maybe [] toElem a))]
instance XmlAttributes OMOBJ_Attrs where
    fromAttrs as =
	OMOBJ_Attrs
	  { oMOBJXmlns = defaultA fromAttrToStr "http://www.openmath.org/OpenMath" "xmlns" as
	  , oMOBJMid = possibleA fromAttrToStr "mid" as
	  , oMOBJStyle = possibleA fromAttrToStr "style" as
	  , oMOBJId = possibleA fromAttrToStr "id" as
	  , oMOBJXref = possibleA fromAttrToStr "xref" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (oMOBJXmlns v)
	, maybeToAttr toAttrFrStr "mid" (oMOBJMid v)
	, maybeToAttr toAttrFrStr "style" (oMOBJStyle v)
	, maybeToAttr toAttrFrStr "id" (oMOBJId v)
	, maybeToAttr toAttrFrStr "xref" (oMOBJXref v)
	]
instance XmlContent OMOBJ_ where
    fromElem c0 =
	case (fromElem c0) of
	(Just a,rest) -> (Just (OMOBJ_OMS a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (OMOBJ_OMV a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (OMOBJ_OMI a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (OMOBJ_OMB a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (OMOBJ_OMSTR a), rest)
					(_,_) ->
						case (fromElem c0) of
						(Just a,rest) -> (Just (OMOBJ_OMF a), rest)
						(_,_) ->
							case (fromElem c0) of
							(Just a,rest) -> (Just (OMOBJ_OMA a), rest)
							(_,_) ->
								case (fromElem c0) of
								(Just a,rest) -> (Just (OMOBJ_OMBIND a), rest)
								(_,_) ->
									case (fromElem c0) of
									(Just a,rest) -> (Just (OMOBJ_OME a), rest)
									(_,_) ->
										case (fromElem c0) of
										(Just a,rest) -> (Just (OMOBJ_OMATTR a), rest)
										(_,_) ->
										    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (OMOBJ_OMS a) = toElem a
    toElem (OMOBJ_OMV a) = toElem a
    toElem (OMOBJ_OMI a) = toElem a
    toElem (OMOBJ_OMB a) = toElem a
    toElem (OMOBJ_OMSTR a) = toElem a
    toElem (OMOBJ_OMF a) = toElem a
    toElem (OMOBJ_OMA a) = toElem a
    toElem (OMOBJ_OMBIND a) = toElem a
    toElem (OMOBJ_OME a) = toElem a
    toElem (OMOBJ_OMATTR a) = toElem a
instance XmlContent Metadata where
    fromElem (CElem (Elem "metadata" as c0):rest) =
	(\(a,ca)->
	   (\(b,cb)->
	      (Just (Metadata (fromAttrs as) a b), rest))
	   (fromElem ca))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Metadata as a b) =
	[CElem (Elem "metadata" (toAttrs as) (concatMap toElem a ++
					      maybe [] toElem b))]
instance XmlAttributes Metadata_Attrs where
    fromAttrs as =
	Metadata_Attrs
	  { metadataId = possibleA fromAttrToStr "id" as
	  , metadataStyle = possibleA fromAttrToStr "style" as
	  , metadataMid = possibleA fromAttrToStr "mid" as
	  , metadataInherits = possibleA fromAttrToStr "inherits" as
	  }
    toAttrs v = catMaybes 
	[ maybeToAttr toAttrFrStr "id" (metadataId v)
	, maybeToAttr toAttrFrStr "style" (metadataStyle v)
	, maybeToAttr toAttrFrStr "mid" (metadataMid v)
	, maybeToAttr toAttrFrStr "inherits" (metadataInherits v)
	]
instance XmlContent Contributor where
    fromElem (CElem (Elem "Contributor" as c0):rest) =
	(\(a,ca)->
	   (Just (Contributor (fromAttrs as) a), rest))
	(definite fromText "text" "Contributor" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Contributor as a) =
	[CElem (Elem "Contributor" (toAttrs as) (toText a))]
instance XmlAttributes Contributor_Attrs where
    fromAttrs as =
	Contributor_Attrs
	  { contributorXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  , contributorId = possibleA fromAttrToStr "id" as
	  , contributorStyle = possibleA fromAttrToStr "style" as
	  , contributorMid = possibleA fromAttrToStr "mid" as
	  , contributorXml'lang = defaultA fromAttrToTyp Contributor_xml'lang_en "xml:lang" as
	  , contributorRole = defaultA fromAttrToTyp Contributor_role_aut "role" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (contributorXmlns v)
	, maybeToAttr toAttrFrStr "id" (contributorId v)
	, maybeToAttr toAttrFrStr "style" (contributorStyle v)
	, maybeToAttr toAttrFrStr "mid" (contributorMid v)
	, defaultToAttr toAttrFrTyp "xml:lang" (contributorXml'lang v)
	, defaultToAttr toAttrFrTyp "role" (contributorRole v)
	]
instance XmlAttrType Contributor_xml'lang where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "aa" = Just Contributor_xml'lang_aa
	    translate "ab" = Just Contributor_xml'lang_ab
	    translate "af" = Just Contributor_xml'lang_af
	    translate "am" = Just Contributor_xml'lang_am
	    translate "ar" = Just Contributor_xml'lang_ar
	    translate "as" = Just Contributor_xml'lang_as
	    translate "ay" = Just Contributor_xml'lang_ay
	    translate "az" = Just Contributor_xml'lang_az
	    translate "ba" = Just Contributor_xml'lang_ba
	    translate "be" = Just Contributor_xml'lang_be
	    translate "bg" = Just Contributor_xml'lang_bg
	    translate "bh" = Just Contributor_xml'lang_bh
	    translate "bi" = Just Contributor_xml'lang_bi
	    translate "bn" = Just Contributor_xml'lang_bn
	    translate "bo" = Just Contributor_xml'lang_bo
	    translate "br" = Just Contributor_xml'lang_br
	    translate "ca" = Just Contributor_xml'lang_ca
	    translate "co" = Just Contributor_xml'lang_co
	    translate "cs" = Just Contributor_xml'lang_cs
	    translate "cy" = Just Contributor_xml'lang_cy
	    translate "da" = Just Contributor_xml'lang_da
	    translate "de" = Just Contributor_xml'lang_de
	    translate "dz" = Just Contributor_xml'lang_dz
	    translate "el" = Just Contributor_xml'lang_el
	    translate "en" = Just Contributor_xml'lang_en
	    translate "eo" = Just Contributor_xml'lang_eo
	    translate "es" = Just Contributor_xml'lang_es
	    translate "et" = Just Contributor_xml'lang_et
	    translate "eu" = Just Contributor_xml'lang_eu
	    translate "fa" = Just Contributor_xml'lang_fa
	    translate "fi" = Just Contributor_xml'lang_fi
	    translate "fj" = Just Contributor_xml'lang_fj
	    translate "fo" = Just Contributor_xml'lang_fo
	    translate "fr" = Just Contributor_xml'lang_fr
	    translate "fy" = Just Contributor_xml'lang_fy
	    translate "ga" = Just Contributor_xml'lang_ga
	    translate "gd" = Just Contributor_xml'lang_gd
	    translate "gl" = Just Contributor_xml'lang_gl
	    translate "gn" = Just Contributor_xml'lang_gn
	    translate "gu" = Just Contributor_xml'lang_gu
	    translate "ha" = Just Contributor_xml'lang_ha
	    translate "he" = Just Contributor_xml'lang_he
	    translate "hi" = Just Contributor_xml'lang_hi
	    translate "hr" = Just Contributor_xml'lang_hr
	    translate "hu" = Just Contributor_xml'lang_hu
	    translate "hy" = Just Contributor_xml'lang_hy
	    translate "ia" = Just Contributor_xml'lang_ia
	    translate "ie" = Just Contributor_xml'lang_ie
	    translate "ik" = Just Contributor_xml'lang_ik
	    translate "id" = Just Contributor_xml'lang_id
	    translate "is" = Just Contributor_xml'lang_is
	    translate "it" = Just Contributor_xml'lang_it
	    translate "iu" = Just Contributor_xml'lang_iu
	    translate "ja" = Just Contributor_xml'lang_ja
	    translate "jv" = Just Contributor_xml'lang_jv
	    translate "ka" = Just Contributor_xml'lang_ka
	    translate "kk" = Just Contributor_xml'lang_kk
	    translate "kl" = Just Contributor_xml'lang_kl
	    translate "km" = Just Contributor_xml'lang_km
	    translate "kn" = Just Contributor_xml'lang_kn
	    translate "ko" = Just Contributor_xml'lang_ko
	    translate "ks" = Just Contributor_xml'lang_ks
	    translate "ku" = Just Contributor_xml'lang_ku
	    translate "ky" = Just Contributor_xml'lang_ky
	    translate "la" = Just Contributor_xml'lang_la
	    translate "ln" = Just Contributor_xml'lang_ln
	    translate "lo" = Just Contributor_xml'lang_lo
	    translate "lt" = Just Contributor_xml'lang_lt
	    translate "lv" = Just Contributor_xml'lang_lv
	    translate "mg" = Just Contributor_xml'lang_mg
	    translate "mi" = Just Contributor_xml'lang_mi
	    translate "mk" = Just Contributor_xml'lang_mk
	    translate "ml" = Just Contributor_xml'lang_ml
	    translate "mn" = Just Contributor_xml'lang_mn
	    translate "mo" = Just Contributor_xml'lang_mo
	    translate "mr" = Just Contributor_xml'lang_mr
	    translate "ms" = Just Contributor_xml'lang_ms
	    translate "mt" = Just Contributor_xml'lang_mt
	    translate "my" = Just Contributor_xml'lang_my
	    translate "na" = Just Contributor_xml'lang_na
	    translate "ne" = Just Contributor_xml'lang_ne
	    translate "nl" = Just Contributor_xml'lang_nl
	    translate "no" = Just Contributor_xml'lang_no
	    translate "oc" = Just Contributor_xml'lang_oc
	    translate "om" = Just Contributor_xml'lang_om
	    translate "or" = Just Contributor_xml'lang_or
	    translate "pa" = Just Contributor_xml'lang_pa
	    translate "pl" = Just Contributor_xml'lang_pl
	    translate "ps" = Just Contributor_xml'lang_ps
	    translate "pt" = Just Contributor_xml'lang_pt
	    translate "qu" = Just Contributor_xml'lang_qu
	    translate "rm" = Just Contributor_xml'lang_rm
	    translate "rn" = Just Contributor_xml'lang_rn
	    translate "ro" = Just Contributor_xml'lang_ro
	    translate "ru" = Just Contributor_xml'lang_ru
	    translate "rw" = Just Contributor_xml'lang_rw
	    translate "sa" = Just Contributor_xml'lang_sa
	    translate "sd" = Just Contributor_xml'lang_sd
	    translate "sg" = Just Contributor_xml'lang_sg
	    translate "sh" = Just Contributor_xml'lang_sh
	    translate "si" = Just Contributor_xml'lang_si
	    translate "sk" = Just Contributor_xml'lang_sk
	    translate "sl" = Just Contributor_xml'lang_sl
	    translate "sm" = Just Contributor_xml'lang_sm
	    translate "sn" = Just Contributor_xml'lang_sn
	    translate "so" = Just Contributor_xml'lang_so
	    translate "sq" = Just Contributor_xml'lang_sq
	    translate "sr" = Just Contributor_xml'lang_sr
	    translate "ss" = Just Contributor_xml'lang_ss
	    translate "st" = Just Contributor_xml'lang_st
	    translate "su" = Just Contributor_xml'lang_su
	    translate "sv" = Just Contributor_xml'lang_sv
	    translate "sw" = Just Contributor_xml'lang_sw
	    translate "ta" = Just Contributor_xml'lang_ta
	    translate "te" = Just Contributor_xml'lang_te
	    translate "tg" = Just Contributor_xml'lang_tg
	    translate "th" = Just Contributor_xml'lang_th
	    translate "ti" = Just Contributor_xml'lang_ti
	    translate "tk" = Just Contributor_xml'lang_tk
	    translate "tl" = Just Contributor_xml'lang_tl
	    translate "tn" = Just Contributor_xml'lang_tn
	    translate "to" = Just Contributor_xml'lang_to
	    translate "tr" = Just Contributor_xml'lang_tr
	    translate "ts" = Just Contributor_xml'lang_ts
	    translate "tt" = Just Contributor_xml'lang_tt
	    translate "tw" = Just Contributor_xml'lang_tw
	    translate "ug" = Just Contributor_xml'lang_ug
	    translate "uk" = Just Contributor_xml'lang_uk
	    translate "ur" = Just Contributor_xml'lang_ur
	    translate "uz" = Just Contributor_xml'lang_uz
	    translate "vi" = Just Contributor_xml'lang_vi
	    translate "vo" = Just Contributor_xml'lang_vo
	    translate "wo" = Just Contributor_xml'lang_wo
	    translate "xh" = Just Contributor_xml'lang_xh
	    translate "yi" = Just Contributor_xml'lang_yi
	    translate "yo" = Just Contributor_xml'lang_yo
	    translate "za" = Just Contributor_xml'lang_za
	    translate "zh" = Just Contributor_xml'lang_zh
	    translate "zu" = Just Contributor_xml'lang_zu
	    translate _ = Nothing
    toAttrFrTyp n Contributor_xml'lang_aa = Just (n, str2attr "aa")
    toAttrFrTyp n Contributor_xml'lang_ab = Just (n, str2attr "ab")
    toAttrFrTyp n Contributor_xml'lang_af = Just (n, str2attr "af")
    toAttrFrTyp n Contributor_xml'lang_am = Just (n, str2attr "am")
    toAttrFrTyp n Contributor_xml'lang_ar = Just (n, str2attr "ar")
    toAttrFrTyp n Contributor_xml'lang_as = Just (n, str2attr "as")
    toAttrFrTyp n Contributor_xml'lang_ay = Just (n, str2attr "ay")
    toAttrFrTyp n Contributor_xml'lang_az = Just (n, str2attr "az")
    toAttrFrTyp n Contributor_xml'lang_ba = Just (n, str2attr "ba")
    toAttrFrTyp n Contributor_xml'lang_be = Just (n, str2attr "be")
    toAttrFrTyp n Contributor_xml'lang_bg = Just (n, str2attr "bg")
    toAttrFrTyp n Contributor_xml'lang_bh = Just (n, str2attr "bh")
    toAttrFrTyp n Contributor_xml'lang_bi = Just (n, str2attr "bi")
    toAttrFrTyp n Contributor_xml'lang_bn = Just (n, str2attr "bn")
    toAttrFrTyp n Contributor_xml'lang_bo = Just (n, str2attr "bo")
    toAttrFrTyp n Contributor_xml'lang_br = Just (n, str2attr "br")
    toAttrFrTyp n Contributor_xml'lang_ca = Just (n, str2attr "ca")
    toAttrFrTyp n Contributor_xml'lang_co = Just (n, str2attr "co")
    toAttrFrTyp n Contributor_xml'lang_cs = Just (n, str2attr "cs")
    toAttrFrTyp n Contributor_xml'lang_cy = Just (n, str2attr "cy")
    toAttrFrTyp n Contributor_xml'lang_da = Just (n, str2attr "da")
    toAttrFrTyp n Contributor_xml'lang_de = Just (n, str2attr "de")
    toAttrFrTyp n Contributor_xml'lang_dz = Just (n, str2attr "dz")
    toAttrFrTyp n Contributor_xml'lang_el = Just (n, str2attr "el")
    toAttrFrTyp n Contributor_xml'lang_en = Just (n, str2attr "en")
    toAttrFrTyp n Contributor_xml'lang_eo = Just (n, str2attr "eo")
    toAttrFrTyp n Contributor_xml'lang_es = Just (n, str2attr "es")
    toAttrFrTyp n Contributor_xml'lang_et = Just (n, str2attr "et")
    toAttrFrTyp n Contributor_xml'lang_eu = Just (n, str2attr "eu")
    toAttrFrTyp n Contributor_xml'lang_fa = Just (n, str2attr "fa")
    toAttrFrTyp n Contributor_xml'lang_fi = Just (n, str2attr "fi")
    toAttrFrTyp n Contributor_xml'lang_fj = Just (n, str2attr "fj")
    toAttrFrTyp n Contributor_xml'lang_fo = Just (n, str2attr "fo")
    toAttrFrTyp n Contributor_xml'lang_fr = Just (n, str2attr "fr")
    toAttrFrTyp n Contributor_xml'lang_fy = Just (n, str2attr "fy")
    toAttrFrTyp n Contributor_xml'lang_ga = Just (n, str2attr "ga")
    toAttrFrTyp n Contributor_xml'lang_gd = Just (n, str2attr "gd")
    toAttrFrTyp n Contributor_xml'lang_gl = Just (n, str2attr "gl")
    toAttrFrTyp n Contributor_xml'lang_gn = Just (n, str2attr "gn")
    toAttrFrTyp n Contributor_xml'lang_gu = Just (n, str2attr "gu")
    toAttrFrTyp n Contributor_xml'lang_ha = Just (n, str2attr "ha")
    toAttrFrTyp n Contributor_xml'lang_he = Just (n, str2attr "he")
    toAttrFrTyp n Contributor_xml'lang_hi = Just (n, str2attr "hi")
    toAttrFrTyp n Contributor_xml'lang_hr = Just (n, str2attr "hr")
    toAttrFrTyp n Contributor_xml'lang_hu = Just (n, str2attr "hu")
    toAttrFrTyp n Contributor_xml'lang_hy = Just (n, str2attr "hy")
    toAttrFrTyp n Contributor_xml'lang_ia = Just (n, str2attr "ia")
    toAttrFrTyp n Contributor_xml'lang_ie = Just (n, str2attr "ie")
    toAttrFrTyp n Contributor_xml'lang_ik = Just (n, str2attr "ik")
    toAttrFrTyp n Contributor_xml'lang_id = Just (n, str2attr "id")
    toAttrFrTyp n Contributor_xml'lang_is = Just (n, str2attr "is")
    toAttrFrTyp n Contributor_xml'lang_it = Just (n, str2attr "it")
    toAttrFrTyp n Contributor_xml'lang_iu = Just (n, str2attr "iu")
    toAttrFrTyp n Contributor_xml'lang_ja = Just (n, str2attr "ja")
    toAttrFrTyp n Contributor_xml'lang_jv = Just (n, str2attr "jv")
    toAttrFrTyp n Contributor_xml'lang_ka = Just (n, str2attr "ka")
    toAttrFrTyp n Contributor_xml'lang_kk = Just (n, str2attr "kk")
    toAttrFrTyp n Contributor_xml'lang_kl = Just (n, str2attr "kl")
    toAttrFrTyp n Contributor_xml'lang_km = Just (n, str2attr "km")
    toAttrFrTyp n Contributor_xml'lang_kn = Just (n, str2attr "kn")
    toAttrFrTyp n Contributor_xml'lang_ko = Just (n, str2attr "ko")
    toAttrFrTyp n Contributor_xml'lang_ks = Just (n, str2attr "ks")
    toAttrFrTyp n Contributor_xml'lang_ku = Just (n, str2attr "ku")
    toAttrFrTyp n Contributor_xml'lang_ky = Just (n, str2attr "ky")
    toAttrFrTyp n Contributor_xml'lang_la = Just (n, str2attr "la")
    toAttrFrTyp n Contributor_xml'lang_ln = Just (n, str2attr "ln")
    toAttrFrTyp n Contributor_xml'lang_lo = Just (n, str2attr "lo")
    toAttrFrTyp n Contributor_xml'lang_lt = Just (n, str2attr "lt")
    toAttrFrTyp n Contributor_xml'lang_lv = Just (n, str2attr "lv")
    toAttrFrTyp n Contributor_xml'lang_mg = Just (n, str2attr "mg")
    toAttrFrTyp n Contributor_xml'lang_mi = Just (n, str2attr "mi")
    toAttrFrTyp n Contributor_xml'lang_mk = Just (n, str2attr "mk")
    toAttrFrTyp n Contributor_xml'lang_ml = Just (n, str2attr "ml")
    toAttrFrTyp n Contributor_xml'lang_mn = Just (n, str2attr "mn")
    toAttrFrTyp n Contributor_xml'lang_mo = Just (n, str2attr "mo")
    toAttrFrTyp n Contributor_xml'lang_mr = Just (n, str2attr "mr")
    toAttrFrTyp n Contributor_xml'lang_ms = Just (n, str2attr "ms")
    toAttrFrTyp n Contributor_xml'lang_mt = Just (n, str2attr "mt")
    toAttrFrTyp n Contributor_xml'lang_my = Just (n, str2attr "my")
    toAttrFrTyp n Contributor_xml'lang_na = Just (n, str2attr "na")
    toAttrFrTyp n Contributor_xml'lang_ne = Just (n, str2attr "ne")
    toAttrFrTyp n Contributor_xml'lang_nl = Just (n, str2attr "nl")
    toAttrFrTyp n Contributor_xml'lang_no = Just (n, str2attr "no")
    toAttrFrTyp n Contributor_xml'lang_oc = Just (n, str2attr "oc")
    toAttrFrTyp n Contributor_xml'lang_om = Just (n, str2attr "om")
    toAttrFrTyp n Contributor_xml'lang_or = Just (n, str2attr "or")
    toAttrFrTyp n Contributor_xml'lang_pa = Just (n, str2attr "pa")
    toAttrFrTyp n Contributor_xml'lang_pl = Just (n, str2attr "pl")
    toAttrFrTyp n Contributor_xml'lang_ps = Just (n, str2attr "ps")
    toAttrFrTyp n Contributor_xml'lang_pt = Just (n, str2attr "pt")
    toAttrFrTyp n Contributor_xml'lang_qu = Just (n, str2attr "qu")
    toAttrFrTyp n Contributor_xml'lang_rm = Just (n, str2attr "rm")
    toAttrFrTyp n Contributor_xml'lang_rn = Just (n, str2attr "rn")
    toAttrFrTyp n Contributor_xml'lang_ro = Just (n, str2attr "ro")
    toAttrFrTyp n Contributor_xml'lang_ru = Just (n, str2attr "ru")
    toAttrFrTyp n Contributor_xml'lang_rw = Just (n, str2attr "rw")
    toAttrFrTyp n Contributor_xml'lang_sa = Just (n, str2attr "sa")
    toAttrFrTyp n Contributor_xml'lang_sd = Just (n, str2attr "sd")
    toAttrFrTyp n Contributor_xml'lang_sg = Just (n, str2attr "sg")
    toAttrFrTyp n Contributor_xml'lang_sh = Just (n, str2attr "sh")
    toAttrFrTyp n Contributor_xml'lang_si = Just (n, str2attr "si")
    toAttrFrTyp n Contributor_xml'lang_sk = Just (n, str2attr "sk")
    toAttrFrTyp n Contributor_xml'lang_sl = Just (n, str2attr "sl")
    toAttrFrTyp n Contributor_xml'lang_sm = Just (n, str2attr "sm")
    toAttrFrTyp n Contributor_xml'lang_sn = Just (n, str2attr "sn")
    toAttrFrTyp n Contributor_xml'lang_so = Just (n, str2attr "so")
    toAttrFrTyp n Contributor_xml'lang_sq = Just (n, str2attr "sq")
    toAttrFrTyp n Contributor_xml'lang_sr = Just (n, str2attr "sr")
    toAttrFrTyp n Contributor_xml'lang_ss = Just (n, str2attr "ss")
    toAttrFrTyp n Contributor_xml'lang_st = Just (n, str2attr "st")
    toAttrFrTyp n Contributor_xml'lang_su = Just (n, str2attr "su")
    toAttrFrTyp n Contributor_xml'lang_sv = Just (n, str2attr "sv")
    toAttrFrTyp n Contributor_xml'lang_sw = Just (n, str2attr "sw")
    toAttrFrTyp n Contributor_xml'lang_ta = Just (n, str2attr "ta")
    toAttrFrTyp n Contributor_xml'lang_te = Just (n, str2attr "te")
    toAttrFrTyp n Contributor_xml'lang_tg = Just (n, str2attr "tg")
    toAttrFrTyp n Contributor_xml'lang_th = Just (n, str2attr "th")
    toAttrFrTyp n Contributor_xml'lang_ti = Just (n, str2attr "ti")
    toAttrFrTyp n Contributor_xml'lang_tk = Just (n, str2attr "tk")
    toAttrFrTyp n Contributor_xml'lang_tl = Just (n, str2attr "tl")
    toAttrFrTyp n Contributor_xml'lang_tn = Just (n, str2attr "tn")
    toAttrFrTyp n Contributor_xml'lang_to = Just (n, str2attr "to")
    toAttrFrTyp n Contributor_xml'lang_tr = Just (n, str2attr "tr")
    toAttrFrTyp n Contributor_xml'lang_ts = Just (n, str2attr "ts")
    toAttrFrTyp n Contributor_xml'lang_tt = Just (n, str2attr "tt")
    toAttrFrTyp n Contributor_xml'lang_tw = Just (n, str2attr "tw")
    toAttrFrTyp n Contributor_xml'lang_ug = Just (n, str2attr "ug")
    toAttrFrTyp n Contributor_xml'lang_uk = Just (n, str2attr "uk")
    toAttrFrTyp n Contributor_xml'lang_ur = Just (n, str2attr "ur")
    toAttrFrTyp n Contributor_xml'lang_uz = Just (n, str2attr "uz")
    toAttrFrTyp n Contributor_xml'lang_vi = Just (n, str2attr "vi")
    toAttrFrTyp n Contributor_xml'lang_vo = Just (n, str2attr "vo")
    toAttrFrTyp n Contributor_xml'lang_wo = Just (n, str2attr "wo")
    toAttrFrTyp n Contributor_xml'lang_xh = Just (n, str2attr "xh")
    toAttrFrTyp n Contributor_xml'lang_yi = Just (n, str2attr "yi")
    toAttrFrTyp n Contributor_xml'lang_yo = Just (n, str2attr "yo")
    toAttrFrTyp n Contributor_xml'lang_za = Just (n, str2attr "za")
    toAttrFrTyp n Contributor_xml'lang_zh = Just (n, str2attr "zh")
    toAttrFrTyp n Contributor_xml'lang_zu = Just (n, str2attr "zu")
instance XmlAttrType Contributor_role where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "aut" = Just Contributor_role_aut
	    translate "ant" = Just Contributor_role_ant
	    translate "clb" = Just Contributor_role_clb
	    translate "edt" = Just Contributor_role_edt
	    translate "ths" = Just Contributor_role_ths
	    translate "trc" = Just Contributor_role_trc
	    translate "trl" = Just Contributor_role_trl
	    translate _ = Nothing
    toAttrFrTyp n Contributor_role_aut = Just (n, str2attr "aut")
    toAttrFrTyp n Contributor_role_ant = Just (n, str2attr "ant")
    toAttrFrTyp n Contributor_role_clb = Just (n, str2attr "clb")
    toAttrFrTyp n Contributor_role_edt = Just (n, str2attr "edt")
    toAttrFrTyp n Contributor_role_ths = Just (n, str2attr "ths")
    toAttrFrTyp n Contributor_role_trc = Just (n, str2attr "trc")
    toAttrFrTyp n Contributor_role_trl = Just (n, str2attr "trl")
instance XmlContent Creator where
    fromElem (CElem (Elem "Creator" as c0):rest) =
	(\(a,ca)->
	   (Just (Creator (fromAttrs as) a), rest))
	(definite fromText "text" "Creator" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Creator as a) =
	[CElem (Elem "Creator" (toAttrs as) (toText a))]
instance XmlAttributes Creator_Attrs where
    fromAttrs as =
	Creator_Attrs
	  { creatorXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  , creatorId = possibleA fromAttrToStr "id" as
	  , creatorStyle = possibleA fromAttrToStr "style" as
	  , creatorMid = possibleA fromAttrToStr "mid" as
	  , creatorXml'lang = defaultA fromAttrToTyp Creator_xml'lang_en "xml:lang" as
	  , creatorRole = defaultA fromAttrToTyp Creator_role_aut "role" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (creatorXmlns v)
	, maybeToAttr toAttrFrStr "id" (creatorId v)
	, maybeToAttr toAttrFrStr "style" (creatorStyle v)
	, maybeToAttr toAttrFrStr "mid" (creatorMid v)
	, defaultToAttr toAttrFrTyp "xml:lang" (creatorXml'lang v)
	, defaultToAttr toAttrFrTyp "role" (creatorRole v)
	]
instance XmlAttrType Creator_xml'lang where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "aa" = Just Creator_xml'lang_aa
	    translate "ab" = Just Creator_xml'lang_ab
	    translate "af" = Just Creator_xml'lang_af
	    translate "am" = Just Creator_xml'lang_am
	    translate "ar" = Just Creator_xml'lang_ar
	    translate "as" = Just Creator_xml'lang_as
	    translate "ay" = Just Creator_xml'lang_ay
	    translate "az" = Just Creator_xml'lang_az
	    translate "ba" = Just Creator_xml'lang_ba
	    translate "be" = Just Creator_xml'lang_be
	    translate "bg" = Just Creator_xml'lang_bg
	    translate "bh" = Just Creator_xml'lang_bh
	    translate "bi" = Just Creator_xml'lang_bi
	    translate "bn" = Just Creator_xml'lang_bn
	    translate "bo" = Just Creator_xml'lang_bo
	    translate "br" = Just Creator_xml'lang_br
	    translate "ca" = Just Creator_xml'lang_ca
	    translate "co" = Just Creator_xml'lang_co
	    translate "cs" = Just Creator_xml'lang_cs
	    translate "cy" = Just Creator_xml'lang_cy
	    translate "da" = Just Creator_xml'lang_da
	    translate "de" = Just Creator_xml'lang_de
	    translate "dz" = Just Creator_xml'lang_dz
	    translate "el" = Just Creator_xml'lang_el
	    translate "en" = Just Creator_xml'lang_en
	    translate "eo" = Just Creator_xml'lang_eo
	    translate "es" = Just Creator_xml'lang_es
	    translate "et" = Just Creator_xml'lang_et
	    translate "eu" = Just Creator_xml'lang_eu
	    translate "fa" = Just Creator_xml'lang_fa
	    translate "fi" = Just Creator_xml'lang_fi
	    translate "fj" = Just Creator_xml'lang_fj
	    translate "fo" = Just Creator_xml'lang_fo
	    translate "fr" = Just Creator_xml'lang_fr
	    translate "fy" = Just Creator_xml'lang_fy
	    translate "ga" = Just Creator_xml'lang_ga
	    translate "gd" = Just Creator_xml'lang_gd
	    translate "gl" = Just Creator_xml'lang_gl
	    translate "gn" = Just Creator_xml'lang_gn
	    translate "gu" = Just Creator_xml'lang_gu
	    translate "ha" = Just Creator_xml'lang_ha
	    translate "he" = Just Creator_xml'lang_he
	    translate "hi" = Just Creator_xml'lang_hi
	    translate "hr" = Just Creator_xml'lang_hr
	    translate "hu" = Just Creator_xml'lang_hu
	    translate "hy" = Just Creator_xml'lang_hy
	    translate "ia" = Just Creator_xml'lang_ia
	    translate "ie" = Just Creator_xml'lang_ie
	    translate "ik" = Just Creator_xml'lang_ik
	    translate "id" = Just Creator_xml'lang_id
	    translate "is" = Just Creator_xml'lang_is
	    translate "it" = Just Creator_xml'lang_it
	    translate "iu" = Just Creator_xml'lang_iu
	    translate "ja" = Just Creator_xml'lang_ja
	    translate "jv" = Just Creator_xml'lang_jv
	    translate "ka" = Just Creator_xml'lang_ka
	    translate "kk" = Just Creator_xml'lang_kk
	    translate "kl" = Just Creator_xml'lang_kl
	    translate "km" = Just Creator_xml'lang_km
	    translate "kn" = Just Creator_xml'lang_kn
	    translate "ko" = Just Creator_xml'lang_ko
	    translate "ks" = Just Creator_xml'lang_ks
	    translate "ku" = Just Creator_xml'lang_ku
	    translate "ky" = Just Creator_xml'lang_ky
	    translate "la" = Just Creator_xml'lang_la
	    translate "ln" = Just Creator_xml'lang_ln
	    translate "lo" = Just Creator_xml'lang_lo
	    translate "lt" = Just Creator_xml'lang_lt
	    translate "lv" = Just Creator_xml'lang_lv
	    translate "mg" = Just Creator_xml'lang_mg
	    translate "mi" = Just Creator_xml'lang_mi
	    translate "mk" = Just Creator_xml'lang_mk
	    translate "ml" = Just Creator_xml'lang_ml
	    translate "mn" = Just Creator_xml'lang_mn
	    translate "mo" = Just Creator_xml'lang_mo
	    translate "mr" = Just Creator_xml'lang_mr
	    translate "ms" = Just Creator_xml'lang_ms
	    translate "mt" = Just Creator_xml'lang_mt
	    translate "my" = Just Creator_xml'lang_my
	    translate "na" = Just Creator_xml'lang_na
	    translate "ne" = Just Creator_xml'lang_ne
	    translate "nl" = Just Creator_xml'lang_nl
	    translate "no" = Just Creator_xml'lang_no
	    translate "oc" = Just Creator_xml'lang_oc
	    translate "om" = Just Creator_xml'lang_om
	    translate "or" = Just Creator_xml'lang_or
	    translate "pa" = Just Creator_xml'lang_pa
	    translate "pl" = Just Creator_xml'lang_pl
	    translate "ps" = Just Creator_xml'lang_ps
	    translate "pt" = Just Creator_xml'lang_pt
	    translate "qu" = Just Creator_xml'lang_qu
	    translate "rm" = Just Creator_xml'lang_rm
	    translate "rn" = Just Creator_xml'lang_rn
	    translate "ro" = Just Creator_xml'lang_ro
	    translate "ru" = Just Creator_xml'lang_ru
	    translate "rw" = Just Creator_xml'lang_rw
	    translate "sa" = Just Creator_xml'lang_sa
	    translate "sd" = Just Creator_xml'lang_sd
	    translate "sg" = Just Creator_xml'lang_sg
	    translate "sh" = Just Creator_xml'lang_sh
	    translate "si" = Just Creator_xml'lang_si
	    translate "sk" = Just Creator_xml'lang_sk
	    translate "sl" = Just Creator_xml'lang_sl
	    translate "sm" = Just Creator_xml'lang_sm
	    translate "sn" = Just Creator_xml'lang_sn
	    translate "so" = Just Creator_xml'lang_so
	    translate "sq" = Just Creator_xml'lang_sq
	    translate "sr" = Just Creator_xml'lang_sr
	    translate "ss" = Just Creator_xml'lang_ss
	    translate "st" = Just Creator_xml'lang_st
	    translate "su" = Just Creator_xml'lang_su
	    translate "sv" = Just Creator_xml'lang_sv
	    translate "sw" = Just Creator_xml'lang_sw
	    translate "ta" = Just Creator_xml'lang_ta
	    translate "te" = Just Creator_xml'lang_te
	    translate "tg" = Just Creator_xml'lang_tg
	    translate "th" = Just Creator_xml'lang_th
	    translate "ti" = Just Creator_xml'lang_ti
	    translate "tk" = Just Creator_xml'lang_tk
	    translate "tl" = Just Creator_xml'lang_tl
	    translate "tn" = Just Creator_xml'lang_tn
	    translate "to" = Just Creator_xml'lang_to
	    translate "tr" = Just Creator_xml'lang_tr
	    translate "ts" = Just Creator_xml'lang_ts
	    translate "tt" = Just Creator_xml'lang_tt
	    translate "tw" = Just Creator_xml'lang_tw
	    translate "ug" = Just Creator_xml'lang_ug
	    translate "uk" = Just Creator_xml'lang_uk
	    translate "ur" = Just Creator_xml'lang_ur
	    translate "uz" = Just Creator_xml'lang_uz
	    translate "vi" = Just Creator_xml'lang_vi
	    translate "vo" = Just Creator_xml'lang_vo
	    translate "wo" = Just Creator_xml'lang_wo
	    translate "xh" = Just Creator_xml'lang_xh
	    translate "yi" = Just Creator_xml'lang_yi
	    translate "yo" = Just Creator_xml'lang_yo
	    translate "za" = Just Creator_xml'lang_za
	    translate "zh" = Just Creator_xml'lang_zh
	    translate "zu" = Just Creator_xml'lang_zu
	    translate _ = Nothing
    toAttrFrTyp n Creator_xml'lang_aa = Just (n, str2attr "aa")
    toAttrFrTyp n Creator_xml'lang_ab = Just (n, str2attr "ab")
    toAttrFrTyp n Creator_xml'lang_af = Just (n, str2attr "af")
    toAttrFrTyp n Creator_xml'lang_am = Just (n, str2attr "am")
    toAttrFrTyp n Creator_xml'lang_ar = Just (n, str2attr "ar")
    toAttrFrTyp n Creator_xml'lang_as = Just (n, str2attr "as")
    toAttrFrTyp n Creator_xml'lang_ay = Just (n, str2attr "ay")
    toAttrFrTyp n Creator_xml'lang_az = Just (n, str2attr "az")
    toAttrFrTyp n Creator_xml'lang_ba = Just (n, str2attr "ba")
    toAttrFrTyp n Creator_xml'lang_be = Just (n, str2attr "be")
    toAttrFrTyp n Creator_xml'lang_bg = Just (n, str2attr "bg")
    toAttrFrTyp n Creator_xml'lang_bh = Just (n, str2attr "bh")
    toAttrFrTyp n Creator_xml'lang_bi = Just (n, str2attr "bi")
    toAttrFrTyp n Creator_xml'lang_bn = Just (n, str2attr "bn")
    toAttrFrTyp n Creator_xml'lang_bo = Just (n, str2attr "bo")
    toAttrFrTyp n Creator_xml'lang_br = Just (n, str2attr "br")
    toAttrFrTyp n Creator_xml'lang_ca = Just (n, str2attr "ca")
    toAttrFrTyp n Creator_xml'lang_co = Just (n, str2attr "co")
    toAttrFrTyp n Creator_xml'lang_cs = Just (n, str2attr "cs")
    toAttrFrTyp n Creator_xml'lang_cy = Just (n, str2attr "cy")
    toAttrFrTyp n Creator_xml'lang_da = Just (n, str2attr "da")
    toAttrFrTyp n Creator_xml'lang_de = Just (n, str2attr "de")
    toAttrFrTyp n Creator_xml'lang_dz = Just (n, str2attr "dz")
    toAttrFrTyp n Creator_xml'lang_el = Just (n, str2attr "el")
    toAttrFrTyp n Creator_xml'lang_en = Just (n, str2attr "en")
    toAttrFrTyp n Creator_xml'lang_eo = Just (n, str2attr "eo")
    toAttrFrTyp n Creator_xml'lang_es = Just (n, str2attr "es")
    toAttrFrTyp n Creator_xml'lang_et = Just (n, str2attr "et")
    toAttrFrTyp n Creator_xml'lang_eu = Just (n, str2attr "eu")
    toAttrFrTyp n Creator_xml'lang_fa = Just (n, str2attr "fa")
    toAttrFrTyp n Creator_xml'lang_fi = Just (n, str2attr "fi")
    toAttrFrTyp n Creator_xml'lang_fj = Just (n, str2attr "fj")
    toAttrFrTyp n Creator_xml'lang_fo = Just (n, str2attr "fo")
    toAttrFrTyp n Creator_xml'lang_fr = Just (n, str2attr "fr")
    toAttrFrTyp n Creator_xml'lang_fy = Just (n, str2attr "fy")
    toAttrFrTyp n Creator_xml'lang_ga = Just (n, str2attr "ga")
    toAttrFrTyp n Creator_xml'lang_gd = Just (n, str2attr "gd")
    toAttrFrTyp n Creator_xml'lang_gl = Just (n, str2attr "gl")
    toAttrFrTyp n Creator_xml'lang_gn = Just (n, str2attr "gn")
    toAttrFrTyp n Creator_xml'lang_gu = Just (n, str2attr "gu")
    toAttrFrTyp n Creator_xml'lang_ha = Just (n, str2attr "ha")
    toAttrFrTyp n Creator_xml'lang_he = Just (n, str2attr "he")
    toAttrFrTyp n Creator_xml'lang_hi = Just (n, str2attr "hi")
    toAttrFrTyp n Creator_xml'lang_hr = Just (n, str2attr "hr")
    toAttrFrTyp n Creator_xml'lang_hu = Just (n, str2attr "hu")
    toAttrFrTyp n Creator_xml'lang_hy = Just (n, str2attr "hy")
    toAttrFrTyp n Creator_xml'lang_ia = Just (n, str2attr "ia")
    toAttrFrTyp n Creator_xml'lang_ie = Just (n, str2attr "ie")
    toAttrFrTyp n Creator_xml'lang_ik = Just (n, str2attr "ik")
    toAttrFrTyp n Creator_xml'lang_id = Just (n, str2attr "id")
    toAttrFrTyp n Creator_xml'lang_is = Just (n, str2attr "is")
    toAttrFrTyp n Creator_xml'lang_it = Just (n, str2attr "it")
    toAttrFrTyp n Creator_xml'lang_iu = Just (n, str2attr "iu")
    toAttrFrTyp n Creator_xml'lang_ja = Just (n, str2attr "ja")
    toAttrFrTyp n Creator_xml'lang_jv = Just (n, str2attr "jv")
    toAttrFrTyp n Creator_xml'lang_ka = Just (n, str2attr "ka")
    toAttrFrTyp n Creator_xml'lang_kk = Just (n, str2attr "kk")
    toAttrFrTyp n Creator_xml'lang_kl = Just (n, str2attr "kl")
    toAttrFrTyp n Creator_xml'lang_km = Just (n, str2attr "km")
    toAttrFrTyp n Creator_xml'lang_kn = Just (n, str2attr "kn")
    toAttrFrTyp n Creator_xml'lang_ko = Just (n, str2attr "ko")
    toAttrFrTyp n Creator_xml'lang_ks = Just (n, str2attr "ks")
    toAttrFrTyp n Creator_xml'lang_ku = Just (n, str2attr "ku")
    toAttrFrTyp n Creator_xml'lang_ky = Just (n, str2attr "ky")
    toAttrFrTyp n Creator_xml'lang_la = Just (n, str2attr "la")
    toAttrFrTyp n Creator_xml'lang_ln = Just (n, str2attr "ln")
    toAttrFrTyp n Creator_xml'lang_lo = Just (n, str2attr "lo")
    toAttrFrTyp n Creator_xml'lang_lt = Just (n, str2attr "lt")
    toAttrFrTyp n Creator_xml'lang_lv = Just (n, str2attr "lv")
    toAttrFrTyp n Creator_xml'lang_mg = Just (n, str2attr "mg")
    toAttrFrTyp n Creator_xml'lang_mi = Just (n, str2attr "mi")
    toAttrFrTyp n Creator_xml'lang_mk = Just (n, str2attr "mk")
    toAttrFrTyp n Creator_xml'lang_ml = Just (n, str2attr "ml")
    toAttrFrTyp n Creator_xml'lang_mn = Just (n, str2attr "mn")
    toAttrFrTyp n Creator_xml'lang_mo = Just (n, str2attr "mo")
    toAttrFrTyp n Creator_xml'lang_mr = Just (n, str2attr "mr")
    toAttrFrTyp n Creator_xml'lang_ms = Just (n, str2attr "ms")
    toAttrFrTyp n Creator_xml'lang_mt = Just (n, str2attr "mt")
    toAttrFrTyp n Creator_xml'lang_my = Just (n, str2attr "my")
    toAttrFrTyp n Creator_xml'lang_na = Just (n, str2attr "na")
    toAttrFrTyp n Creator_xml'lang_ne = Just (n, str2attr "ne")
    toAttrFrTyp n Creator_xml'lang_nl = Just (n, str2attr "nl")
    toAttrFrTyp n Creator_xml'lang_no = Just (n, str2attr "no")
    toAttrFrTyp n Creator_xml'lang_oc = Just (n, str2attr "oc")
    toAttrFrTyp n Creator_xml'lang_om = Just (n, str2attr "om")
    toAttrFrTyp n Creator_xml'lang_or = Just (n, str2attr "or")
    toAttrFrTyp n Creator_xml'lang_pa = Just (n, str2attr "pa")
    toAttrFrTyp n Creator_xml'lang_pl = Just (n, str2attr "pl")
    toAttrFrTyp n Creator_xml'lang_ps = Just (n, str2attr "ps")
    toAttrFrTyp n Creator_xml'lang_pt = Just (n, str2attr "pt")
    toAttrFrTyp n Creator_xml'lang_qu = Just (n, str2attr "qu")
    toAttrFrTyp n Creator_xml'lang_rm = Just (n, str2attr "rm")
    toAttrFrTyp n Creator_xml'lang_rn = Just (n, str2attr "rn")
    toAttrFrTyp n Creator_xml'lang_ro = Just (n, str2attr "ro")
    toAttrFrTyp n Creator_xml'lang_ru = Just (n, str2attr "ru")
    toAttrFrTyp n Creator_xml'lang_rw = Just (n, str2attr "rw")
    toAttrFrTyp n Creator_xml'lang_sa = Just (n, str2attr "sa")
    toAttrFrTyp n Creator_xml'lang_sd = Just (n, str2attr "sd")
    toAttrFrTyp n Creator_xml'lang_sg = Just (n, str2attr "sg")
    toAttrFrTyp n Creator_xml'lang_sh = Just (n, str2attr "sh")
    toAttrFrTyp n Creator_xml'lang_si = Just (n, str2attr "si")
    toAttrFrTyp n Creator_xml'lang_sk = Just (n, str2attr "sk")
    toAttrFrTyp n Creator_xml'lang_sl = Just (n, str2attr "sl")
    toAttrFrTyp n Creator_xml'lang_sm = Just (n, str2attr "sm")
    toAttrFrTyp n Creator_xml'lang_sn = Just (n, str2attr "sn")
    toAttrFrTyp n Creator_xml'lang_so = Just (n, str2attr "so")
    toAttrFrTyp n Creator_xml'lang_sq = Just (n, str2attr "sq")
    toAttrFrTyp n Creator_xml'lang_sr = Just (n, str2attr "sr")
    toAttrFrTyp n Creator_xml'lang_ss = Just (n, str2attr "ss")
    toAttrFrTyp n Creator_xml'lang_st = Just (n, str2attr "st")
    toAttrFrTyp n Creator_xml'lang_su = Just (n, str2attr "su")
    toAttrFrTyp n Creator_xml'lang_sv = Just (n, str2attr "sv")
    toAttrFrTyp n Creator_xml'lang_sw = Just (n, str2attr "sw")
    toAttrFrTyp n Creator_xml'lang_ta = Just (n, str2attr "ta")
    toAttrFrTyp n Creator_xml'lang_te = Just (n, str2attr "te")
    toAttrFrTyp n Creator_xml'lang_tg = Just (n, str2attr "tg")
    toAttrFrTyp n Creator_xml'lang_th = Just (n, str2attr "th")
    toAttrFrTyp n Creator_xml'lang_ti = Just (n, str2attr "ti")
    toAttrFrTyp n Creator_xml'lang_tk = Just (n, str2attr "tk")
    toAttrFrTyp n Creator_xml'lang_tl = Just (n, str2attr "tl")
    toAttrFrTyp n Creator_xml'lang_tn = Just (n, str2attr "tn")
    toAttrFrTyp n Creator_xml'lang_to = Just (n, str2attr "to")
    toAttrFrTyp n Creator_xml'lang_tr = Just (n, str2attr "tr")
    toAttrFrTyp n Creator_xml'lang_ts = Just (n, str2attr "ts")
    toAttrFrTyp n Creator_xml'lang_tt = Just (n, str2attr "tt")
    toAttrFrTyp n Creator_xml'lang_tw = Just (n, str2attr "tw")
    toAttrFrTyp n Creator_xml'lang_ug = Just (n, str2attr "ug")
    toAttrFrTyp n Creator_xml'lang_uk = Just (n, str2attr "uk")
    toAttrFrTyp n Creator_xml'lang_ur = Just (n, str2attr "ur")
    toAttrFrTyp n Creator_xml'lang_uz = Just (n, str2attr "uz")
    toAttrFrTyp n Creator_xml'lang_vi = Just (n, str2attr "vi")
    toAttrFrTyp n Creator_xml'lang_vo = Just (n, str2attr "vo")
    toAttrFrTyp n Creator_xml'lang_wo = Just (n, str2attr "wo")
    toAttrFrTyp n Creator_xml'lang_xh = Just (n, str2attr "xh")
    toAttrFrTyp n Creator_xml'lang_yi = Just (n, str2attr "yi")
    toAttrFrTyp n Creator_xml'lang_yo = Just (n, str2attr "yo")
    toAttrFrTyp n Creator_xml'lang_za = Just (n, str2attr "za")
    toAttrFrTyp n Creator_xml'lang_zh = Just (n, str2attr "zh")
    toAttrFrTyp n Creator_xml'lang_zu = Just (n, str2attr "zu")
instance XmlAttrType Creator_role where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "aut" = Just Creator_role_aut
	    translate "ant" = Just Creator_role_ant
	    translate "clb" = Just Creator_role_clb
	    translate "edt" = Just Creator_role_edt
	    translate "ths" = Just Creator_role_ths
	    translate "trc" = Just Creator_role_trc
	    translate "trl" = Just Creator_role_trl
	    translate _ = Nothing
    toAttrFrTyp n Creator_role_aut = Just (n, str2attr "aut")
    toAttrFrTyp n Creator_role_ant = Just (n, str2attr "ant")
    toAttrFrTyp n Creator_role_clb = Just (n, str2attr "clb")
    toAttrFrTyp n Creator_role_edt = Just (n, str2attr "edt")
    toAttrFrTyp n Creator_role_ths = Just (n, str2attr "ths")
    toAttrFrTyp n Creator_role_trc = Just (n, str2attr "trc")
    toAttrFrTyp n Creator_role_trl = Just (n, str2attr "trl")
instance XmlContent Title where
    fromElem (CElem (Elem "Title" as c0):rest) =
	(\(a,ca)->
	   (Just (Title (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Title as a) =
	[CElem (Elem "Title" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Title_Attrs where
    fromAttrs as =
	Title_Attrs
	  { titleXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  , titleXml'lang = defaultA fromAttrToTyp Title_xml'lang_en "xml:lang" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (titleXmlns v)
	, defaultToAttr toAttrFrTyp "xml:lang" (titleXml'lang v)
	]
instance XmlContent Title_ where
    fromElem c0 =
	case (fromText c0) of
	(Just a,rest) -> (Just (Title_Str a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Title_OMOBJ a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (Title_Omlet a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (Title_With a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (Title_Ref a), rest)
					(_,_) ->
						case (fromElem c0) of
						(Just a,rest) -> (Just (Title_Ignore a), rest)
						(_,_) ->
						    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Title_Str a) = toText a
    toElem (Title_OMOBJ a) = toElem a
    toElem (Title_Omlet a) = toElem a
    toElem (Title_With a) = toElem a
    toElem (Title_Ref a) = toElem a
    toElem (Title_Ignore a) = toElem a
instance XmlAttrType Title_xml'lang where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "aa" = Just Title_xml'lang_aa
	    translate "ab" = Just Title_xml'lang_ab
	    translate "af" = Just Title_xml'lang_af
	    translate "am" = Just Title_xml'lang_am
	    translate "ar" = Just Title_xml'lang_ar
	    translate "as" = Just Title_xml'lang_as
	    translate "ay" = Just Title_xml'lang_ay
	    translate "az" = Just Title_xml'lang_az
	    translate "ba" = Just Title_xml'lang_ba
	    translate "be" = Just Title_xml'lang_be
	    translate "bg" = Just Title_xml'lang_bg
	    translate "bh" = Just Title_xml'lang_bh
	    translate "bi" = Just Title_xml'lang_bi
	    translate "bn" = Just Title_xml'lang_bn
	    translate "bo" = Just Title_xml'lang_bo
	    translate "br" = Just Title_xml'lang_br
	    translate "ca" = Just Title_xml'lang_ca
	    translate "co" = Just Title_xml'lang_co
	    translate "cs" = Just Title_xml'lang_cs
	    translate "cy" = Just Title_xml'lang_cy
	    translate "da" = Just Title_xml'lang_da
	    translate "de" = Just Title_xml'lang_de
	    translate "dz" = Just Title_xml'lang_dz
	    translate "el" = Just Title_xml'lang_el
	    translate "en" = Just Title_xml'lang_en
	    translate "eo" = Just Title_xml'lang_eo
	    translate "es" = Just Title_xml'lang_es
	    translate "et" = Just Title_xml'lang_et
	    translate "eu" = Just Title_xml'lang_eu
	    translate "fa" = Just Title_xml'lang_fa
	    translate "fi" = Just Title_xml'lang_fi
	    translate "fj" = Just Title_xml'lang_fj
	    translate "fo" = Just Title_xml'lang_fo
	    translate "fr" = Just Title_xml'lang_fr
	    translate "fy" = Just Title_xml'lang_fy
	    translate "ga" = Just Title_xml'lang_ga
	    translate "gd" = Just Title_xml'lang_gd
	    translate "gl" = Just Title_xml'lang_gl
	    translate "gn" = Just Title_xml'lang_gn
	    translate "gu" = Just Title_xml'lang_gu
	    translate "ha" = Just Title_xml'lang_ha
	    translate "he" = Just Title_xml'lang_he
	    translate "hi" = Just Title_xml'lang_hi
	    translate "hr" = Just Title_xml'lang_hr
	    translate "hu" = Just Title_xml'lang_hu
	    translate "hy" = Just Title_xml'lang_hy
	    translate "ia" = Just Title_xml'lang_ia
	    translate "ie" = Just Title_xml'lang_ie
	    translate "ik" = Just Title_xml'lang_ik
	    translate "id" = Just Title_xml'lang_id
	    translate "is" = Just Title_xml'lang_is
	    translate "it" = Just Title_xml'lang_it
	    translate "iu" = Just Title_xml'lang_iu
	    translate "ja" = Just Title_xml'lang_ja
	    translate "jv" = Just Title_xml'lang_jv
	    translate "ka" = Just Title_xml'lang_ka
	    translate "kk" = Just Title_xml'lang_kk
	    translate "kl" = Just Title_xml'lang_kl
	    translate "km" = Just Title_xml'lang_km
	    translate "kn" = Just Title_xml'lang_kn
	    translate "ko" = Just Title_xml'lang_ko
	    translate "ks" = Just Title_xml'lang_ks
	    translate "ku" = Just Title_xml'lang_ku
	    translate "ky" = Just Title_xml'lang_ky
	    translate "la" = Just Title_xml'lang_la
	    translate "ln" = Just Title_xml'lang_ln
	    translate "lo" = Just Title_xml'lang_lo
	    translate "lt" = Just Title_xml'lang_lt
	    translate "lv" = Just Title_xml'lang_lv
	    translate "mg" = Just Title_xml'lang_mg
	    translate "mi" = Just Title_xml'lang_mi
	    translate "mk" = Just Title_xml'lang_mk
	    translate "ml" = Just Title_xml'lang_ml
	    translate "mn" = Just Title_xml'lang_mn
	    translate "mo" = Just Title_xml'lang_mo
	    translate "mr" = Just Title_xml'lang_mr
	    translate "ms" = Just Title_xml'lang_ms
	    translate "mt" = Just Title_xml'lang_mt
	    translate "my" = Just Title_xml'lang_my
	    translate "na" = Just Title_xml'lang_na
	    translate "ne" = Just Title_xml'lang_ne
	    translate "nl" = Just Title_xml'lang_nl
	    translate "no" = Just Title_xml'lang_no
	    translate "oc" = Just Title_xml'lang_oc
	    translate "om" = Just Title_xml'lang_om
	    translate "or" = Just Title_xml'lang_or
	    translate "pa" = Just Title_xml'lang_pa
	    translate "pl" = Just Title_xml'lang_pl
	    translate "ps" = Just Title_xml'lang_ps
	    translate "pt" = Just Title_xml'lang_pt
	    translate "qu" = Just Title_xml'lang_qu
	    translate "rm" = Just Title_xml'lang_rm
	    translate "rn" = Just Title_xml'lang_rn
	    translate "ro" = Just Title_xml'lang_ro
	    translate "ru" = Just Title_xml'lang_ru
	    translate "rw" = Just Title_xml'lang_rw
	    translate "sa" = Just Title_xml'lang_sa
	    translate "sd" = Just Title_xml'lang_sd
	    translate "sg" = Just Title_xml'lang_sg
	    translate "sh" = Just Title_xml'lang_sh
	    translate "si" = Just Title_xml'lang_si
	    translate "sk" = Just Title_xml'lang_sk
	    translate "sl" = Just Title_xml'lang_sl
	    translate "sm" = Just Title_xml'lang_sm
	    translate "sn" = Just Title_xml'lang_sn
	    translate "so" = Just Title_xml'lang_so
	    translate "sq" = Just Title_xml'lang_sq
	    translate "sr" = Just Title_xml'lang_sr
	    translate "ss" = Just Title_xml'lang_ss
	    translate "st" = Just Title_xml'lang_st
	    translate "su" = Just Title_xml'lang_su
	    translate "sv" = Just Title_xml'lang_sv
	    translate "sw" = Just Title_xml'lang_sw
	    translate "ta" = Just Title_xml'lang_ta
	    translate "te" = Just Title_xml'lang_te
	    translate "tg" = Just Title_xml'lang_tg
	    translate "th" = Just Title_xml'lang_th
	    translate "ti" = Just Title_xml'lang_ti
	    translate "tk" = Just Title_xml'lang_tk
	    translate "tl" = Just Title_xml'lang_tl
	    translate "tn" = Just Title_xml'lang_tn
	    translate "to" = Just Title_xml'lang_to
	    translate "tr" = Just Title_xml'lang_tr
	    translate "ts" = Just Title_xml'lang_ts
	    translate "tt" = Just Title_xml'lang_tt
	    translate "tw" = Just Title_xml'lang_tw
	    translate "ug" = Just Title_xml'lang_ug
	    translate "uk" = Just Title_xml'lang_uk
	    translate "ur" = Just Title_xml'lang_ur
	    translate "uz" = Just Title_xml'lang_uz
	    translate "vi" = Just Title_xml'lang_vi
	    translate "vo" = Just Title_xml'lang_vo
	    translate "wo" = Just Title_xml'lang_wo
	    translate "xh" = Just Title_xml'lang_xh
	    translate "yi" = Just Title_xml'lang_yi
	    translate "yo" = Just Title_xml'lang_yo
	    translate "za" = Just Title_xml'lang_za
	    translate "zh" = Just Title_xml'lang_zh
	    translate "zu" = Just Title_xml'lang_zu
	    translate _ = Nothing
    toAttrFrTyp n Title_xml'lang_aa = Just (n, str2attr "aa")
    toAttrFrTyp n Title_xml'lang_ab = Just (n, str2attr "ab")
    toAttrFrTyp n Title_xml'lang_af = Just (n, str2attr "af")
    toAttrFrTyp n Title_xml'lang_am = Just (n, str2attr "am")
    toAttrFrTyp n Title_xml'lang_ar = Just (n, str2attr "ar")
    toAttrFrTyp n Title_xml'lang_as = Just (n, str2attr "as")
    toAttrFrTyp n Title_xml'lang_ay = Just (n, str2attr "ay")
    toAttrFrTyp n Title_xml'lang_az = Just (n, str2attr "az")
    toAttrFrTyp n Title_xml'lang_ba = Just (n, str2attr "ba")
    toAttrFrTyp n Title_xml'lang_be = Just (n, str2attr "be")
    toAttrFrTyp n Title_xml'lang_bg = Just (n, str2attr "bg")
    toAttrFrTyp n Title_xml'lang_bh = Just (n, str2attr "bh")
    toAttrFrTyp n Title_xml'lang_bi = Just (n, str2attr "bi")
    toAttrFrTyp n Title_xml'lang_bn = Just (n, str2attr "bn")
    toAttrFrTyp n Title_xml'lang_bo = Just (n, str2attr "bo")
    toAttrFrTyp n Title_xml'lang_br = Just (n, str2attr "br")
    toAttrFrTyp n Title_xml'lang_ca = Just (n, str2attr "ca")
    toAttrFrTyp n Title_xml'lang_co = Just (n, str2attr "co")
    toAttrFrTyp n Title_xml'lang_cs = Just (n, str2attr "cs")
    toAttrFrTyp n Title_xml'lang_cy = Just (n, str2attr "cy")
    toAttrFrTyp n Title_xml'lang_da = Just (n, str2attr "da")
    toAttrFrTyp n Title_xml'lang_de = Just (n, str2attr "de")
    toAttrFrTyp n Title_xml'lang_dz = Just (n, str2attr "dz")
    toAttrFrTyp n Title_xml'lang_el = Just (n, str2attr "el")
    toAttrFrTyp n Title_xml'lang_en = Just (n, str2attr "en")
    toAttrFrTyp n Title_xml'lang_eo = Just (n, str2attr "eo")
    toAttrFrTyp n Title_xml'lang_es = Just (n, str2attr "es")
    toAttrFrTyp n Title_xml'lang_et = Just (n, str2attr "et")
    toAttrFrTyp n Title_xml'lang_eu = Just (n, str2attr "eu")
    toAttrFrTyp n Title_xml'lang_fa = Just (n, str2attr "fa")
    toAttrFrTyp n Title_xml'lang_fi = Just (n, str2attr "fi")
    toAttrFrTyp n Title_xml'lang_fj = Just (n, str2attr "fj")
    toAttrFrTyp n Title_xml'lang_fo = Just (n, str2attr "fo")
    toAttrFrTyp n Title_xml'lang_fr = Just (n, str2attr "fr")
    toAttrFrTyp n Title_xml'lang_fy = Just (n, str2attr "fy")
    toAttrFrTyp n Title_xml'lang_ga = Just (n, str2attr "ga")
    toAttrFrTyp n Title_xml'lang_gd = Just (n, str2attr "gd")
    toAttrFrTyp n Title_xml'lang_gl = Just (n, str2attr "gl")
    toAttrFrTyp n Title_xml'lang_gn = Just (n, str2attr "gn")
    toAttrFrTyp n Title_xml'lang_gu = Just (n, str2attr "gu")
    toAttrFrTyp n Title_xml'lang_ha = Just (n, str2attr "ha")
    toAttrFrTyp n Title_xml'lang_he = Just (n, str2attr "he")
    toAttrFrTyp n Title_xml'lang_hi = Just (n, str2attr "hi")
    toAttrFrTyp n Title_xml'lang_hr = Just (n, str2attr "hr")
    toAttrFrTyp n Title_xml'lang_hu = Just (n, str2attr "hu")
    toAttrFrTyp n Title_xml'lang_hy = Just (n, str2attr "hy")
    toAttrFrTyp n Title_xml'lang_ia = Just (n, str2attr "ia")
    toAttrFrTyp n Title_xml'lang_ie = Just (n, str2attr "ie")
    toAttrFrTyp n Title_xml'lang_ik = Just (n, str2attr "ik")
    toAttrFrTyp n Title_xml'lang_id = Just (n, str2attr "id")
    toAttrFrTyp n Title_xml'lang_is = Just (n, str2attr "is")
    toAttrFrTyp n Title_xml'lang_it = Just (n, str2attr "it")
    toAttrFrTyp n Title_xml'lang_iu = Just (n, str2attr "iu")
    toAttrFrTyp n Title_xml'lang_ja = Just (n, str2attr "ja")
    toAttrFrTyp n Title_xml'lang_jv = Just (n, str2attr "jv")
    toAttrFrTyp n Title_xml'lang_ka = Just (n, str2attr "ka")
    toAttrFrTyp n Title_xml'lang_kk = Just (n, str2attr "kk")
    toAttrFrTyp n Title_xml'lang_kl = Just (n, str2attr "kl")
    toAttrFrTyp n Title_xml'lang_km = Just (n, str2attr "km")
    toAttrFrTyp n Title_xml'lang_kn = Just (n, str2attr "kn")
    toAttrFrTyp n Title_xml'lang_ko = Just (n, str2attr "ko")
    toAttrFrTyp n Title_xml'lang_ks = Just (n, str2attr "ks")
    toAttrFrTyp n Title_xml'lang_ku = Just (n, str2attr "ku")
    toAttrFrTyp n Title_xml'lang_ky = Just (n, str2attr "ky")
    toAttrFrTyp n Title_xml'lang_la = Just (n, str2attr "la")
    toAttrFrTyp n Title_xml'lang_ln = Just (n, str2attr "ln")
    toAttrFrTyp n Title_xml'lang_lo = Just (n, str2attr "lo")
    toAttrFrTyp n Title_xml'lang_lt = Just (n, str2attr "lt")
    toAttrFrTyp n Title_xml'lang_lv = Just (n, str2attr "lv")
    toAttrFrTyp n Title_xml'lang_mg = Just (n, str2attr "mg")
    toAttrFrTyp n Title_xml'lang_mi = Just (n, str2attr "mi")
    toAttrFrTyp n Title_xml'lang_mk = Just (n, str2attr "mk")
    toAttrFrTyp n Title_xml'lang_ml = Just (n, str2attr "ml")
    toAttrFrTyp n Title_xml'lang_mn = Just (n, str2attr "mn")
    toAttrFrTyp n Title_xml'lang_mo = Just (n, str2attr "mo")
    toAttrFrTyp n Title_xml'lang_mr = Just (n, str2attr "mr")
    toAttrFrTyp n Title_xml'lang_ms = Just (n, str2attr "ms")
    toAttrFrTyp n Title_xml'lang_mt = Just (n, str2attr "mt")
    toAttrFrTyp n Title_xml'lang_my = Just (n, str2attr "my")
    toAttrFrTyp n Title_xml'lang_na = Just (n, str2attr "na")
    toAttrFrTyp n Title_xml'lang_ne = Just (n, str2attr "ne")
    toAttrFrTyp n Title_xml'lang_nl = Just (n, str2attr "nl")
    toAttrFrTyp n Title_xml'lang_no = Just (n, str2attr "no")
    toAttrFrTyp n Title_xml'lang_oc = Just (n, str2attr "oc")
    toAttrFrTyp n Title_xml'lang_om = Just (n, str2attr "om")
    toAttrFrTyp n Title_xml'lang_or = Just (n, str2attr "or")
    toAttrFrTyp n Title_xml'lang_pa = Just (n, str2attr "pa")
    toAttrFrTyp n Title_xml'lang_pl = Just (n, str2attr "pl")
    toAttrFrTyp n Title_xml'lang_ps = Just (n, str2attr "ps")
    toAttrFrTyp n Title_xml'lang_pt = Just (n, str2attr "pt")
    toAttrFrTyp n Title_xml'lang_qu = Just (n, str2attr "qu")
    toAttrFrTyp n Title_xml'lang_rm = Just (n, str2attr "rm")
    toAttrFrTyp n Title_xml'lang_rn = Just (n, str2attr "rn")
    toAttrFrTyp n Title_xml'lang_ro = Just (n, str2attr "ro")
    toAttrFrTyp n Title_xml'lang_ru = Just (n, str2attr "ru")
    toAttrFrTyp n Title_xml'lang_rw = Just (n, str2attr "rw")
    toAttrFrTyp n Title_xml'lang_sa = Just (n, str2attr "sa")
    toAttrFrTyp n Title_xml'lang_sd = Just (n, str2attr "sd")
    toAttrFrTyp n Title_xml'lang_sg = Just (n, str2attr "sg")
    toAttrFrTyp n Title_xml'lang_sh = Just (n, str2attr "sh")
    toAttrFrTyp n Title_xml'lang_si = Just (n, str2attr "si")
    toAttrFrTyp n Title_xml'lang_sk = Just (n, str2attr "sk")
    toAttrFrTyp n Title_xml'lang_sl = Just (n, str2attr "sl")
    toAttrFrTyp n Title_xml'lang_sm = Just (n, str2attr "sm")
    toAttrFrTyp n Title_xml'lang_sn = Just (n, str2attr "sn")
    toAttrFrTyp n Title_xml'lang_so = Just (n, str2attr "so")
    toAttrFrTyp n Title_xml'lang_sq = Just (n, str2attr "sq")
    toAttrFrTyp n Title_xml'lang_sr = Just (n, str2attr "sr")
    toAttrFrTyp n Title_xml'lang_ss = Just (n, str2attr "ss")
    toAttrFrTyp n Title_xml'lang_st = Just (n, str2attr "st")
    toAttrFrTyp n Title_xml'lang_su = Just (n, str2attr "su")
    toAttrFrTyp n Title_xml'lang_sv = Just (n, str2attr "sv")
    toAttrFrTyp n Title_xml'lang_sw = Just (n, str2attr "sw")
    toAttrFrTyp n Title_xml'lang_ta = Just (n, str2attr "ta")
    toAttrFrTyp n Title_xml'lang_te = Just (n, str2attr "te")
    toAttrFrTyp n Title_xml'lang_tg = Just (n, str2attr "tg")
    toAttrFrTyp n Title_xml'lang_th = Just (n, str2attr "th")
    toAttrFrTyp n Title_xml'lang_ti = Just (n, str2attr "ti")
    toAttrFrTyp n Title_xml'lang_tk = Just (n, str2attr "tk")
    toAttrFrTyp n Title_xml'lang_tl = Just (n, str2attr "tl")
    toAttrFrTyp n Title_xml'lang_tn = Just (n, str2attr "tn")
    toAttrFrTyp n Title_xml'lang_to = Just (n, str2attr "to")
    toAttrFrTyp n Title_xml'lang_tr = Just (n, str2attr "tr")
    toAttrFrTyp n Title_xml'lang_ts = Just (n, str2attr "ts")
    toAttrFrTyp n Title_xml'lang_tt = Just (n, str2attr "tt")
    toAttrFrTyp n Title_xml'lang_tw = Just (n, str2attr "tw")
    toAttrFrTyp n Title_xml'lang_ug = Just (n, str2attr "ug")
    toAttrFrTyp n Title_xml'lang_uk = Just (n, str2attr "uk")
    toAttrFrTyp n Title_xml'lang_ur = Just (n, str2attr "ur")
    toAttrFrTyp n Title_xml'lang_uz = Just (n, str2attr "uz")
    toAttrFrTyp n Title_xml'lang_vi = Just (n, str2attr "vi")
    toAttrFrTyp n Title_xml'lang_vo = Just (n, str2attr "vo")
    toAttrFrTyp n Title_xml'lang_wo = Just (n, str2attr "wo")
    toAttrFrTyp n Title_xml'lang_xh = Just (n, str2attr "xh")
    toAttrFrTyp n Title_xml'lang_yi = Just (n, str2attr "yi")
    toAttrFrTyp n Title_xml'lang_yo = Just (n, str2attr "yo")
    toAttrFrTyp n Title_xml'lang_za = Just (n, str2attr "za")
    toAttrFrTyp n Title_xml'lang_zh = Just (n, str2attr "zh")
    toAttrFrTyp n Title_xml'lang_zu = Just (n, str2attr "zu")
instance XmlContent Subject where
    fromElem (CElem (Elem "Subject" as c0):rest) =
	(\(a,ca)->
	   (Just (Subject (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Subject as a) =
	[CElem (Elem "Subject" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Subject_Attrs where
    fromAttrs as =
	Subject_Attrs
	  { subjectXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  , subjectXml'lang = defaultA fromAttrToTyp Subject_xml'lang_en "xml:lang" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (subjectXmlns v)
	, defaultToAttr toAttrFrTyp "xml:lang" (subjectXml'lang v)
	]
instance XmlContent Subject_ where
    fromElem c0 =
	case (fromText c0) of
	(Just a,rest) -> (Just (Subject_Str a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Subject_OMOBJ a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (Subject_Omlet a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (Subject_With a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (Subject_Ref a), rest)
					(_,_) ->
						case (fromElem c0) of
						(Just a,rest) -> (Just (Subject_Ignore a), rest)
						(_,_) ->
						    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Subject_Str a) = toText a
    toElem (Subject_OMOBJ a) = toElem a
    toElem (Subject_Omlet a) = toElem a
    toElem (Subject_With a) = toElem a
    toElem (Subject_Ref a) = toElem a
    toElem (Subject_Ignore a) = toElem a
instance XmlAttrType Subject_xml'lang where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "aa" = Just Subject_xml'lang_aa
	    translate "ab" = Just Subject_xml'lang_ab
	    translate "af" = Just Subject_xml'lang_af
	    translate "am" = Just Subject_xml'lang_am
	    translate "ar" = Just Subject_xml'lang_ar
	    translate "as" = Just Subject_xml'lang_as
	    translate "ay" = Just Subject_xml'lang_ay
	    translate "az" = Just Subject_xml'lang_az
	    translate "ba" = Just Subject_xml'lang_ba
	    translate "be" = Just Subject_xml'lang_be
	    translate "bg" = Just Subject_xml'lang_bg
	    translate "bh" = Just Subject_xml'lang_bh
	    translate "bi" = Just Subject_xml'lang_bi
	    translate "bn" = Just Subject_xml'lang_bn
	    translate "bo" = Just Subject_xml'lang_bo
	    translate "br" = Just Subject_xml'lang_br
	    translate "ca" = Just Subject_xml'lang_ca
	    translate "co" = Just Subject_xml'lang_co
	    translate "cs" = Just Subject_xml'lang_cs
	    translate "cy" = Just Subject_xml'lang_cy
	    translate "da" = Just Subject_xml'lang_da
	    translate "de" = Just Subject_xml'lang_de
	    translate "dz" = Just Subject_xml'lang_dz
	    translate "el" = Just Subject_xml'lang_el
	    translate "en" = Just Subject_xml'lang_en
	    translate "eo" = Just Subject_xml'lang_eo
	    translate "es" = Just Subject_xml'lang_es
	    translate "et" = Just Subject_xml'lang_et
	    translate "eu" = Just Subject_xml'lang_eu
	    translate "fa" = Just Subject_xml'lang_fa
	    translate "fi" = Just Subject_xml'lang_fi
	    translate "fj" = Just Subject_xml'lang_fj
	    translate "fo" = Just Subject_xml'lang_fo
	    translate "fr" = Just Subject_xml'lang_fr
	    translate "fy" = Just Subject_xml'lang_fy
	    translate "ga" = Just Subject_xml'lang_ga
	    translate "gd" = Just Subject_xml'lang_gd
	    translate "gl" = Just Subject_xml'lang_gl
	    translate "gn" = Just Subject_xml'lang_gn
	    translate "gu" = Just Subject_xml'lang_gu
	    translate "ha" = Just Subject_xml'lang_ha
	    translate "he" = Just Subject_xml'lang_he
	    translate "hi" = Just Subject_xml'lang_hi
	    translate "hr" = Just Subject_xml'lang_hr
	    translate "hu" = Just Subject_xml'lang_hu
	    translate "hy" = Just Subject_xml'lang_hy
	    translate "ia" = Just Subject_xml'lang_ia
	    translate "ie" = Just Subject_xml'lang_ie
	    translate "ik" = Just Subject_xml'lang_ik
	    translate "id" = Just Subject_xml'lang_id
	    translate "is" = Just Subject_xml'lang_is
	    translate "it" = Just Subject_xml'lang_it
	    translate "iu" = Just Subject_xml'lang_iu
	    translate "ja" = Just Subject_xml'lang_ja
	    translate "jv" = Just Subject_xml'lang_jv
	    translate "ka" = Just Subject_xml'lang_ka
	    translate "kk" = Just Subject_xml'lang_kk
	    translate "kl" = Just Subject_xml'lang_kl
	    translate "km" = Just Subject_xml'lang_km
	    translate "kn" = Just Subject_xml'lang_kn
	    translate "ko" = Just Subject_xml'lang_ko
	    translate "ks" = Just Subject_xml'lang_ks
	    translate "ku" = Just Subject_xml'lang_ku
	    translate "ky" = Just Subject_xml'lang_ky
	    translate "la" = Just Subject_xml'lang_la
	    translate "ln" = Just Subject_xml'lang_ln
	    translate "lo" = Just Subject_xml'lang_lo
	    translate "lt" = Just Subject_xml'lang_lt
	    translate "lv" = Just Subject_xml'lang_lv
	    translate "mg" = Just Subject_xml'lang_mg
	    translate "mi" = Just Subject_xml'lang_mi
	    translate "mk" = Just Subject_xml'lang_mk
	    translate "ml" = Just Subject_xml'lang_ml
	    translate "mn" = Just Subject_xml'lang_mn
	    translate "mo" = Just Subject_xml'lang_mo
	    translate "mr" = Just Subject_xml'lang_mr
	    translate "ms" = Just Subject_xml'lang_ms
	    translate "mt" = Just Subject_xml'lang_mt
	    translate "my" = Just Subject_xml'lang_my
	    translate "na" = Just Subject_xml'lang_na
	    translate "ne" = Just Subject_xml'lang_ne
	    translate "nl" = Just Subject_xml'lang_nl
	    translate "no" = Just Subject_xml'lang_no
	    translate "oc" = Just Subject_xml'lang_oc
	    translate "om" = Just Subject_xml'lang_om
	    translate "or" = Just Subject_xml'lang_or
	    translate "pa" = Just Subject_xml'lang_pa
	    translate "pl" = Just Subject_xml'lang_pl
	    translate "ps" = Just Subject_xml'lang_ps
	    translate "pt" = Just Subject_xml'lang_pt
	    translate "qu" = Just Subject_xml'lang_qu
	    translate "rm" = Just Subject_xml'lang_rm
	    translate "rn" = Just Subject_xml'lang_rn
	    translate "ro" = Just Subject_xml'lang_ro
	    translate "ru" = Just Subject_xml'lang_ru
	    translate "rw" = Just Subject_xml'lang_rw
	    translate "sa" = Just Subject_xml'lang_sa
	    translate "sd" = Just Subject_xml'lang_sd
	    translate "sg" = Just Subject_xml'lang_sg
	    translate "sh" = Just Subject_xml'lang_sh
	    translate "si" = Just Subject_xml'lang_si
	    translate "sk" = Just Subject_xml'lang_sk
	    translate "sl" = Just Subject_xml'lang_sl
	    translate "sm" = Just Subject_xml'lang_sm
	    translate "sn" = Just Subject_xml'lang_sn
	    translate "so" = Just Subject_xml'lang_so
	    translate "sq" = Just Subject_xml'lang_sq
	    translate "sr" = Just Subject_xml'lang_sr
	    translate "ss" = Just Subject_xml'lang_ss
	    translate "st" = Just Subject_xml'lang_st
	    translate "su" = Just Subject_xml'lang_su
	    translate "sv" = Just Subject_xml'lang_sv
	    translate "sw" = Just Subject_xml'lang_sw
	    translate "ta" = Just Subject_xml'lang_ta
	    translate "te" = Just Subject_xml'lang_te
	    translate "tg" = Just Subject_xml'lang_tg
	    translate "th" = Just Subject_xml'lang_th
	    translate "ti" = Just Subject_xml'lang_ti
	    translate "tk" = Just Subject_xml'lang_tk
	    translate "tl" = Just Subject_xml'lang_tl
	    translate "tn" = Just Subject_xml'lang_tn
	    translate "to" = Just Subject_xml'lang_to
	    translate "tr" = Just Subject_xml'lang_tr
	    translate "ts" = Just Subject_xml'lang_ts
	    translate "tt" = Just Subject_xml'lang_tt
	    translate "tw" = Just Subject_xml'lang_tw
	    translate "ug" = Just Subject_xml'lang_ug
	    translate "uk" = Just Subject_xml'lang_uk
	    translate "ur" = Just Subject_xml'lang_ur
	    translate "uz" = Just Subject_xml'lang_uz
	    translate "vi" = Just Subject_xml'lang_vi
	    translate "vo" = Just Subject_xml'lang_vo
	    translate "wo" = Just Subject_xml'lang_wo
	    translate "xh" = Just Subject_xml'lang_xh
	    translate "yi" = Just Subject_xml'lang_yi
	    translate "yo" = Just Subject_xml'lang_yo
	    translate "za" = Just Subject_xml'lang_za
	    translate "zh" = Just Subject_xml'lang_zh
	    translate "zu" = Just Subject_xml'lang_zu
	    translate _ = Nothing
    toAttrFrTyp n Subject_xml'lang_aa = Just (n, str2attr "aa")
    toAttrFrTyp n Subject_xml'lang_ab = Just (n, str2attr "ab")
    toAttrFrTyp n Subject_xml'lang_af = Just (n, str2attr "af")
    toAttrFrTyp n Subject_xml'lang_am = Just (n, str2attr "am")
    toAttrFrTyp n Subject_xml'lang_ar = Just (n, str2attr "ar")
    toAttrFrTyp n Subject_xml'lang_as = Just (n, str2attr "as")
    toAttrFrTyp n Subject_xml'lang_ay = Just (n, str2attr "ay")
    toAttrFrTyp n Subject_xml'lang_az = Just (n, str2attr "az")
    toAttrFrTyp n Subject_xml'lang_ba = Just (n, str2attr "ba")
    toAttrFrTyp n Subject_xml'lang_be = Just (n, str2attr "be")
    toAttrFrTyp n Subject_xml'lang_bg = Just (n, str2attr "bg")
    toAttrFrTyp n Subject_xml'lang_bh = Just (n, str2attr "bh")
    toAttrFrTyp n Subject_xml'lang_bi = Just (n, str2attr "bi")
    toAttrFrTyp n Subject_xml'lang_bn = Just (n, str2attr "bn")
    toAttrFrTyp n Subject_xml'lang_bo = Just (n, str2attr "bo")
    toAttrFrTyp n Subject_xml'lang_br = Just (n, str2attr "br")
    toAttrFrTyp n Subject_xml'lang_ca = Just (n, str2attr "ca")
    toAttrFrTyp n Subject_xml'lang_co = Just (n, str2attr "co")
    toAttrFrTyp n Subject_xml'lang_cs = Just (n, str2attr "cs")
    toAttrFrTyp n Subject_xml'lang_cy = Just (n, str2attr "cy")
    toAttrFrTyp n Subject_xml'lang_da = Just (n, str2attr "da")
    toAttrFrTyp n Subject_xml'lang_de = Just (n, str2attr "de")
    toAttrFrTyp n Subject_xml'lang_dz = Just (n, str2attr "dz")
    toAttrFrTyp n Subject_xml'lang_el = Just (n, str2attr "el")
    toAttrFrTyp n Subject_xml'lang_en = Just (n, str2attr "en")
    toAttrFrTyp n Subject_xml'lang_eo = Just (n, str2attr "eo")
    toAttrFrTyp n Subject_xml'lang_es = Just (n, str2attr "es")
    toAttrFrTyp n Subject_xml'lang_et = Just (n, str2attr "et")
    toAttrFrTyp n Subject_xml'lang_eu = Just (n, str2attr "eu")
    toAttrFrTyp n Subject_xml'lang_fa = Just (n, str2attr "fa")
    toAttrFrTyp n Subject_xml'lang_fi = Just (n, str2attr "fi")
    toAttrFrTyp n Subject_xml'lang_fj = Just (n, str2attr "fj")
    toAttrFrTyp n Subject_xml'lang_fo = Just (n, str2attr "fo")
    toAttrFrTyp n Subject_xml'lang_fr = Just (n, str2attr "fr")
    toAttrFrTyp n Subject_xml'lang_fy = Just (n, str2attr "fy")
    toAttrFrTyp n Subject_xml'lang_ga = Just (n, str2attr "ga")
    toAttrFrTyp n Subject_xml'lang_gd = Just (n, str2attr "gd")
    toAttrFrTyp n Subject_xml'lang_gl = Just (n, str2attr "gl")
    toAttrFrTyp n Subject_xml'lang_gn = Just (n, str2attr "gn")
    toAttrFrTyp n Subject_xml'lang_gu = Just (n, str2attr "gu")
    toAttrFrTyp n Subject_xml'lang_ha = Just (n, str2attr "ha")
    toAttrFrTyp n Subject_xml'lang_he = Just (n, str2attr "he")
    toAttrFrTyp n Subject_xml'lang_hi = Just (n, str2attr "hi")
    toAttrFrTyp n Subject_xml'lang_hr = Just (n, str2attr "hr")
    toAttrFrTyp n Subject_xml'lang_hu = Just (n, str2attr "hu")
    toAttrFrTyp n Subject_xml'lang_hy = Just (n, str2attr "hy")
    toAttrFrTyp n Subject_xml'lang_ia = Just (n, str2attr "ia")
    toAttrFrTyp n Subject_xml'lang_ie = Just (n, str2attr "ie")
    toAttrFrTyp n Subject_xml'lang_ik = Just (n, str2attr "ik")
    toAttrFrTyp n Subject_xml'lang_id = Just (n, str2attr "id")
    toAttrFrTyp n Subject_xml'lang_is = Just (n, str2attr "is")
    toAttrFrTyp n Subject_xml'lang_it = Just (n, str2attr "it")
    toAttrFrTyp n Subject_xml'lang_iu = Just (n, str2attr "iu")
    toAttrFrTyp n Subject_xml'lang_ja = Just (n, str2attr "ja")
    toAttrFrTyp n Subject_xml'lang_jv = Just (n, str2attr "jv")
    toAttrFrTyp n Subject_xml'lang_ka = Just (n, str2attr "ka")
    toAttrFrTyp n Subject_xml'lang_kk = Just (n, str2attr "kk")
    toAttrFrTyp n Subject_xml'lang_kl = Just (n, str2attr "kl")
    toAttrFrTyp n Subject_xml'lang_km = Just (n, str2attr "km")
    toAttrFrTyp n Subject_xml'lang_kn = Just (n, str2attr "kn")
    toAttrFrTyp n Subject_xml'lang_ko = Just (n, str2attr "ko")
    toAttrFrTyp n Subject_xml'lang_ks = Just (n, str2attr "ks")
    toAttrFrTyp n Subject_xml'lang_ku = Just (n, str2attr "ku")
    toAttrFrTyp n Subject_xml'lang_ky = Just (n, str2attr "ky")
    toAttrFrTyp n Subject_xml'lang_la = Just (n, str2attr "la")
    toAttrFrTyp n Subject_xml'lang_ln = Just (n, str2attr "ln")
    toAttrFrTyp n Subject_xml'lang_lo = Just (n, str2attr "lo")
    toAttrFrTyp n Subject_xml'lang_lt = Just (n, str2attr "lt")
    toAttrFrTyp n Subject_xml'lang_lv = Just (n, str2attr "lv")
    toAttrFrTyp n Subject_xml'lang_mg = Just (n, str2attr "mg")
    toAttrFrTyp n Subject_xml'lang_mi = Just (n, str2attr "mi")
    toAttrFrTyp n Subject_xml'lang_mk = Just (n, str2attr "mk")
    toAttrFrTyp n Subject_xml'lang_ml = Just (n, str2attr "ml")
    toAttrFrTyp n Subject_xml'lang_mn = Just (n, str2attr "mn")
    toAttrFrTyp n Subject_xml'lang_mo = Just (n, str2attr "mo")
    toAttrFrTyp n Subject_xml'lang_mr = Just (n, str2attr "mr")
    toAttrFrTyp n Subject_xml'lang_ms = Just (n, str2attr "ms")
    toAttrFrTyp n Subject_xml'lang_mt = Just (n, str2attr "mt")
    toAttrFrTyp n Subject_xml'lang_my = Just (n, str2attr "my")
    toAttrFrTyp n Subject_xml'lang_na = Just (n, str2attr "na")
    toAttrFrTyp n Subject_xml'lang_ne = Just (n, str2attr "ne")
    toAttrFrTyp n Subject_xml'lang_nl = Just (n, str2attr "nl")
    toAttrFrTyp n Subject_xml'lang_no = Just (n, str2attr "no")
    toAttrFrTyp n Subject_xml'lang_oc = Just (n, str2attr "oc")
    toAttrFrTyp n Subject_xml'lang_om = Just (n, str2attr "om")
    toAttrFrTyp n Subject_xml'lang_or = Just (n, str2attr "or")
    toAttrFrTyp n Subject_xml'lang_pa = Just (n, str2attr "pa")
    toAttrFrTyp n Subject_xml'lang_pl = Just (n, str2attr "pl")
    toAttrFrTyp n Subject_xml'lang_ps = Just (n, str2attr "ps")
    toAttrFrTyp n Subject_xml'lang_pt = Just (n, str2attr "pt")
    toAttrFrTyp n Subject_xml'lang_qu = Just (n, str2attr "qu")
    toAttrFrTyp n Subject_xml'lang_rm = Just (n, str2attr "rm")
    toAttrFrTyp n Subject_xml'lang_rn = Just (n, str2attr "rn")
    toAttrFrTyp n Subject_xml'lang_ro = Just (n, str2attr "ro")
    toAttrFrTyp n Subject_xml'lang_ru = Just (n, str2attr "ru")
    toAttrFrTyp n Subject_xml'lang_rw = Just (n, str2attr "rw")
    toAttrFrTyp n Subject_xml'lang_sa = Just (n, str2attr "sa")
    toAttrFrTyp n Subject_xml'lang_sd = Just (n, str2attr "sd")
    toAttrFrTyp n Subject_xml'lang_sg = Just (n, str2attr "sg")
    toAttrFrTyp n Subject_xml'lang_sh = Just (n, str2attr "sh")
    toAttrFrTyp n Subject_xml'lang_si = Just (n, str2attr "si")
    toAttrFrTyp n Subject_xml'lang_sk = Just (n, str2attr "sk")
    toAttrFrTyp n Subject_xml'lang_sl = Just (n, str2attr "sl")
    toAttrFrTyp n Subject_xml'lang_sm = Just (n, str2attr "sm")
    toAttrFrTyp n Subject_xml'lang_sn = Just (n, str2attr "sn")
    toAttrFrTyp n Subject_xml'lang_so = Just (n, str2attr "so")
    toAttrFrTyp n Subject_xml'lang_sq = Just (n, str2attr "sq")
    toAttrFrTyp n Subject_xml'lang_sr = Just (n, str2attr "sr")
    toAttrFrTyp n Subject_xml'lang_ss = Just (n, str2attr "ss")
    toAttrFrTyp n Subject_xml'lang_st = Just (n, str2attr "st")
    toAttrFrTyp n Subject_xml'lang_su = Just (n, str2attr "su")
    toAttrFrTyp n Subject_xml'lang_sv = Just (n, str2attr "sv")
    toAttrFrTyp n Subject_xml'lang_sw = Just (n, str2attr "sw")
    toAttrFrTyp n Subject_xml'lang_ta = Just (n, str2attr "ta")
    toAttrFrTyp n Subject_xml'lang_te = Just (n, str2attr "te")
    toAttrFrTyp n Subject_xml'lang_tg = Just (n, str2attr "tg")
    toAttrFrTyp n Subject_xml'lang_th = Just (n, str2attr "th")
    toAttrFrTyp n Subject_xml'lang_ti = Just (n, str2attr "ti")
    toAttrFrTyp n Subject_xml'lang_tk = Just (n, str2attr "tk")
    toAttrFrTyp n Subject_xml'lang_tl = Just (n, str2attr "tl")
    toAttrFrTyp n Subject_xml'lang_tn = Just (n, str2attr "tn")
    toAttrFrTyp n Subject_xml'lang_to = Just (n, str2attr "to")
    toAttrFrTyp n Subject_xml'lang_tr = Just (n, str2attr "tr")
    toAttrFrTyp n Subject_xml'lang_ts = Just (n, str2attr "ts")
    toAttrFrTyp n Subject_xml'lang_tt = Just (n, str2attr "tt")
    toAttrFrTyp n Subject_xml'lang_tw = Just (n, str2attr "tw")
    toAttrFrTyp n Subject_xml'lang_ug = Just (n, str2attr "ug")
    toAttrFrTyp n Subject_xml'lang_uk = Just (n, str2attr "uk")
    toAttrFrTyp n Subject_xml'lang_ur = Just (n, str2attr "ur")
    toAttrFrTyp n Subject_xml'lang_uz = Just (n, str2attr "uz")
    toAttrFrTyp n Subject_xml'lang_vi = Just (n, str2attr "vi")
    toAttrFrTyp n Subject_xml'lang_vo = Just (n, str2attr "vo")
    toAttrFrTyp n Subject_xml'lang_wo = Just (n, str2attr "wo")
    toAttrFrTyp n Subject_xml'lang_xh = Just (n, str2attr "xh")
    toAttrFrTyp n Subject_xml'lang_yi = Just (n, str2attr "yi")
    toAttrFrTyp n Subject_xml'lang_yo = Just (n, str2attr "yo")
    toAttrFrTyp n Subject_xml'lang_za = Just (n, str2attr "za")
    toAttrFrTyp n Subject_xml'lang_zh = Just (n, str2attr "zh")
    toAttrFrTyp n Subject_xml'lang_zu = Just (n, str2attr "zu")
instance XmlContent Description where
    fromElem (CElem (Elem "Description" as c0):rest) =
	(\(a,ca)->
	   (Just (Description (fromAttrs as) a), rest))
	(many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Description as a) =
	[CElem (Elem "Description" (toAttrs as) (concatMap toElem a))]
instance XmlAttributes Description_Attrs where
    fromAttrs as =
	Description_Attrs
	  { descriptionXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  , descriptionXml'lang = defaultA fromAttrToTyp Description_xml'lang_en "xml:lang" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (descriptionXmlns v)
	, defaultToAttr toAttrFrTyp "xml:lang" (descriptionXml'lang v)
	]
instance XmlContent Description_ where
    fromElem c0 =
	case (fromText c0) of
	(Just a,rest) -> (Just (Description_Str a), rest)
	(_,_) ->
		case (fromElem c0) of
		(Just a,rest) -> (Just (Description_OMOBJ a), rest)
		(_,_) ->
			case (fromElem c0) of
			(Just a,rest) -> (Just (Description_Omlet a), rest)
			(_,_) ->
				case (fromElem c0) of
				(Just a,rest) -> (Just (Description_With a), rest)
				(_,_) ->
					case (fromElem c0) of
					(Just a,rest) -> (Just (Description_Ref a), rest)
					(_,_) ->
						case (fromElem c0) of
						(Just a,rest) -> (Just (Description_Ignore a), rest)
						(_,_) ->
						    (Nothing, c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Description_Str a) = toText a
    toElem (Description_OMOBJ a) = toElem a
    toElem (Description_Omlet a) = toElem a
    toElem (Description_With a) = toElem a
    toElem (Description_Ref a) = toElem a
    toElem (Description_Ignore a) = toElem a
instance XmlAttrType Description_xml'lang where
    fromAttrToTyp n (n',v)
	| n==n'     = translate (attr2str v)
	| otherwise = Nothing
      where translate "aa" = Just Description_xml'lang_aa
	    translate "ab" = Just Description_xml'lang_ab
	    translate "af" = Just Description_xml'lang_af
	    translate "am" = Just Description_xml'lang_am
	    translate "ar" = Just Description_xml'lang_ar
	    translate "as" = Just Description_xml'lang_as
	    translate "ay" = Just Description_xml'lang_ay
	    translate "az" = Just Description_xml'lang_az
	    translate "ba" = Just Description_xml'lang_ba
	    translate "be" = Just Description_xml'lang_be
	    translate "bg" = Just Description_xml'lang_bg
	    translate "bh" = Just Description_xml'lang_bh
	    translate "bi" = Just Description_xml'lang_bi
	    translate "bn" = Just Description_xml'lang_bn
	    translate "bo" = Just Description_xml'lang_bo
	    translate "br" = Just Description_xml'lang_br
	    translate "ca" = Just Description_xml'lang_ca
	    translate "co" = Just Description_xml'lang_co
	    translate "cs" = Just Description_xml'lang_cs
	    translate "cy" = Just Description_xml'lang_cy
	    translate "da" = Just Description_xml'lang_da
	    translate "de" = Just Description_xml'lang_de
	    translate "dz" = Just Description_xml'lang_dz
	    translate "el" = Just Description_xml'lang_el
	    translate "en" = Just Description_xml'lang_en
	    translate "eo" = Just Description_xml'lang_eo
	    translate "es" = Just Description_xml'lang_es
	    translate "et" = Just Description_xml'lang_et
	    translate "eu" = Just Description_xml'lang_eu
	    translate "fa" = Just Description_xml'lang_fa
	    translate "fi" = Just Description_xml'lang_fi
	    translate "fj" = Just Description_xml'lang_fj
	    translate "fo" = Just Description_xml'lang_fo
	    translate "fr" = Just Description_xml'lang_fr
	    translate "fy" = Just Description_xml'lang_fy
	    translate "ga" = Just Description_xml'lang_ga
	    translate "gd" = Just Description_xml'lang_gd
	    translate "gl" = Just Description_xml'lang_gl
	    translate "gn" = Just Description_xml'lang_gn
	    translate "gu" = Just Description_xml'lang_gu
	    translate "ha" = Just Description_xml'lang_ha
	    translate "he" = Just Description_xml'lang_he
	    translate "hi" = Just Description_xml'lang_hi
	    translate "hr" = Just Description_xml'lang_hr
	    translate "hu" = Just Description_xml'lang_hu
	    translate "hy" = Just Description_xml'lang_hy
	    translate "ia" = Just Description_xml'lang_ia
	    translate "ie" = Just Description_xml'lang_ie
	    translate "ik" = Just Description_xml'lang_ik
	    translate "id" = Just Description_xml'lang_id
	    translate "is" = Just Description_xml'lang_is
	    translate "it" = Just Description_xml'lang_it
	    translate "iu" = Just Description_xml'lang_iu
	    translate "ja" = Just Description_xml'lang_ja
	    translate "jv" = Just Description_xml'lang_jv
	    translate "ka" = Just Description_xml'lang_ka
	    translate "kk" = Just Description_xml'lang_kk
	    translate "kl" = Just Description_xml'lang_kl
	    translate "km" = Just Description_xml'lang_km
	    translate "kn" = Just Description_xml'lang_kn
	    translate "ko" = Just Description_xml'lang_ko
	    translate "ks" = Just Description_xml'lang_ks
	    translate "ku" = Just Description_xml'lang_ku
	    translate "ky" = Just Description_xml'lang_ky
	    translate "la" = Just Description_xml'lang_la
	    translate "ln" = Just Description_xml'lang_ln
	    translate "lo" = Just Description_xml'lang_lo
	    translate "lt" = Just Description_xml'lang_lt
	    translate "lv" = Just Description_xml'lang_lv
	    translate "mg" = Just Description_xml'lang_mg
	    translate "mi" = Just Description_xml'lang_mi
	    translate "mk" = Just Description_xml'lang_mk
	    translate "ml" = Just Description_xml'lang_ml
	    translate "mn" = Just Description_xml'lang_mn
	    translate "mo" = Just Description_xml'lang_mo
	    translate "mr" = Just Description_xml'lang_mr
	    translate "ms" = Just Description_xml'lang_ms
	    translate "mt" = Just Description_xml'lang_mt
	    translate "my" = Just Description_xml'lang_my
	    translate "na" = Just Description_xml'lang_na
	    translate "ne" = Just Description_xml'lang_ne
	    translate "nl" = Just Description_xml'lang_nl
	    translate "no" = Just Description_xml'lang_no
	    translate "oc" = Just Description_xml'lang_oc
	    translate "om" = Just Description_xml'lang_om
	    translate "or" = Just Description_xml'lang_or
	    translate "pa" = Just Description_xml'lang_pa
	    translate "pl" = Just Description_xml'lang_pl
	    translate "ps" = Just Description_xml'lang_ps
	    translate "pt" = Just Description_xml'lang_pt
	    translate "qu" = Just Description_xml'lang_qu
	    translate "rm" = Just Description_xml'lang_rm
	    translate "rn" = Just Description_xml'lang_rn
	    translate "ro" = Just Description_xml'lang_ro
	    translate "ru" = Just Description_xml'lang_ru
	    translate "rw" = Just Description_xml'lang_rw
	    translate "sa" = Just Description_xml'lang_sa
	    translate "sd" = Just Description_xml'lang_sd
	    translate "sg" = Just Description_xml'lang_sg
	    translate "sh" = Just Description_xml'lang_sh
	    translate "si" = Just Description_xml'lang_si
	    translate "sk" = Just Description_xml'lang_sk
	    translate "sl" = Just Description_xml'lang_sl
	    translate "sm" = Just Description_xml'lang_sm
	    translate "sn" = Just Description_xml'lang_sn
	    translate "so" = Just Description_xml'lang_so
	    translate "sq" = Just Description_xml'lang_sq
	    translate "sr" = Just Description_xml'lang_sr
	    translate "ss" = Just Description_xml'lang_ss
	    translate "st" = Just Description_xml'lang_st
	    translate "su" = Just Description_xml'lang_su
	    translate "sv" = Just Description_xml'lang_sv
	    translate "sw" = Just Description_xml'lang_sw
	    translate "ta" = Just Description_xml'lang_ta
	    translate "te" = Just Description_xml'lang_te
	    translate "tg" = Just Description_xml'lang_tg
	    translate "th" = Just Description_xml'lang_th
	    translate "ti" = Just Description_xml'lang_ti
	    translate "tk" = Just Description_xml'lang_tk
	    translate "tl" = Just Description_xml'lang_tl
	    translate "tn" = Just Description_xml'lang_tn
	    translate "to" = Just Description_xml'lang_to
	    translate "tr" = Just Description_xml'lang_tr
	    translate "ts" = Just Description_xml'lang_ts
	    translate "tt" = Just Description_xml'lang_tt
	    translate "tw" = Just Description_xml'lang_tw
	    translate "ug" = Just Description_xml'lang_ug
	    translate "uk" = Just Description_xml'lang_uk
	    translate "ur" = Just Description_xml'lang_ur
	    translate "uz" = Just Description_xml'lang_uz
	    translate "vi" = Just Description_xml'lang_vi
	    translate "vo" = Just Description_xml'lang_vo
	    translate "wo" = Just Description_xml'lang_wo
	    translate "xh" = Just Description_xml'lang_xh
	    translate "yi" = Just Description_xml'lang_yi
	    translate "yo" = Just Description_xml'lang_yo
	    translate "za" = Just Description_xml'lang_za
	    translate "zh" = Just Description_xml'lang_zh
	    translate "zu" = Just Description_xml'lang_zu
	    translate _ = Nothing
    toAttrFrTyp n Description_xml'lang_aa = Just (n, str2attr "aa")
    toAttrFrTyp n Description_xml'lang_ab = Just (n, str2attr "ab")
    toAttrFrTyp n Description_xml'lang_af = Just (n, str2attr "af")
    toAttrFrTyp n Description_xml'lang_am = Just (n, str2attr "am")
    toAttrFrTyp n Description_xml'lang_ar = Just (n, str2attr "ar")
    toAttrFrTyp n Description_xml'lang_as = Just (n, str2attr "as")
    toAttrFrTyp n Description_xml'lang_ay = Just (n, str2attr "ay")
    toAttrFrTyp n Description_xml'lang_az = Just (n, str2attr "az")
    toAttrFrTyp n Description_xml'lang_ba = Just (n, str2attr "ba")
    toAttrFrTyp n Description_xml'lang_be = Just (n, str2attr "be")
    toAttrFrTyp n Description_xml'lang_bg = Just (n, str2attr "bg")
    toAttrFrTyp n Description_xml'lang_bh = Just (n, str2attr "bh")
    toAttrFrTyp n Description_xml'lang_bi = Just (n, str2attr "bi")
    toAttrFrTyp n Description_xml'lang_bn = Just (n, str2attr "bn")
    toAttrFrTyp n Description_xml'lang_bo = Just (n, str2attr "bo")
    toAttrFrTyp n Description_xml'lang_br = Just (n, str2attr "br")
    toAttrFrTyp n Description_xml'lang_ca = Just (n, str2attr "ca")
    toAttrFrTyp n Description_xml'lang_co = Just (n, str2attr "co")
    toAttrFrTyp n Description_xml'lang_cs = Just (n, str2attr "cs")
    toAttrFrTyp n Description_xml'lang_cy = Just (n, str2attr "cy")
    toAttrFrTyp n Description_xml'lang_da = Just (n, str2attr "da")
    toAttrFrTyp n Description_xml'lang_de = Just (n, str2attr "de")
    toAttrFrTyp n Description_xml'lang_dz = Just (n, str2attr "dz")
    toAttrFrTyp n Description_xml'lang_el = Just (n, str2attr "el")
    toAttrFrTyp n Description_xml'lang_en = Just (n, str2attr "en")
    toAttrFrTyp n Description_xml'lang_eo = Just (n, str2attr "eo")
    toAttrFrTyp n Description_xml'lang_es = Just (n, str2attr "es")
    toAttrFrTyp n Description_xml'lang_et = Just (n, str2attr "et")
    toAttrFrTyp n Description_xml'lang_eu = Just (n, str2attr "eu")
    toAttrFrTyp n Description_xml'lang_fa = Just (n, str2attr "fa")
    toAttrFrTyp n Description_xml'lang_fi = Just (n, str2attr "fi")
    toAttrFrTyp n Description_xml'lang_fj = Just (n, str2attr "fj")
    toAttrFrTyp n Description_xml'lang_fo = Just (n, str2attr "fo")
    toAttrFrTyp n Description_xml'lang_fr = Just (n, str2attr "fr")
    toAttrFrTyp n Description_xml'lang_fy = Just (n, str2attr "fy")
    toAttrFrTyp n Description_xml'lang_ga = Just (n, str2attr "ga")
    toAttrFrTyp n Description_xml'lang_gd = Just (n, str2attr "gd")
    toAttrFrTyp n Description_xml'lang_gl = Just (n, str2attr "gl")
    toAttrFrTyp n Description_xml'lang_gn = Just (n, str2attr "gn")
    toAttrFrTyp n Description_xml'lang_gu = Just (n, str2attr "gu")
    toAttrFrTyp n Description_xml'lang_ha = Just (n, str2attr "ha")
    toAttrFrTyp n Description_xml'lang_he = Just (n, str2attr "he")
    toAttrFrTyp n Description_xml'lang_hi = Just (n, str2attr "hi")
    toAttrFrTyp n Description_xml'lang_hr = Just (n, str2attr "hr")
    toAttrFrTyp n Description_xml'lang_hu = Just (n, str2attr "hu")
    toAttrFrTyp n Description_xml'lang_hy = Just (n, str2attr "hy")
    toAttrFrTyp n Description_xml'lang_ia = Just (n, str2attr "ia")
    toAttrFrTyp n Description_xml'lang_ie = Just (n, str2attr "ie")
    toAttrFrTyp n Description_xml'lang_ik = Just (n, str2attr "ik")
    toAttrFrTyp n Description_xml'lang_id = Just (n, str2attr "id")
    toAttrFrTyp n Description_xml'lang_is = Just (n, str2attr "is")
    toAttrFrTyp n Description_xml'lang_it = Just (n, str2attr "it")
    toAttrFrTyp n Description_xml'lang_iu = Just (n, str2attr "iu")
    toAttrFrTyp n Description_xml'lang_ja = Just (n, str2attr "ja")
    toAttrFrTyp n Description_xml'lang_jv = Just (n, str2attr "jv")
    toAttrFrTyp n Description_xml'lang_ka = Just (n, str2attr "ka")
    toAttrFrTyp n Description_xml'lang_kk = Just (n, str2attr "kk")
    toAttrFrTyp n Description_xml'lang_kl = Just (n, str2attr "kl")
    toAttrFrTyp n Description_xml'lang_km = Just (n, str2attr "km")
    toAttrFrTyp n Description_xml'lang_kn = Just (n, str2attr "kn")
    toAttrFrTyp n Description_xml'lang_ko = Just (n, str2attr "ko")
    toAttrFrTyp n Description_xml'lang_ks = Just (n, str2attr "ks")
    toAttrFrTyp n Description_xml'lang_ku = Just (n, str2attr "ku")
    toAttrFrTyp n Description_xml'lang_ky = Just (n, str2attr "ky")
    toAttrFrTyp n Description_xml'lang_la = Just (n, str2attr "la")
    toAttrFrTyp n Description_xml'lang_ln = Just (n, str2attr "ln")
    toAttrFrTyp n Description_xml'lang_lo = Just (n, str2attr "lo")
    toAttrFrTyp n Description_xml'lang_lt = Just (n, str2attr "lt")
    toAttrFrTyp n Description_xml'lang_lv = Just (n, str2attr "lv")
    toAttrFrTyp n Description_xml'lang_mg = Just (n, str2attr "mg")
    toAttrFrTyp n Description_xml'lang_mi = Just (n, str2attr "mi")
    toAttrFrTyp n Description_xml'lang_mk = Just (n, str2attr "mk")
    toAttrFrTyp n Description_xml'lang_ml = Just (n, str2attr "ml")
    toAttrFrTyp n Description_xml'lang_mn = Just (n, str2attr "mn")
    toAttrFrTyp n Description_xml'lang_mo = Just (n, str2attr "mo")
    toAttrFrTyp n Description_xml'lang_mr = Just (n, str2attr "mr")
    toAttrFrTyp n Description_xml'lang_ms = Just (n, str2attr "ms")
    toAttrFrTyp n Description_xml'lang_mt = Just (n, str2attr "mt")
    toAttrFrTyp n Description_xml'lang_my = Just (n, str2attr "my")
    toAttrFrTyp n Description_xml'lang_na = Just (n, str2attr "na")
    toAttrFrTyp n Description_xml'lang_ne = Just (n, str2attr "ne")
    toAttrFrTyp n Description_xml'lang_nl = Just (n, str2attr "nl")
    toAttrFrTyp n Description_xml'lang_no = Just (n, str2attr "no")
    toAttrFrTyp n Description_xml'lang_oc = Just (n, str2attr "oc")
    toAttrFrTyp n Description_xml'lang_om = Just (n, str2attr "om")
    toAttrFrTyp n Description_xml'lang_or = Just (n, str2attr "or")
    toAttrFrTyp n Description_xml'lang_pa = Just (n, str2attr "pa")
    toAttrFrTyp n Description_xml'lang_pl = Just (n, str2attr "pl")
    toAttrFrTyp n Description_xml'lang_ps = Just (n, str2attr "ps")
    toAttrFrTyp n Description_xml'lang_pt = Just (n, str2attr "pt")
    toAttrFrTyp n Description_xml'lang_qu = Just (n, str2attr "qu")
    toAttrFrTyp n Description_xml'lang_rm = Just (n, str2attr "rm")
    toAttrFrTyp n Description_xml'lang_rn = Just (n, str2attr "rn")
    toAttrFrTyp n Description_xml'lang_ro = Just (n, str2attr "ro")
    toAttrFrTyp n Description_xml'lang_ru = Just (n, str2attr "ru")
    toAttrFrTyp n Description_xml'lang_rw = Just (n, str2attr "rw")
    toAttrFrTyp n Description_xml'lang_sa = Just (n, str2attr "sa")
    toAttrFrTyp n Description_xml'lang_sd = Just (n, str2attr "sd")
    toAttrFrTyp n Description_xml'lang_sg = Just (n, str2attr "sg")
    toAttrFrTyp n Description_xml'lang_sh = Just (n, str2attr "sh")
    toAttrFrTyp n Description_xml'lang_si = Just (n, str2attr "si")
    toAttrFrTyp n Description_xml'lang_sk = Just (n, str2attr "sk")
    toAttrFrTyp n Description_xml'lang_sl = Just (n, str2attr "sl")
    toAttrFrTyp n Description_xml'lang_sm = Just (n, str2attr "sm")
    toAttrFrTyp n Description_xml'lang_sn = Just (n, str2attr "sn")
    toAttrFrTyp n Description_xml'lang_so = Just (n, str2attr "so")
    toAttrFrTyp n Description_xml'lang_sq = Just (n, str2attr "sq")
    toAttrFrTyp n Description_xml'lang_sr = Just (n, str2attr "sr")
    toAttrFrTyp n Description_xml'lang_ss = Just (n, str2attr "ss")
    toAttrFrTyp n Description_xml'lang_st = Just (n, str2attr "st")
    toAttrFrTyp n Description_xml'lang_su = Just (n, str2attr "su")
    toAttrFrTyp n Description_xml'lang_sv = Just (n, str2attr "sv")
    toAttrFrTyp n Description_xml'lang_sw = Just (n, str2attr "sw")
    toAttrFrTyp n Description_xml'lang_ta = Just (n, str2attr "ta")
    toAttrFrTyp n Description_xml'lang_te = Just (n, str2attr "te")
    toAttrFrTyp n Description_xml'lang_tg = Just (n, str2attr "tg")
    toAttrFrTyp n Description_xml'lang_th = Just (n, str2attr "th")
    toAttrFrTyp n Description_xml'lang_ti = Just (n, str2attr "ti")
    toAttrFrTyp n Description_xml'lang_tk = Just (n, str2attr "tk")
    toAttrFrTyp n Description_xml'lang_tl = Just (n, str2attr "tl")
    toAttrFrTyp n Description_xml'lang_tn = Just (n, str2attr "tn")
    toAttrFrTyp n Description_xml'lang_to = Just (n, str2attr "to")
    toAttrFrTyp n Description_xml'lang_tr = Just (n, str2attr "tr")
    toAttrFrTyp n Description_xml'lang_ts = Just (n, str2attr "ts")
    toAttrFrTyp n Description_xml'lang_tt = Just (n, str2attr "tt")
    toAttrFrTyp n Description_xml'lang_tw = Just (n, str2attr "tw")
    toAttrFrTyp n Description_xml'lang_ug = Just (n, str2attr "ug")
    toAttrFrTyp n Description_xml'lang_uk = Just (n, str2attr "uk")
    toAttrFrTyp n Description_xml'lang_ur = Just (n, str2attr "ur")
    toAttrFrTyp n Description_xml'lang_uz = Just (n, str2attr "uz")
    toAttrFrTyp n Description_xml'lang_vi = Just (n, str2attr "vi")
    toAttrFrTyp n Description_xml'lang_vo = Just (n, str2attr "vo")
    toAttrFrTyp n Description_xml'lang_wo = Just (n, str2attr "wo")
    toAttrFrTyp n Description_xml'lang_xh = Just (n, str2attr "xh")
    toAttrFrTyp n Description_xml'lang_yi = Just (n, str2attr "yi")
    toAttrFrTyp n Description_xml'lang_yo = Just (n, str2attr "yo")
    toAttrFrTyp n Description_xml'lang_za = Just (n, str2attr "za")
    toAttrFrTyp n Description_xml'lang_zh = Just (n, str2attr "zh")
    toAttrFrTyp n Description_xml'lang_zu = Just (n, str2attr "zu")
instance XmlContent Publisher where
    fromElem (CElem (Elem "Publisher" as c0):rest) =
	(\(a,ca)->
	   (Just (Publisher (fromAttrs as) a), rest))
	(definite fromElem "ANY" "Publisher" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Publisher as a) =
	[CElem (Elem "Publisher" (toAttrs as) (toElem a))]
instance XmlAttributes Publisher_Attrs where
    fromAttrs as =
	Publisher_Attrs
	  { publisherXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  , publisherId = possibleA fromAttrToStr "id" as
	  , publisherStyle = possibleA fromAttrToStr "style" as
	  , publisherMid = possibleA fromAttrToStr "mid" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (publisherXmlns v)
	, maybeToAttr toAttrFrStr "id" (publisherId v)
	, maybeToAttr toAttrFrStr "style" (publisherStyle v)
	, maybeToAttr toAttrFrStr "mid" (publisherMid v)
	]
instance XmlContent TypeMeta where
    fromElem (CElem (Elem "Type" as c0):rest) =
	(\(a,ca)->
	   (Just (TypeMeta (fromAttrs as) a), rest))
	(definite fromElem "ANY" "Type" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (TypeMeta as a) =
	[CElem (Elem "Type" (toAttrs as) (toElem a))]
instance XmlAttributes TypeMeta_Attrs where
    fromAttrs as =
	TypeMeta_Attrs
	  { typeMetaXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (typeMetaXmlns v)
	]
instance XmlContent Format where
    fromElem (CElem (Elem "Format" as c0):rest) =
	(\(a,ca)->
	   (Just (Format (fromAttrs as) a), rest))
	(definite fromElem "ANY" "Format" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Format as a) =
	[CElem (Elem "Format" (toAttrs as) (toElem a))]
instance XmlAttributes Format_Attrs where
    fromAttrs as =
	Format_Attrs
	  { formatXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (formatXmlns v)
	]
instance XmlContent Source where
    fromElem (CElem (Elem "Source" as c0):rest) =
	(\(a,ca)->
	   (Just (Source (fromAttrs as) a), rest))
	(definite fromElem "ANY" "Source" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Source as a) =
	[CElem (Elem "Source" (toAttrs as) (toElem a))]
instance XmlAttributes Source_Attrs where
    fromAttrs as =
	Source_Attrs
	  { sourceXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (sourceXmlns v)
	]
instance XmlContent Language where
    fromElem (CElem (Elem "Language" as c0):rest) =
	(\(a,ca)->
	   (Just (Language (fromAttrs as) a), rest))
	(definite fromElem "ANY" "Language" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Language as a) =
	[CElem (Elem "Language" (toAttrs as) (toElem a))]
instance XmlAttributes Language_Attrs where
    fromAttrs as =
	Language_Attrs
	  { languageXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (languageXmlns v)
	]
instance XmlContent Relation where
    fromElem (CElem (Elem "Relation" as c0):rest) =
	(\(a,ca)->
	   (Just (Relation (fromAttrs as) a), rest))
	(definite fromElem "ANY" "Relation" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Relation as a) =
	[CElem (Elem "Relation" (toAttrs as) (toElem a))]
instance XmlAttributes Relation_Attrs where
    fromAttrs as =
	Relation_Attrs
	  { relationXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (relationXmlns v)
	]
instance XmlContent Rights where
    fromElem (CElem (Elem "Rights" as c0):rest) =
	(\(a,ca)->
	   (Just (Rights (fromAttrs as) a), rest))
	(definite fromElem "ANY" "Rights" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Rights as a) =
	[CElem (Elem "Rights" (toAttrs as) (toElem a))]
instance XmlAttributes Rights_Attrs where
    fromAttrs as =
	Rights_Attrs
	  { rightsXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (rightsXmlns v)
	]
instance XmlContent Date where
    fromElem (CElem (Elem "Date" as c0):rest) =
	(\(a,ca)->
	   (Just (Date (fromAttrs as) a), rest))
	(definite fromText "text" "Date" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Date as a) =
	[CElem (Elem "Date" (toAttrs as) (toText a))]
instance XmlAttributes Date_Attrs where
    fromAttrs as =
	Date_Attrs
	  { dateXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  , dateAction = possibleA fromAttrToStr "action" as
	  , dateWho = possibleA fromAttrToStr "who" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (dateXmlns v)
	, maybeToAttr toAttrFrStr "action" (dateAction v)
	, maybeToAttr toAttrFrStr "who" (dateWho v)
	]
instance XmlContent Identifier where
    fromElem (CElem (Elem "Identifier" as c0):rest) =
	(\(a,ca)->
	   (Just (Identifier (fromAttrs as) a), rest))
	(definite fromText "text" "Identifier" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Identifier as a) =
	[CElem (Elem "Identifier" (toAttrs as) (toText a))]
instance XmlAttributes Identifier_Attrs where
    fromAttrs as =
	Identifier_Attrs
	  { identifierXmlns = defaultA fromAttrToStr "http://purl.org/DC" "xmlns" as
	  , identifierScheme = defaultA fromAttrToStr "ISBN" "scheme" as
	  }
    toAttrs v = catMaybes 
	[ defaultToAttr toAttrFrStr "xmlns" (identifierXmlns v)
	, defaultToAttr toAttrFrStr "scheme" (identifierScheme v)
	]
instance XmlContent Extradata where
    fromElem (CElem (Elem "extradata" [] []):rest) =
	(Just Extradata, rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem (CString _ s:rest) | all isSpace s = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem Extradata =
	[CElem (Elem "extradata" [] [])]


{-Done-}
