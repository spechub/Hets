-- $Id$

module Latin ( toASCII, fromASCII ) where

import List 
import Char

-- convert all LATIN-1 symbol to ASCII representations
--  useful for generating lowlevel labels from identifiers
--  the names are the ones specified in the Unicode standard
--
toASCII :: String -> String
toASCII []     = []
toASCII "\0"   = "_ControlCharacterNull_"
toASCII "\1"   = "_ControlCharacterStartOfHeading_"
toASCII "\2"   = "_ControlCharacterStartOfText_"
toASCII "\3"   = "_ControlCharacterEndTransmission_"
toASCII "\4"   = "_ControlCharacterEndOfText_"
toASCII "\5"   = "_ControlCharacterEnquiry_"
toASCII "\6"   = "_ControlCharacterAcknowledge_"
toASCII "\7"   = "_ControlCharacterBell_"
toASCII "\8"   = "_ControlCharacterBackspace_"
toASCII "\9"   = "_ControlCharacterHorizontalTabulation_"
toASCII "\10"  = "_ControlCharacterLineFeed_"
toASCII "\11"  = "_ControlCharacterVerticalTabulation_"
toASCII "\12"  = "_ControlCharacterFormFeed_"
toASCII "\13"  = "_ControlCharacterCarriageReturn_"
toASCII "\14"  = "_ControlCharacterShiftOut_"
toASCII "\15"  = "_ControlCharacterShiftIn_"
toASCII "\16"  = "_ControlCharacterDataLinkEscape_"
toASCII "\17"  = "_ControlCharacterDeviceControlOne_"
toASCII "\18"  = "_ControlCharacterDeviceControlTwo_"
toASCII "\19"  = "_ControlCharacterDeviceControlThree_"
toASCII "\20"  = "_ControlCharacterDeviceControlFour_"
toASCII "\21"  = "_ControlCharacterNegativeAckknowledge_"
toASCII "\22"  = "_ControlCharacterSynchronousIdle_"
toASCII "\23"  = "_ControlCharacterEndOfTransmissionBlock_"
toASCII "\24"  = "_ControlCharacterCancel_"
toASCII "\25"  = "_ControlCharacterEndOfMedium_"
toASCII "\26"  = "_ControlCharacterSubstitute_"
toASCII "\27"  = "_ControlCharacterEscape_"
toASCII "\28"  = "_ControlCharacterFileSeperator_"
toASCII "\29"  = "_ControlCharacterGroupSeperator_"
toASCII "\30"  = "_ControlCharacterRecordSeperator_"
toASCII "\31"  = "_ControlCharacterUnitSeperator_"
toASCII "\32"  = "_Space_"
toASCII "\33"  = "_ExclamationMark_"
toASCII "\34"  = "_QuotatationMark_"
toASCII "\35"  = "_NumberSign_"
toASCII "\36"  = "_DollarSign_"
toASCII "\37"  = "_PercentSign_"
toASCII "\38"  = "_Ampersand_"
toASCII "\40"  = "_LeftParenthesis_"
toASCII "\41"  = "_RightParenthesis_"
toASCII "\42"  = "_Asterisk_"
toASCII "\43"  = "_PlusSign_"
toASCII "\44"  = "_Comma_"
toASCII "\45"  = "_HyphenMinus_"
toASCII "\46"  = "_FullStop_"
toASCII "\47"  = "_Solidus_"
toASCII "\58"  = "_Colon_"
toASCII "\59"  = "_Semicolon_"
toASCII "\60"  = "_LessThanSign_"
toASCII "\61"  = "_EqualsSign_"
toASCII "\62"  = "_GreaterThanSign_"
toASCII "\63"  = "_QuestionMark_"
toASCII "\64"  = "_CommercialAt_"
toASCII "\91"  = "_LeftSquareBracket_"
toASCII "\92"  = "_ReverseSolidus_"
toASCII "\93"  = "_RightSquareBracket_"
toASCII "\94"  = "_Circumflex_"
toASCII "\96"  = "_GraveAccent_"
toASCII "\123" = "_LeftCurlyBracket_"
toASCII "\124" = "_VerticalLine_"
toASCII "\125" = "_RightCurlyBracket_"
toASCII "\126" = "_Tilde_"
toASCII "\127" = "_ControlCharacterDelete_"
toASCII "\128" = "_EuroSign_"
toASCII "\129" = "_RingAbove_"
toASCII "\130" = "_SingleLow9QuotationMark_"
toASCII "\131" = "_FWithHook_"
toASCII "\132" = "_DoubleLow9QuotationMark_"
toASCII "\133" = "_HorizontalEllipse_"
toASCII "\134" = "_Dagger_"
toASCII "\135" = "_DoubleDagger_"
toASCII "\136" = "_ModifierLetterCircumflexAccent_"
toASCII "\137" = "_PerMilleSign_"
toASCII "\138" = "_SCaron_"
toASCII "\139" = "_SingleLeftPointingAngleQuotationMark_"
toASCII "\140" = "_OELigature_"
toASCII "\141" = "_SmallCCedilla_"
toASCII "\142" = "_ZCaron_"
toASCII "\143" = "_SmallEGrave_"
toASCII "\144" = "_SmallECircumflex_"
toASCII "\145" = "_LeftSingleQuotationMark_"
toASCII "\146" = "_RightSingleQuotationMark_"
toASCII "\147" = "_LeftDoubleQuotationMark_"
toASCII "\148" = "_RightDoubleQuotationMark_"
toASCII "\149" = "_Bullet_"
toASCII "\150" = "_EnDash_"
toASCII "\151" = "_EmDash_"
toASCII "\152" = "_SmallTilde_"
toASCII "\153" = "_TradeMarkSign_"
toASCII "\154" = "_SCaron_"
toASCII "\155" = "_SingleRightPointingAngleQuotationMark_"
toASCII "\156" = "_SmallOELigature_"
toASCII "\157" = "_UGrave_"
toASCII "\158" = "_SmallZCaron_"
toASCII "\159" = "_YDiaeresis_"
toASCII "\160" = "_NonbreakingSpace_"
toASCII "\161" = "_InvertedExclamationMark_"
toASCII "\162" = "_CentSign_"
toASCII "\163" = "_PoundSign_"
toASCII "\164" = "_CurrencySign_"
toASCII "\165" = "_YenSign_"
toASCII "\166" = "_BrokenBar_"
toASCII "\167" = "_SectionSign_"
toASCII "\168" = "_Diaeresis_"
toASCII "\169" = "_CopyrightSign_"
toASCII "\170" = "_FeminineOrdinalIndicator_"
toASCII "\171" = "_LeftPointingDoubleAngleQuotationMark_"
toASCII "\172" = "_NotSign_"
toASCII "\173" = "_SoftHyphen_"
toASCII "\174" = "_RegisteredSign_"
toASCII "\175" = "_Macron_"
toASCII "\176" = "_DegreeSign_"
toASCII "\177" = "_PlusMinusSign_"
toASCII "\178" = "_SuperscriptTwo_"
toASCII "\179" = "_SuperscriptThree_"
toASCII "\180" = "_AcuteAccent_"
toASCII "\181" = "_MicroSign_"
toASCII "\182" = "_PilcrowSign_"
toASCII "\183" = "_MiddleDot_"
toASCII "\184" = "_Cedilla_"
toASCII "\185" = "_SuperscriptOne_"
toASCII "\186" = "_MasculineOrdinalIndicator_"
toASCII "\187" = "_RightPointingDoubleAngleQuotationMark_"
toASCII "\188" = "_VulgarFractionOneQuarter_"
toASCII "\189" = "_VulgarFractionOneHalf_"
toASCII "\190" = "_VulgarFractionThreeQuarters_"
toASCII "\191" = "_InvertedQuestionMark_"
toASCII "\192" = "_LatinCapitalLetterAWithGrave_"
toASCII "\193" = "_LatinCapitalLetterAWithAcute_"
toASCII "\194" = "_LatinCapitalLetterAWithCircumflex_"
toASCII "\195" = "_LatinCapotalLetterAWithTilde_"
toASCII "\196" = "_LatinCapitalLetterAWithDiaeresis_"
toASCII "\197" = "_LatinCapitalLetterAWithRingAbove_"
toASCII "\198" = "_LatinCapitalLetterAE_"
toASCII "\199" = "_LatinCapitalLetterCWithCedilla_"
toASCII "\200" = "_LatinCapitalLetterEWithGrave_"
toASCII "\201" = "_LatinCapitalLetterEWithAcute_"
toASCII "\202" = "_LatinCapitalLetterEWithCircumflex_"
toASCII "\203" = "_LatinCapitalLetterEWithDiaeresis_"
toASCII "\204" = "_LatinCapitalLetterIWithGrave_"
toASCII "\205" = "_LatinCapitalLetterIWithAcute_"
toASCII "\206" = "_LatinCapitalLetterIWithCircumflex_"
toASCII "\207" = "_LatinCapitalLetterIWithDiaeresis_"
toASCII "\208" = "_LatinCapitalLetterEth_"
toASCII "\209" = "_LatinCapitalLetterNWithTilde_"
toASCII "\210" = "_LatinCapitalLetterOWithGrave_"
toASCII "\211" = "_LatinCapitalLetterOWithAcute_"
toASCII "\212" = "_LatinCapitalLetterOWithCircumflex_"
toASCII "\213" = "_LatinCapitalLetterOWithTilde_"
toASCII "\214" = "_LatinCapitalLetterOWithDiaeresis_"
toASCII "\215" = "_MultiplicationSign_"
toASCII "\216" = "_LatinCapitalLetterOWithStroke_"
toASCII "\217" = "_LatinCapitalLetterUWithGrave_"
toASCII "\218" = "_LatinCapitalLetterUWithAcute_"
toASCII "\219" = "_LatinCapitalLetterUWithCircumflex_"
toASCII "\220" = "_LatinCapitalLetterUWithDiaeresis_"
toASCII "\221" = "_LatinCapitalLetterYWithAcute_"
toASCII "\222" = "_LatinCapitalLetterThorn_"
toASCII "\223" = "_LatinSmallLetterSharpS_"
toASCII "\224" = "_LatinSmallLetterAWithGrave_"
toASCII "\225" = "_LatinSmallLetterAWithAcute_"
toASCII "\226" = "_LatinSmallLetterAWithCircumflex_"
toASCII "\227" = "_LatinSmallLetterAWithTilde_"
toASCII "\228" = "_LatinSmallLetterAWithDiaeresis_"
toASCII "\229" = "_LatinSmallLetterAWithRingAbove_"
toASCII "\230" = "_LatinSmallLetterAE_"
toASCII "\231" = "_LatinSmallLetterCWithCedilla_"
toASCII "\232" = "_LatinSmallLetterEWithGrave_"
toASCII "\233" = "_LatinSmallLetterEWithAcute_"
toASCII "\234" = "_LatinSmallLetterEWithCircumflex_"
toASCII "\235" = "_LatinSmallLetterEWithDiaeresis_"
toASCII "\236" = "_LatinSmallLetterIWithGrave_"
toASCII "\237" = "_LatinSmallLetterIWithAcute_"
toASCII "\238" = "_LatinSmallLetterIWithCircumflex_"
toASCII "\239" = "_LatinSmallLetterIWithDiaeresis_"
toASCII "\240" = "_LatinSmallLetterEth_"
toASCII "\241" = "_LatinSmallLetterNWithTilde_"
toASCII "\242" = "_LatinSmallLetterOWithGrave_"
toASCII "\243" = "_LatinSmallLetterOWithAcute_"
toASCII "\244" = "_LatinSmallLetterOWithCircumflex_"
toASCII "\245" = "_LatinSmallLetterOWithTilde_"
toASCII "\246" = "_LatinSmallLetterOWithDiaeresis_"
toASCII "\247" = "_DivisionSign_"
toASCII "\248" = "_LatinSmallLetterOWithStroke_"
toASCII "\249" = "_LatinSmallLetterUWithGrave_"
toASCII "\250" = "_LatinSmallLetterUWithAcute_"
toASCII "\251" = "_LatinSmallLetterUWithCircumflex_"
toASCII "\252" = "_LatinSmallLetterUWithDiaeresis_"
toASCII "\253" = "_LatinSmallLettterYWithAcute_"
toASCII "\254" = "_LatinSmallLetterThorn_"
toASCII "\255" = "_LatinSmallLetterYWithDiaeresis_"
toASCII [x]    = [x]
toASCII l      = concat $ map (toASCII . (\x -> [x])) l

-- a list of all possible transscription strings
--
allTransscripts :: [String]
allTransscripts = map (toASCII.(\x -> [x])) ['\0'..'\255']

-- check to see if one of the transscriptions strings in the given list
--  fits the beginning of a string
--  if yes, return the corresponding normal LATIN-1 character as the new
--  starting character of the string and drop the transscription from
--  the beginning of the string
--  if no, return the original string
--
checkOne :: String -> [String] -> Int -> String
checkOne s [] idx    = s
checkOne s (h:t) idx = if (h `isPrefixOf` s) then
                         (chr idx):(drop (length h) s)
                       else
                         checkOne s t (idx+1)

-- convert from ASCII with LATIN-1 transscriptions to LATIN-1
--  runs checkOne with the complete transscriptions list as generatable
--  by fromASCII, starting with the whole string, then dropping the
--  first character after the check to iterate over the whole string
--
fromASCII :: String -> String
fromASCII [] = []
fromASCII s  = let
                 try = checkOne s allTransscripts 0
                 res = if (length s>1) then
                         if (take 2 s)=="__" then
                           s
                         else
                           try
                       else
                         try
               in
                 (head res):(fromASCII $ tail res) 
