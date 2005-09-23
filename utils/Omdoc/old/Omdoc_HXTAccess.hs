-- ----------------------------------------
--
-- don't edit this module
-- generated with DTDtoHXml
-- simple access function for Haskell XML Toolbox
-- generated from DTD of document: "nocan_omdoc.dtd"

{- EDIT - Namespace declarations had to be fixed. - EDIT -}
{- EDIT - DOCTYPE-Element definition - EDIT -}

module Omdoc_HXTAccess
where

import Text.XML.HXT.DOM.XmlTree (XmlFilter)
import qualified Text.XML.HXT.DOM.XmlTree as X
import qualified Text.XML.HXT.DOM.XmlTreeTypes as XT

mkOmdocTypeElem::String->XT.XNode
mkOmdocTypeElem system =
	XT.XDTD XT.DOCTYPE [
		 ("name", "omdoc")
		,("PUBLIC", "-//OMDoc//DTD OMDoc V1.1//EN")
		,("SYSTEM", system)
		]

omdocDocTypeElem::XT.XNode
omdocDocTypeElem = mkOmdocTypeElem "omdoc.dtd"

-- ----------------------------------------
--
-- namespace declarations

nsomdoc :: String
nsxsi :: String
nsopenmath :: String
nspurl :: String
-- ----------------------------------------
--
-- 

nsomdoc =  "http://www.mathweb.org/omdoc"
nsxsi = "http://www.w3.org/2001/XMLSchema-instance"
nsxsischemalocation = "http://www.mathweb.org/omdoc\nhttp://www.mathweb.org/omdoc/xsd/omdoc.xsd"
nsopenmath = "http://www.openmath.org/OpenMath" 
nspurl = "http://purl.org/DC"
-- ----------------------------------------
--
-- element names (tag names)

tagCMP              :: String
tagContributor      :: String
tagCreator          :: String
tagDate             :: String
tagDescription      :: String
tagFMP              :: String
tagFormat           :: String
tagIdentifier       :: String
tagLanguage         :: String
tagOMA              :: String
tagOMATP            :: String
tagOMATTR           :: String
tagOMB              :: String
tagOMBIND           :: String
tagOMBVAR           :: String
tagOME              :: String
tagOMF              :: String
tagOMI              :: String
tagOMOBJ            :: String
tagOMS              :: String
tagOMSTR            :: String
tagOMV              :: String
tagPublisher        :: String
tagRelation         :: String
tagRights           :: String
tagSource           :: String
tagSubject          :: String
tagTitle            :: String
tagType             :: String
tagadt              :: String
tagalternative      :: String
taganswer           :: String
tagargument         :: String
tagassertion        :: String
tagassumption       :: String
tagattribute        :: String
tagaxiom            :: String
tagaxiom_inclusion  :: String
tagcatalogue        :: String
tagchoice           :: String
tagcode             :: String
tagcommonname       :: String
tagconclude         :: String
tagconclusion       :: String
tagconstructor      :: String
tagdata             :: String
tagdecomposition    :: String
tagdefinition       :: String
tagderive           :: String
tageffect           :: String
tagelement          :: String
tagexample          :: String
tagexercise         :: String
tagextradata        :: String
taghint             :: String
taghypothesis       :: String
tagignore           :: String
tagimports          :: String
taginclusion        :: String
taginput            :: String
taginsort           :: String
tagloc              :: String
tagmc               :: String
tagmeasure          :: String
tagmetacomment      :: String
tagmetadata         :: String
tagmethod           :: String
tagmorphism         :: String
tagobligation       :: String
tagomdoc            :: String
tagomgroup          :: String
tagomlet            :: String
tagomstyle          :: String
tagomtext           :: String
tagordering         :: String
tagoutput           :: String
tagpath_just        :: String
tagpattern          :: String
tagpremise          :: String
tagpresentation     :: String
tagprivate          :: String
tagproof            :: String
tagproofobject      :: String
tagrecognizer       :: String
tagrecurse          :: String
tagref              :: String
tagrequation        :: String
tagselector         :: String
tagsolution         :: String
tagsortdef          :: String
tagstyle            :: String
tagsymbol           :: String
tagtext             :: String
tagtheory           :: String
tagtheory_inclusion :: String
tagtype             :: String
taguse              :: String
tagvalue            :: String
tagvalue_of         :: String
tagwith             :: String
tagxslt             :: String

-- ----------------------------------------
--
-- 

tagCMP              =  "CMP"
tagContributor      =  "Contributor"
tagCreator          =  "Creator"
tagDate             =  "Date"
tagDescription      =  "Description"
tagFMP              =  "FMP"
tagFormat           =  "Format"
tagIdentifier       =  "Identifier"
tagLanguage         =  "Language"
tagOMA              =  "OMA"
tagOMATP            =  "OMATP"
tagOMATTR           =  "OMATTR"
tagOMB              =  "OMB"
tagOMBIND           =  "OMBIND"
tagOMBVAR           =  "OMBVAR"
tagOME              =  "OME"
tagOMF              =  "OMF"
tagOMI              =  "OMI"
tagOMOBJ            =  "OMOBJ"
tagOMS              =  "OMS"
tagOMSTR            =  "OMSTR"
tagOMV              =  "OMV"
tagPublisher        =  "Publisher"
tagRelation         =  "Relation"
tagRights           =  "Rights"
tagSource           =  "Source"
tagSubject          =  "Subject"
tagTitle            =  "Title"
tagType             =  "Type"
tagadt              =  "adt"
tagalternative      =  "alternative"
taganswer           =  "answer"
tagargument         =  "argument"
tagassertion        =  "assertion"
tagassumption       =  "assumption"
tagattribute        =  "attribute"
tagaxiom            =  "axiom"
tagaxiom_inclusion  =  "axiom-inclusion"
tagcatalogue        =  "catalogue"
tagchoice           =  "choice"
tagcode             =  "code"
tagcommonname       =  "commonname"
tagconclude         =  "conclude"
tagconclusion       =  "conclusion"
tagconstructor      =  "constructor"
tagdata             =  "data"
tagdecomposition    =  "decomposition"
tagdefinition       =  "definition"
tagderive           =  "derive"
tageffect           =  "effect"
tagelement          =  "element"
tagexample          =  "example"
tagexercise         =  "exercise"
tagextradata        =  "extradata"
taghint             =  "hint"
taghypothesis       =  "hypothesis"
tagignore           =  "ignore"
tagimports          =  "imports"
taginclusion        =  "inclusion"
taginput            =  "input"
taginsort           =  "insort"
tagloc              =  "loc"
tagmc               =  "mc"
tagmeasure          =  "measure"
tagmetacomment      =  "metacomment"
tagmetadata         =  "metadata"
tagmethod           =  "method"
tagmorphism         =  "morphism"
tagobligation       =  "obligation"
tagomdoc            =  "omdoc"
tagomgroup          =  "omgroup"
tagomlet            =  "omlet"
tagomstyle          =  "omstyle"
tagomtext           =  "omtext"
tagordering         =  "ordering"
tagoutput           =  "output"
tagpath_just        =  "path-just"
tagpattern          =  "pattern"
tagpremise          =  "premise"
tagpresentation     =  "presentation"
tagprivate          =  "private"
tagproof            =  "proof"
tagproofobject      =  "proofobject"
tagrecognizer       =  "recognizer"
tagrecurse          =  "recurse"
tagref              =  "ref"
tagrequation        =  "requation"
tagselector         =  "selector"
tagsolution         =  "solution"
tagsortdef          =  "sortdef"
tagstyle            =  "style"
tagsymbol           =  "symbol"
tagtext             =  "text"
tagtheory           =  "theory"
tagtheory_inclusion =  "theory-inclusion"
tagtype             =  "type"
taguse              =  "use"
tagvalue            =  "value"
tagvalue_of         =  "value-of"
tagwith             =  "with"
tagxslt             =  "xslt"

-- ----------------------------------------
--
-- isTag test filter

isCMP              :: XmlFilter
isContributor      :: XmlFilter
isCreator          :: XmlFilter
isDate             :: XmlFilter
isDescription      :: XmlFilter
isFMP              :: XmlFilter
isFormat           :: XmlFilter
isIdentifier       :: XmlFilter
isLanguage         :: XmlFilter
isOMA              :: XmlFilter
isOMATP            :: XmlFilter
isOMATTR           :: XmlFilter
isOMB              :: XmlFilter
isOMBIND           :: XmlFilter
isOMBVAR           :: XmlFilter
isOME              :: XmlFilter
isOMF              :: XmlFilter
isOMI              :: XmlFilter
isOMOBJ            :: XmlFilter
isOMS              :: XmlFilter
isOMSTR            :: XmlFilter
isOMV              :: XmlFilter
isPublisher        :: XmlFilter
isRelation         :: XmlFilter
isRights           :: XmlFilter
isSource           :: XmlFilter
isSubject          :: XmlFilter
isTitle            :: XmlFilter
isType             :: XmlFilter
isadt              :: XmlFilter
isalternative      :: XmlFilter
isanswer           :: XmlFilter
isargument         :: XmlFilter
isassertion        :: XmlFilter
isassumption       :: XmlFilter
isattribute        :: XmlFilter
isaxiom            :: XmlFilter
isaxiom_inclusion  :: XmlFilter
iscatalogue        :: XmlFilter
ischoice           :: XmlFilter
iscode             :: XmlFilter
iscommonname       :: XmlFilter
isconclude         :: XmlFilter
isconclusion       :: XmlFilter
isconstructor      :: XmlFilter
isdata             :: XmlFilter
isdecomposition    :: XmlFilter
isdefinition       :: XmlFilter
isderive           :: XmlFilter
iseffect           :: XmlFilter
iselement          :: XmlFilter
isexample          :: XmlFilter
isexercise         :: XmlFilter
isextradata        :: XmlFilter
ishint             :: XmlFilter
ishypothesis       :: XmlFilter
isignore           :: XmlFilter
isimports          :: XmlFilter
isinclusion        :: XmlFilter
isinput            :: XmlFilter
isinsort           :: XmlFilter
isloc              :: XmlFilter
ismc               :: XmlFilter
ismeasure          :: XmlFilter
ismetacomment      :: XmlFilter
ismetadata         :: XmlFilter
ismethod           :: XmlFilter
ismorphism         :: XmlFilter
isobligation       :: XmlFilter
isomdoc            :: XmlFilter
isomgroup          :: XmlFilter
isomlet            :: XmlFilter
isomstyle          :: XmlFilter
isomtext           :: XmlFilter
isordering         :: XmlFilter
isoutput           :: XmlFilter
ispath_just        :: XmlFilter
ispattern          :: XmlFilter
ispremise          :: XmlFilter
ispresentation     :: XmlFilter
isprivate          :: XmlFilter
isproof            :: XmlFilter
isproofobject      :: XmlFilter
isrecognizer       :: XmlFilter
isrecurse          :: XmlFilter
isref              :: XmlFilter
isrequation        :: XmlFilter
isselector         :: XmlFilter
issolution         :: XmlFilter
issortdef          :: XmlFilter
isstyle            :: XmlFilter
issymbol           :: XmlFilter
istext             :: XmlFilter
istheory           :: XmlFilter
istheory_inclusion :: XmlFilter
istype             :: XmlFilter
isuse              :: XmlFilter
isvalue            :: XmlFilter
isvalue_of         :: XmlFilter
iswith             :: XmlFilter
isxslt             :: XmlFilter

-- ----------------------------------------
--
-- 

isCMP              =  X.isTag tagCMP
isContributor      =  X.isTag tagContributor
isCreator          =  X.isTag tagCreator
isDate             =  X.isTag tagDate
isDescription      =  X.isTag tagDescription
isFMP              =  X.isTag tagFMP
isFormat           =  X.isTag tagFormat
isIdentifier       =  X.isTag tagIdentifier
isLanguage         =  X.isTag tagLanguage
isOMA              =  X.isTag tagOMA
isOMATP            =  X.isTag tagOMATP
isOMATTR           =  X.isTag tagOMATTR
isOMB              =  X.isTag tagOMB
isOMBIND           =  X.isTag tagOMBIND
isOMBVAR           =  X.isTag tagOMBVAR
isOME              =  X.isTag tagOME
isOMF              =  X.isTag tagOMF
isOMI              =  X.isTag tagOMI
isOMOBJ            =  X.isTag tagOMOBJ
isOMS              =  X.isTag tagOMS
isOMSTR            =  X.isTag tagOMSTR
isOMV              =  X.isTag tagOMV
isPublisher        =  X.isTag tagPublisher
isRelation         =  X.isTag tagRelation
isRights           =  X.isTag tagRights
isSource           =  X.isTag tagSource
isSubject          =  X.isTag tagSubject
isTitle            =  X.isTag tagTitle
isType             =  X.isTag tagType
isadt              =  X.isTag tagadt
isalternative      =  X.isTag tagalternative
isanswer           =  X.isTag taganswer
isargument         =  X.isTag tagargument
isassertion        =  X.isTag tagassertion
isassumption       =  X.isTag tagassumption
isattribute        =  X.isTag tagattribute
isaxiom            =  X.isTag tagaxiom
isaxiom_inclusion  =  X.isTag tagaxiom_inclusion
iscatalogue        =  X.isTag tagcatalogue
ischoice           =  X.isTag tagchoice
iscode             =  X.isTag tagcode
iscommonname       =  X.isTag tagcommonname
isconclude         =  X.isTag tagconclude
isconclusion       =  X.isTag tagconclusion
isconstructor      =  X.isTag tagconstructor
isdata             =  X.isTag tagdata
isdecomposition    =  X.isTag tagdecomposition
isdefinition       =  X.isTag tagdefinition
isderive           =  X.isTag tagderive
iseffect           =  X.isTag tageffect
iselement          =  X.isTag tagelement
isexample          =  X.isTag tagexample
isexercise         =  X.isTag tagexercise
isextradata        =  X.isTag tagextradata
ishint             =  X.isTag taghint
ishypothesis       =  X.isTag taghypothesis
isignore           =  X.isTag tagignore
isimports          =  X.isTag tagimports
isinclusion        =  X.isTag taginclusion
isinput            =  X.isTag taginput
isinsort           =  X.isTag taginsort
isloc              =  X.isTag tagloc
ismc               =  X.isTag tagmc
ismeasure          =  X.isTag tagmeasure
ismetacomment      =  X.isTag tagmetacomment
ismetadata         =  X.isTag tagmetadata
ismethod           =  X.isTag tagmethod
ismorphism         =  X.isTag tagmorphism
isobligation       =  X.isTag tagobligation
isomdoc            =  X.isTag tagomdoc
isomgroup          =  X.isTag tagomgroup
isomlet            =  X.isTag tagomlet
isomstyle          =  X.isTag tagomstyle
isomtext           =  X.isTag tagomtext
isordering         =  X.isTag tagordering
isoutput           =  X.isTag tagoutput
ispath_just        =  X.isTag tagpath_just
ispattern          =  X.isTag tagpattern
ispremise          =  X.isTag tagpremise
ispresentation     =  X.isTag tagpresentation
isprivate          =  X.isTag tagprivate
isproof            =  X.isTag tagproof
isproofobject      =  X.isTag tagproofobject
isrecognizer       =  X.isTag tagrecognizer
isrecurse          =  X.isTag tagrecurse
isref              =  X.isTag tagref
isrequation        =  X.isTag tagrequation
isselector         =  X.isTag tagselector
issolution         =  X.isTag tagsolution
issortdef          =  X.isTag tagsortdef
isstyle            =  X.isTag tagstyle
issymbol           =  X.isTag tagsymbol
istext             =  X.isTag tagtext
istheory           =  X.isTag tagtheory
istheory_inclusion =  X.isTag tagtheory_inclusion
istype             =  X.isTag tagtype
isuse              =  X.isTag taguse
isvalue            =  X.isTag tagvalue
isvalue_of         =  X.isTag tagvalue_of
iswith             =  X.isTag tagwith
isxslt             =  X.isTag tagxslt

-- ----------------------------------------
--
-- make tag nodes constructor filter

tCMP              :: XmlFilter
tContributor      :: XmlFilter
tCreator          :: XmlFilter
tDate             :: XmlFilter
tDescription      :: XmlFilter
tFMP              :: XmlFilter
tFormat           :: XmlFilter
tIdentifier       :: XmlFilter
tLanguage         :: XmlFilter
tOMA              :: XmlFilter
tOMATP            :: XmlFilter
tOMATTR           :: XmlFilter
tOMB              :: XmlFilter
tOMBIND           :: XmlFilter
tOMBVAR           :: XmlFilter
tOME              :: XmlFilter
tOMF              :: XmlFilter
tOMI              :: XmlFilter
tOMOBJ            :: XmlFilter
tOMS              :: XmlFilter
tOMSTR            :: XmlFilter
tOMV              :: XmlFilter
tPublisher        :: XmlFilter
tRelation         :: XmlFilter
tRights           :: XmlFilter
tSource           :: XmlFilter
tSubject          :: XmlFilter
tTitle            :: XmlFilter
tType             :: XmlFilter
tadt              :: XmlFilter
talternative      :: XmlFilter
tanswer           :: XmlFilter
targument         :: XmlFilter
tassertion        :: XmlFilter
tassumption       :: XmlFilter
tattribute        :: XmlFilter
taxiom            :: XmlFilter
taxiom_inclusion  :: XmlFilter
tcatalogue        :: XmlFilter
tchoice           :: XmlFilter
tcode             :: XmlFilter
tcommonname       :: XmlFilter
tconclude         :: XmlFilter
tconclusion       :: XmlFilter
tconstructor      :: XmlFilter
tdata             :: XmlFilter
tdecomposition    :: XmlFilter
tdefinition       :: XmlFilter
tderive           :: XmlFilter
teffect           :: XmlFilter
telement          :: XmlFilter
texample          :: XmlFilter
texercise         :: XmlFilter
textradata        :: XmlFilter
thint             :: XmlFilter
thypothesis       :: XmlFilter
tignore           :: XmlFilter
timports          :: XmlFilter
tinclusion        :: XmlFilter
tinput            :: XmlFilter
tinsort           :: XmlFilter
tloc              :: XmlFilter
tmc               :: XmlFilter
tmeasure          :: XmlFilter
tmetacomment      :: XmlFilter
tmetadata         :: XmlFilter
tmethod           :: XmlFilter
tmorphism         :: XmlFilter
tobligation       :: XmlFilter
tomdoc            :: XmlFilter
tomgroup          :: XmlFilter
tomlet            :: XmlFilter
tomstyle          :: XmlFilter
tomtext           :: XmlFilter
tordering         :: XmlFilter
toutput           :: XmlFilter
tpath_just        :: XmlFilter
tpattern          :: XmlFilter
tpremise          :: XmlFilter
tpresentation     :: XmlFilter
tprivate          :: XmlFilter
tproof            :: XmlFilter
tproofobject      :: XmlFilter
trecognizer       :: XmlFilter
trecurse          :: XmlFilter
tref              :: XmlFilter
trequation        :: XmlFilter
tselector         :: XmlFilter
tsolution         :: XmlFilter
tsortdef          :: XmlFilter
tstyle            :: XmlFilter
tsymbol           :: XmlFilter
ttext             :: XmlFilter
ttheory           :: XmlFilter
ttheory_inclusion :: XmlFilter
ttype             :: XmlFilter
tuse              :: XmlFilter
tvalue            :: XmlFilter
tvalue_of         :: XmlFilter
twith             :: XmlFilter
txslt             :: XmlFilter

-- ----------------------------------------
--
-- 

tCMP              = X.etag tagCMP
tContributor      = X.etag tagContributor
tCreator          = X.etag tagCreator
tDate             = X.etag tagDate
tDescription      = X.etag tagDescription
tFMP              = X.etag tagFMP
tFormat           = X.etag tagFormat
tIdentifier       = X.etag tagIdentifier
tLanguage         = X.etag tagLanguage
tOMA              = X.etag tagOMA
tOMATP            = X.etag tagOMATP
tOMATTR           = X.etag tagOMATTR
tOMB              = X.etag tagOMB
tOMBIND           = X.etag tagOMBIND
tOMBVAR           = X.etag tagOMBVAR
tOME              = X.etag tagOME
tOMF              = X.etag tagOMF
tOMI              = X.etag tagOMI
tOMOBJ            = X.etag tagOMOBJ
tOMS              = X.etag tagOMS
tOMSTR            = X.etag tagOMSTR
tOMV              = X.etag tagOMV
tPublisher        = X.etag tagPublisher
tRelation         = X.etag tagRelation
tRights           = X.etag tagRights
tSource           = X.etag tagSource
tSubject          = X.etag tagSubject
tTitle            = X.etag tagTitle
tType             = X.etag tagType
tadt              = X.etag tagadt
talternative      = X.etag tagalternative
tanswer           = X.etag taganswer
targument         = X.etag tagargument
tassertion        = X.etag tagassertion
tassumption       = X.etag tagassumption
tattribute        = X.etag tagattribute
taxiom            = X.etag tagaxiom
taxiom_inclusion  = X.etag tagaxiom_inclusion
tcatalogue        = X.etag tagcatalogue
tchoice           = X.etag tagchoice
tcode             = X.etag tagcode
tcommonname       = X.etag tagcommonname
tconclude         = X.etag tagconclude
tconclusion       = X.etag tagconclusion
tconstructor      = X.etag tagconstructor
tdata             = X.etag tagdata
tdecomposition    = X.etag tagdecomposition
tdefinition       = X.etag tagdefinition
tderive           = X.etag tagderive
teffect           = X.etag tageffect
telement          = X.etag tagelement
texample          = X.etag tagexample
texercise         = X.etag tagexercise
textradata        = X.etag tagextradata
thint             = X.etag taghint
thypothesis       = X.etag taghypothesis
tignore           = X.etag tagignore
timports          = X.etag tagimports
tinclusion        = X.etag taginclusion
tinput            = X.etag taginput
tinsort           = X.etag taginsort
tloc              = X.etag tagloc
tmc               = X.etag tagmc
tmeasure          = X.etag tagmeasure
tmetacomment      = X.etag tagmetacomment
tmetadata         = X.etag tagmetadata
tmethod           = X.etag tagmethod
tmorphism         = X.etag tagmorphism
tobligation       = X.etag tagobligation
tomdoc            = X.etag tagomdoc
tomgroup          = X.etag tagomgroup
tomlet            = X.etag tagomlet
tomstyle          = X.etag tagomstyle
tomtext           = X.etag tagomtext
tordering         = X.etag tagordering
toutput           = X.etag tagoutput
tpath_just        = X.etag tagpath_just
tpattern          = X.etag tagpattern
tpremise          = X.etag tagpremise
tpresentation     = X.etag tagpresentation
tprivate          = X.etag tagprivate
tproof            = X.etag tagproof
tproofobject      = X.etag tagproofobject
trecognizer       = X.etag tagrecognizer
trecurse          = X.etag tagrecurse
tref              = X.etag tagref
trequation        = X.etag tagrequation
tselector         = X.etag tagselector
tsolution         = X.etag tagsolution
tsortdef          = X.etag tagsortdef
tstyle            = X.etag tagstyle
tsymbol           = X.etag tagsymbol
ttext             = X.etag tagtext
ttheory           = X.etag tagtheory
ttheory_inclusion = X.etag tagtheory_inclusion
ttype             = X.etag tagtype
tuse              = X.etag taguse
tvalue            = X.etag tagvalue
tvalue_of         = X.etag tagvalue_of
twith             = X.etag tagwith
txslt             = X.etag tagxslt

-- ----------------------------------------
--
-- attribute names

attraction             :: String
attrargstr             :: String
attrassertion          :: String
attrattributes         :: String
attrbase               :: String
attrbracket_style      :: String
attrcatalogue          :: String
attrcd                 :: String
attrclassid            :: String
attrcodebase           :: String
attrcomment            :: String
attrcrossref_symbol    :: String
attrdata               :: String
attrdec                :: String
attrdischarged_in      :: String
attrelement            :: String
attrentailed_by        :: String
attrentailed_by_thm    :: String
attrentails            :: String
attrentails_thm        :: String
attrfixity             :: String
attrfor                :: String
attrformat             :: String
attrfrom               :: String
attrfunction           :: String
attrgenerated_by       :: String
attrglobals            :: String
attrheight             :: String
attrhex                :: String
attrhiding             :: String
attrhref               :: String
attrid                 :: String
attrinduced_by         :: String
attrinherits           :: String
attrjust_by            :: String
attrkind               :: String
attrlarg_group         :: String
attrlbrack             :: String
attrlinks              :: String
attrlocal              :: String
attrlogic              :: String
attrmid                :: String
attrname               :: String
attromdoc              :: String
attrparent             :: String
attrprecedence         :: String
attrproofs             :: String
attrpto                :: String
attrpto_version        :: String
attrrank               :: String
attrrarg_group         :: String
attrrbrack             :: String
attrreplaces           :: String
attrrequires           :: String
attrrole               :: String
attrscheme             :: String
attrscope              :: String
attrselect             :: String
attrseparator          :: String
attrsize               :: String
attrsort               :: String
attrstyle              :: String
attrsystem             :: String
attrtheory             :: String
attrto                 :: String
attrtotal              :: String
attrtype               :: String
attrverdict            :: String
attrversion            :: String
attrvia                :: String
attrwho                :: String
attrwidth              :: String
attrxml_lang           :: String
attrxmlns              :: String
attrxmlns_xsi          :: String
attrxref               :: String
attrxsi_schemaLocation :: String

-- ----------------------------------------
--
-- 

attraction             =  "action"
attrargstr             =  "argstr"
attrassertion          =  "assertion"
attrattributes         =  "attributes"
attrbase               =  "base"
attrbracket_style      =  "bracket-style"
attrcatalogue          =  "catalogue"
attrcd                 =  "cd"
attrclassid            =  "classid"
attrcodebase           =  "codebase"
attrcomment            =  "comment"
attrcrossref_symbol    =  "crossref-symbol"
attrdata               =  "data"
attrdec                =  "dec"
attrdischarged_in      =  "discharged-in"
attrelement            =  "element"
attrentailed_by        =  "entailed-by"
attrentailed_by_thm    =  "entailed-by-thm"
attrentails            =  "entails"
attrentails_thm        =  "entails-thm"
attrfixity             =  "fixity"
attrfor                =  "for"
attrformat             =  "format"
attrfrom               =  "from"
attrfunction           =  "function"
attrgenerated_by       =  "generated-by"
attrglobals            =  "globals"
attrheight             =  "height"
attrhex                =  "hex"
attrhiding             =  "hiding"
attrhref               =  "href"
attrid                 =  "id"
attrinduced_by         =  "induced-by"
attrinherits           =  "inherits"
attrjust_by            =  "just-by"
attrkind               =  "kind"
attrlarg_group         =  "larg-group"
attrlbrack             =  "lbrack"
attrlinks              =  "links"
attrlocal              =  "local"
attrlogic              =  "logic"
attrmid                =  "mid"
attrname               =  "name"
attromdoc              =  "omdoc"
attrparent             =  "parent"
attrprecedence         =  "precedence"
attrproofs             =  "proofs"
attrpto                =  "pto"
attrpto_version        =  "pto-version"
attrrank               =  "rank"
attrrarg_group         =  "rarg-group"
attrrbrack             =  "rbrack"
attrreplaces           =  "replaces"
attrrequires           =  "requires"
attrrole               =  "role"
attrscheme             =  "scheme"
attrscope              =  "scope"
attrselect             =  "select"
attrseparator          =  "separator"
attrsize               =  "size"
attrsort               =  "sort"
attrstyle              =  "style"
attrsystem             =  "system"
attrtheory             =  "theory"
attrto                 =  "to"
attrtotal              =  "total"
attrtype               =  "type"
attrverdict            =  "verdict"
attrversion            =  "version"
attrvia                =  "via"
attrwho                =  "who"
attrwidth              =  "width"
attrxml_lang           =  "xml:lang"
attrxmlns              =  "xmlns"
attrxmlns_xsi          =  "xmlns:xsi"
attrxref               =  "xref"
attrxsi_schemaLocation =  "xsi:schemaLocation"

-- ----------------------------------------
--
-- get attribute value access filter

getaction             :: XmlFilter
getargstr             :: XmlFilter
getassertion          :: XmlFilter
getattributes         :: XmlFilter
getbase               :: XmlFilter
getbracket_style      :: XmlFilter
getcatalogue          :: XmlFilter
getcd                 :: XmlFilter
getclassid            :: XmlFilter
getcodebase           :: XmlFilter
getcomment            :: XmlFilter
getcrossref_symbol    :: XmlFilter
getdata               :: XmlFilter
getdec                :: XmlFilter
getdischarged_in      :: XmlFilter
getelement            :: XmlFilter
getentailed_by        :: XmlFilter
getentailed_by_thm    :: XmlFilter
getentails            :: XmlFilter
getentails_thm        :: XmlFilter
getfixity             :: XmlFilter
getfor                :: XmlFilter
getformat             :: XmlFilter
getfrom               :: XmlFilter
getfunction           :: XmlFilter
getgenerated_by       :: XmlFilter
getglobals            :: XmlFilter
getheight             :: XmlFilter
gethex                :: XmlFilter
gethiding             :: XmlFilter
gethref               :: XmlFilter
getid                 :: XmlFilter
getinduced_by         :: XmlFilter
getinherits           :: XmlFilter
getjust_by            :: XmlFilter
getkind               :: XmlFilter
getlarg_group         :: XmlFilter
getlbrack             :: XmlFilter
getlinks              :: XmlFilter
getlocal              :: XmlFilter
getlogic              :: XmlFilter
getmid                :: XmlFilter
getname               :: XmlFilter
getomdoc              :: XmlFilter
getparent             :: XmlFilter
getprecedence         :: XmlFilter
getproofs             :: XmlFilter
getpto                :: XmlFilter
getpto_version        :: XmlFilter
getrank               :: XmlFilter
getrarg_group         :: XmlFilter
getrbrack             :: XmlFilter
getreplaces           :: XmlFilter
getrequires           :: XmlFilter
getrole               :: XmlFilter
getscheme             :: XmlFilter
getscope              :: XmlFilter
getselect             :: XmlFilter
getseparator          :: XmlFilter
getsize               :: XmlFilter
getsort               :: XmlFilter
getstyle              :: XmlFilter
getsystem             :: XmlFilter
gettheory             :: XmlFilter
getto                 :: XmlFilter
gettotal              :: XmlFilter
gettype               :: XmlFilter
getverdict            :: XmlFilter
getversion            :: XmlFilter
getvia                :: XmlFilter
getwho                :: XmlFilter
getwidth              :: XmlFilter
getxml_lang           :: XmlFilter
getxmlns              :: XmlFilter
getxmlns_xsi          :: XmlFilter
getxref               :: XmlFilter
getxsi_schemaLocation :: XmlFilter

-- ----------------------------------------
--
-- 

getaction             =  X.getValue attraction
getargstr             =  X.getValue attrargstr
getassertion          =  X.getValue attrassertion
getattributes         =  X.getValue attrattributes
getbase               =  X.getValue attrbase
getbracket_style      =  X.getValue attrbracket_style
getcatalogue          =  X.getValue attrcatalogue
getcd                 =  X.getValue attrcd
getclassid            =  X.getValue attrclassid
getcodebase           =  X.getValue attrcodebase
getcomment            =  X.getValue attrcomment
getcrossref_symbol    =  X.getValue attrcrossref_symbol
getdata               =  X.getValue attrdata
getdec                =  X.getValue attrdec
getdischarged_in      =  X.getValue attrdischarged_in
getelement            =  X.getValue attrelement
getentailed_by        =  X.getValue attrentailed_by
getentailed_by_thm    =  X.getValue attrentailed_by_thm
getentails            =  X.getValue attrentails
getentails_thm        =  X.getValue attrentails_thm
getfixity             =  X.getValue attrfixity
getfor                =  X.getValue attrfor
getformat             =  X.getValue attrformat
getfrom               =  X.getValue attrfrom
getfunction           =  X.getValue attrfunction
getgenerated_by       =  X.getValue attrgenerated_by
getglobals            =  X.getValue attrglobals
getheight             =  X.getValue attrheight
gethex                =  X.getValue attrhex
gethiding             =  X.getValue attrhiding
gethref               =  X.getValue attrhref
getid                 =  X.getValue attrid
getinduced_by         =  X.getValue attrinduced_by
getinherits           =  X.getValue attrinherits
getjust_by            =  X.getValue attrjust_by
getkind               =  X.getValue attrkind
getlarg_group         =  X.getValue attrlarg_group
getlbrack             =  X.getValue attrlbrack
getlinks              =  X.getValue attrlinks
getlocal              =  X.getValue attrlocal
getlogic              =  X.getValue attrlogic
getmid                =  X.getValue attrmid
getname               =  X.getValue attrname
getomdoc              =  X.getValue attromdoc
getparent             =  X.getValue attrparent
getprecedence         =  X.getValue attrprecedence
getproofs             =  X.getValue attrproofs
getpto                =  X.getValue attrpto
getpto_version        =  X.getValue attrpto_version
getrank               =  X.getValue attrrank
getrarg_group         =  X.getValue attrrarg_group
getrbrack             =  X.getValue attrrbrack
getreplaces           =  X.getValue attrreplaces
getrequires           =  X.getValue attrrequires
getrole               =  X.getValue attrrole
getscheme             =  X.getValue attrscheme
getscope              =  X.getValue attrscope
getselect             =  X.getValue attrselect
getseparator          =  X.getValue attrseparator
getsize               =  X.getValue attrsize
getsort               =  X.getValue attrsort
getstyle              =  X.getValue attrstyle
getsystem             =  X.getValue attrsystem
gettheory             =  X.getValue attrtheory
getto                 =  X.getValue attrto
gettotal              =  X.getValue attrtotal
gettype               =  X.getValue attrtype
getverdict            =  X.getValue attrverdict
getversion            =  X.getValue attrversion
getvia                =  X.getValue attrvia
getwho                =  X.getValue attrwho
getwidth              =  X.getValue attrwidth
getxml_lang           =  X.getValue attrxml_lang
getxmlns              =  X.getValue attrxmlns
getxmlns_xsi          =  X.getValue attrxmlns_xsi
getxref               =  X.getValue attrxref
getxsi_schemaLocation =  X.getValue attrxsi_schemaLocation

-- ----------------------------------------
--
-- has attribute test filter

hasaction             :: XmlFilter
hasargstr             :: XmlFilter
hasassertion          :: XmlFilter
hasattributes         :: XmlFilter
hasbase               :: XmlFilter
hasbracket_style      :: XmlFilter
hascatalogue          :: XmlFilter
hascd                 :: XmlFilter
hasclassid            :: XmlFilter
hascodebase           :: XmlFilter
hascomment            :: XmlFilter
hascrossref_symbol    :: XmlFilter
hasdata               :: XmlFilter
hasdec                :: XmlFilter
hasdischarged_in      :: XmlFilter
haselement            :: XmlFilter
hasentailed_by        :: XmlFilter
hasentailed_by_thm    :: XmlFilter
hasentails            :: XmlFilter
hasentails_thm        :: XmlFilter
hasfixity             :: XmlFilter
hasfor                :: XmlFilter
hasformat             :: XmlFilter
hasfrom               :: XmlFilter
hasfunction           :: XmlFilter
hasgenerated_by       :: XmlFilter
hasglobals            :: XmlFilter
hasheight             :: XmlFilter
hashex                :: XmlFilter
hashiding             :: XmlFilter
hashref               :: XmlFilter
hasid                 :: XmlFilter
hasinduced_by         :: XmlFilter
hasinherits           :: XmlFilter
hasjust_by            :: XmlFilter
haskind               :: XmlFilter
haslarg_group         :: XmlFilter
haslbrack             :: XmlFilter
haslinks              :: XmlFilter
haslocal              :: XmlFilter
haslogic              :: XmlFilter
hasmid                :: XmlFilter
hasname               :: XmlFilter
hasomdoc              :: XmlFilter
hasparent             :: XmlFilter
hasprecedence         :: XmlFilter
hasproofs             :: XmlFilter
haspto                :: XmlFilter
haspto_version        :: XmlFilter
hasrank               :: XmlFilter
hasrarg_group         :: XmlFilter
hasrbrack             :: XmlFilter
hasreplaces           :: XmlFilter
hasrequires           :: XmlFilter
hasrole               :: XmlFilter
hasscheme             :: XmlFilter
hasscope              :: XmlFilter
hasselect             :: XmlFilter
hasseparator          :: XmlFilter
hassize               :: XmlFilter
hassort               :: XmlFilter
hasstyle              :: XmlFilter
hassystem             :: XmlFilter
hastheory             :: XmlFilter
hasto                 :: XmlFilter
hastotal              :: XmlFilter
hastype               :: XmlFilter
hasverdict            :: XmlFilter
hasversion            :: XmlFilter
hasvia                :: XmlFilter
haswho                :: XmlFilter
haswidth              :: XmlFilter
hasxml_lang           :: XmlFilter
hasxmlns              :: XmlFilter
hasxmlns_xsi          :: XmlFilter
hasxref               :: XmlFilter
hasxsi_schemaLocation :: XmlFilter

-- ----------------------------------------
--
-- 

hasaction             = X.hasAttr attraction
hasargstr             = X.hasAttr attrargstr
hasassertion          = X.hasAttr attrassertion
hasattributes         = X.hasAttr attrattributes
hasbase               = X.hasAttr attrbase
hasbracket_style      = X.hasAttr attrbracket_style
hascatalogue          = X.hasAttr attrcatalogue
hascd                 = X.hasAttr attrcd
hasclassid            = X.hasAttr attrclassid
hascodebase           = X.hasAttr attrcodebase
hascomment            = X.hasAttr attrcomment
hascrossref_symbol    = X.hasAttr attrcrossref_symbol
hasdata               = X.hasAttr attrdata
hasdec                = X.hasAttr attrdec
hasdischarged_in      = X.hasAttr attrdischarged_in
haselement            = X.hasAttr attrelement
hasentailed_by        = X.hasAttr attrentailed_by
hasentailed_by_thm    = X.hasAttr attrentailed_by_thm
hasentails            = X.hasAttr attrentails
hasentails_thm        = X.hasAttr attrentails_thm
hasfixity             = X.hasAttr attrfixity
hasfor                = X.hasAttr attrfor
hasformat             = X.hasAttr attrformat
hasfrom               = X.hasAttr attrfrom
hasfunction           = X.hasAttr attrfunction
hasgenerated_by       = X.hasAttr attrgenerated_by
hasglobals            = X.hasAttr attrglobals
hasheight             = X.hasAttr attrheight
hashex                = X.hasAttr attrhex
hashiding             = X.hasAttr attrhiding
hashref               = X.hasAttr attrhref
hasid                 = X.hasAttr attrid
hasinduced_by         = X.hasAttr attrinduced_by
hasinherits           = X.hasAttr attrinherits
hasjust_by            = X.hasAttr attrjust_by
haskind               = X.hasAttr attrkind
haslarg_group         = X.hasAttr attrlarg_group
haslbrack             = X.hasAttr attrlbrack
haslinks              = X.hasAttr attrlinks
haslocal              = X.hasAttr attrlocal
haslogic              = X.hasAttr attrlogic
hasmid                = X.hasAttr attrmid
hasname               = X.hasAttr attrname
hasomdoc              = X.hasAttr attromdoc
hasparent             = X.hasAttr attrparent
hasprecedence         = X.hasAttr attrprecedence
hasproofs             = X.hasAttr attrproofs
haspto                = X.hasAttr attrpto
haspto_version        = X.hasAttr attrpto_version
hasrank               = X.hasAttr attrrank
hasrarg_group         = X.hasAttr attrrarg_group
hasrbrack             = X.hasAttr attrrbrack
hasreplaces           = X.hasAttr attrreplaces
hasrequires           = X.hasAttr attrrequires
hasrole               = X.hasAttr attrrole
hasscheme             = X.hasAttr attrscheme
hasscope              = X.hasAttr attrscope
hasselect             = X.hasAttr attrselect
hasseparator          = X.hasAttr attrseparator
hassize               = X.hasAttr attrsize
hassort               = X.hasAttr attrsort
hasstyle              = X.hasAttr attrstyle
hassystem             = X.hasAttr attrsystem
hastheory             = X.hasAttr attrtheory
hasto                 = X.hasAttr attrto
hastotal              = X.hasAttr attrtotal
hastype               = X.hasAttr attrtype
hasverdict            = X.hasAttr attrverdict
hasversion            = X.hasAttr attrversion
hasvia                = X.hasAttr attrvia
haswho                = X.hasAttr attrwho
haswidth              = X.hasAttr attrwidth
hasxml_lang           = X.hasAttr attrxml_lang
hasxmlns              = X.hasAttr attrxmlns
hasxmlns_xsi          = X.hasAttr attrxmlns_xsi
hasxref               = X.hasAttr attrxref
hasxsi_schemaLocation = X.hasAttr attrxsi_schemaLocation

-- ----------------------------------------
--
-- make attribute nodes constructor filter for computed attribute values

afaction             :: XmlFilter -> XmlFilter
afargstr             :: XmlFilter -> XmlFilter
afassertion          :: XmlFilter -> XmlFilter
afattributes         :: XmlFilter -> XmlFilter
afbase               :: XmlFilter -> XmlFilter
afbracket_style      :: XmlFilter -> XmlFilter
afcatalogue          :: XmlFilter -> XmlFilter
afcd                 :: XmlFilter -> XmlFilter
afclassid            :: XmlFilter -> XmlFilter
afcodebase           :: XmlFilter -> XmlFilter
afcomment            :: XmlFilter -> XmlFilter
afcrossref_symbol    :: XmlFilter -> XmlFilter
afdata               :: XmlFilter -> XmlFilter
afdec                :: XmlFilter -> XmlFilter
afdischarged_in      :: XmlFilter -> XmlFilter
afelement            :: XmlFilter -> XmlFilter
afentailed_by        :: XmlFilter -> XmlFilter
afentailed_by_thm    :: XmlFilter -> XmlFilter
afentails            :: XmlFilter -> XmlFilter
afentails_thm        :: XmlFilter -> XmlFilter
affixity             :: XmlFilter -> XmlFilter
affor                :: XmlFilter -> XmlFilter
afformat             :: XmlFilter -> XmlFilter
affrom               :: XmlFilter -> XmlFilter
affunction           :: XmlFilter -> XmlFilter
afgenerated_by       :: XmlFilter -> XmlFilter
afglobals            :: XmlFilter -> XmlFilter
afheight             :: XmlFilter -> XmlFilter
afhex                :: XmlFilter -> XmlFilter
afhiding             :: XmlFilter -> XmlFilter
afhref               :: XmlFilter -> XmlFilter
afid                 :: XmlFilter -> XmlFilter
afinduced_by         :: XmlFilter -> XmlFilter
afinherits           :: XmlFilter -> XmlFilter
afjust_by            :: XmlFilter -> XmlFilter
afkind               :: XmlFilter -> XmlFilter
aflarg_group         :: XmlFilter -> XmlFilter
aflbrack             :: XmlFilter -> XmlFilter
aflinks              :: XmlFilter -> XmlFilter
aflocal              :: XmlFilter -> XmlFilter
aflogic              :: XmlFilter -> XmlFilter
afmid                :: XmlFilter -> XmlFilter
afname               :: XmlFilter -> XmlFilter
afomdoc              :: XmlFilter -> XmlFilter
afparent             :: XmlFilter -> XmlFilter
afprecedence         :: XmlFilter -> XmlFilter
afproofs             :: XmlFilter -> XmlFilter
afpto                :: XmlFilter -> XmlFilter
afpto_version        :: XmlFilter -> XmlFilter
afrank               :: XmlFilter -> XmlFilter
afrarg_group         :: XmlFilter -> XmlFilter
afrbrack             :: XmlFilter -> XmlFilter
afreplaces           :: XmlFilter -> XmlFilter
afrequires           :: XmlFilter -> XmlFilter
afrole               :: XmlFilter -> XmlFilter
afscheme             :: XmlFilter -> XmlFilter
afscope              :: XmlFilter -> XmlFilter
afselect             :: XmlFilter -> XmlFilter
afseparator          :: XmlFilter -> XmlFilter
afsize               :: XmlFilter -> XmlFilter
afsort               :: XmlFilter -> XmlFilter
afstyle              :: XmlFilter -> XmlFilter
afsystem             :: XmlFilter -> XmlFilter
aftheory             :: XmlFilter -> XmlFilter
afto                 :: XmlFilter -> XmlFilter
aftotal              :: XmlFilter -> XmlFilter
aftype               :: XmlFilter -> XmlFilter
afverdict            :: XmlFilter -> XmlFilter
afversion            :: XmlFilter -> XmlFilter
afvia                :: XmlFilter -> XmlFilter
afwho                :: XmlFilter -> XmlFilter
afwidth              :: XmlFilter -> XmlFilter
afxml_lang           :: XmlFilter -> XmlFilter
afxmlns              :: XmlFilter -> XmlFilter
afxmlns_xsi          :: XmlFilter -> XmlFilter
afxref               :: XmlFilter -> XmlFilter
afxsi_schemaLocation :: XmlFilter -> XmlFilter

-- ----------------------------------------
--
-- 

afaction             = X.mkXAttr attraction
afargstr             = X.mkXAttr attrargstr
afassertion          = X.mkXAttr attrassertion
afattributes         = X.mkXAttr attrattributes
afbase               = X.mkXAttr attrbase
afbracket_style      = X.mkXAttr attrbracket_style
afcatalogue          = X.mkXAttr attrcatalogue
afcd                 = X.mkXAttr attrcd
afclassid            = X.mkXAttr attrclassid
afcodebase           = X.mkXAttr attrcodebase
afcomment            = X.mkXAttr attrcomment
afcrossref_symbol    = X.mkXAttr attrcrossref_symbol
afdata               = X.mkXAttr attrdata
afdec                = X.mkXAttr attrdec
afdischarged_in      = X.mkXAttr attrdischarged_in
afelement            = X.mkXAttr attrelement
afentailed_by        = X.mkXAttr attrentailed_by
afentailed_by_thm    = X.mkXAttr attrentailed_by_thm
afentails            = X.mkXAttr attrentails
afentails_thm        = X.mkXAttr attrentails_thm
affixity             = X.mkXAttr attrfixity
affor                = X.mkXAttr attrfor
afformat             = X.mkXAttr attrformat
affrom               = X.mkXAttr attrfrom
affunction           = X.mkXAttr attrfunction
afgenerated_by       = X.mkXAttr attrgenerated_by
afglobals            = X.mkXAttr attrglobals
afheight             = X.mkXAttr attrheight
afhex                = X.mkXAttr attrhex
afhiding             = X.mkXAttr attrhiding
afhref               = X.mkXAttr attrhref
afid                 = X.mkXAttr attrid
afinduced_by         = X.mkXAttr attrinduced_by
afinherits           = X.mkXAttr attrinherits
afjust_by            = X.mkXAttr attrjust_by
afkind               = X.mkXAttr attrkind
aflarg_group         = X.mkXAttr attrlarg_group
aflbrack             = X.mkXAttr attrlbrack
aflinks              = X.mkXAttr attrlinks
aflocal              = X.mkXAttr attrlocal
aflogic              = X.mkXAttr attrlogic
afmid                = X.mkXAttr attrmid
afname               = X.mkXAttr attrname
afomdoc              = X.mkXAttr attromdoc
afparent             = X.mkXAttr attrparent
afprecedence         = X.mkXAttr attrprecedence
afproofs             = X.mkXAttr attrproofs
afpto                = X.mkXAttr attrpto
afpto_version        = X.mkXAttr attrpto_version
afrank               = X.mkXAttr attrrank
afrarg_group         = X.mkXAttr attrrarg_group
afrbrack             = X.mkXAttr attrrbrack
afreplaces           = X.mkXAttr attrreplaces
afrequires           = X.mkXAttr attrrequires
afrole               = X.mkXAttr attrrole
afscheme             = X.mkXAttr attrscheme
afscope              = X.mkXAttr attrscope
afselect             = X.mkXAttr attrselect
afseparator          = X.mkXAttr attrseparator
afsize               = X.mkXAttr attrsize
afsort               = X.mkXAttr attrsort
afstyle              = X.mkXAttr attrstyle
afsystem             = X.mkXAttr attrsystem
aftheory             = X.mkXAttr attrtheory
afto                 = X.mkXAttr attrto
aftotal              = X.mkXAttr attrtotal
aftype               = X.mkXAttr attrtype
afverdict            = X.mkXAttr attrverdict
afversion            = X.mkXAttr attrversion
afvia                = X.mkXAttr attrvia
afwho                = X.mkXAttr attrwho
afwidth              = X.mkXAttr attrwidth
afxml_lang           = X.mkXAttr attrxml_lang
afxmlns              = X.mkXAttr attrxmlns
afxmlns_xsi          = X.mkXAttr attrxmlns_xsi
afxref               = X.mkXAttr attrxref
afxsi_schemaLocation = X.mkXAttr attrxsi_schemaLocation

-- ----------------------------------------
--
-- make attribute nodes constructor filter for string attribute values

aaction             :: String -> XmlFilter
aargstr             :: String -> XmlFilter
aassertion          :: String -> XmlFilter
aattributes         :: String -> XmlFilter
abase               :: String -> XmlFilter
abracket_style      :: String -> XmlFilter
acatalogue          :: String -> XmlFilter
acd                 :: String -> XmlFilter
aclassid            :: String -> XmlFilter
acodebase           :: String -> XmlFilter
acomment            :: String -> XmlFilter
acrossref_symbol    :: String -> XmlFilter
adata               :: String -> XmlFilter
adec                :: String -> XmlFilter
adischarged_in      :: String -> XmlFilter
aelement            :: String -> XmlFilter
aentailed_by        :: String -> XmlFilter
aentailed_by_thm    :: String -> XmlFilter
aentails            :: String -> XmlFilter
aentails_thm        :: String -> XmlFilter
afixity             :: String -> XmlFilter
afor                :: String -> XmlFilter
aformat             :: String -> XmlFilter
afrom               :: String -> XmlFilter
afunction           :: String -> XmlFilter
agenerated_by       :: String -> XmlFilter
aglobals            :: String -> XmlFilter
aheight             :: String -> XmlFilter
ahex                :: String -> XmlFilter
ahiding             :: String -> XmlFilter
ahref               :: String -> XmlFilter
aid                 :: String -> XmlFilter
ainduced_by         :: String -> XmlFilter
ainherits           :: String -> XmlFilter
ajust_by            :: String -> XmlFilter
akind               :: String -> XmlFilter
alarg_group         :: String -> XmlFilter
albrack             :: String -> XmlFilter
alinks              :: String -> XmlFilter
alocal              :: String -> XmlFilter
alogic              :: String -> XmlFilter
amid                :: String -> XmlFilter
aname               :: String -> XmlFilter
aomdoc              :: String -> XmlFilter
aparent             :: String -> XmlFilter
aprecedence         :: String -> XmlFilter
aproofs             :: String -> XmlFilter
apto                :: String -> XmlFilter
apto_version        :: String -> XmlFilter
arank               :: String -> XmlFilter
ararg_group         :: String -> XmlFilter
arbrack             :: String -> XmlFilter
areplaces           :: String -> XmlFilter
arequires           :: String -> XmlFilter
arole               :: String -> XmlFilter
ascheme             :: String -> XmlFilter
ascope              :: String -> XmlFilter
aselect             :: String -> XmlFilter
aseparator          :: String -> XmlFilter
asize               :: String -> XmlFilter
asort               :: String -> XmlFilter
astyle              :: String -> XmlFilter
asystem             :: String -> XmlFilter
atheory             :: String -> XmlFilter
ato                 :: String -> XmlFilter
atotal              :: String -> XmlFilter
atype               :: String -> XmlFilter
averdict            :: String -> XmlFilter
aversion            :: String -> XmlFilter
avia                :: String -> XmlFilter
awho                :: String -> XmlFilter
awidth              :: String -> XmlFilter
axml_lang           :: String -> XmlFilter
axmlns              :: String -> XmlFilter
axmlns_xsi          :: String -> XmlFilter
axref               :: String -> XmlFilter
axsi_schemaLocation :: String -> XmlFilter

-- ----------------------------------------
--
-- 

aaction             = \ v -> X.mkXAttr attraction (X.txt v)
aargstr             = \ v -> X.mkXAttr attrargstr (X.txt v)
aassertion          = \ v -> X.mkXAttr attrassertion (X.txt v)
aattributes         = \ v -> X.mkXAttr attrattributes (X.txt v)
abase               = \ v -> X.mkXAttr attrbase (X.txt v)
abracket_style      = \ v -> X.mkXAttr attrbracket_style (X.txt v)
acatalogue          = \ v -> X.mkXAttr attrcatalogue (X.txt v)
acd                 = \ v -> X.mkXAttr attrcd (X.txt v)
aclassid            = \ v -> X.mkXAttr attrclassid (X.txt v)
acodebase           = \ v -> X.mkXAttr attrcodebase (X.txt v)
acomment            = \ v -> X.mkXAttr attrcomment (X.txt v)
acrossref_symbol    = \ v -> X.mkXAttr attrcrossref_symbol (X.txt v)
adata               = \ v -> X.mkXAttr attrdata (X.txt v)
adec                = \ v -> X.mkXAttr attrdec (X.txt v)
adischarged_in      = \ v -> X.mkXAttr attrdischarged_in (X.txt v)
aelement            = \ v -> X.mkXAttr attrelement (X.txt v)
aentailed_by        = \ v -> X.mkXAttr attrentailed_by (X.txt v)
aentailed_by_thm    = \ v -> X.mkXAttr attrentailed_by_thm (X.txt v)
aentails            = \ v -> X.mkXAttr attrentails (X.txt v)
aentails_thm        = \ v -> X.mkXAttr attrentails_thm (X.txt v)
afixity             = \ v -> X.mkXAttr attrfixity (X.txt v)
afor                = \ v -> X.mkXAttr attrfor (X.txt v)
aformat             = \ v -> X.mkXAttr attrformat (X.txt v)
afrom               = \ v -> X.mkXAttr attrfrom (X.txt v)
afunction           = \ v -> X.mkXAttr attrfunction (X.txt v)
agenerated_by       = \ v -> X.mkXAttr attrgenerated_by (X.txt v)
aglobals            = \ v -> X.mkXAttr attrglobals (X.txt v)
aheight             = \ v -> X.mkXAttr attrheight (X.txt v)
ahex                = \ v -> X.mkXAttr attrhex (X.txt v)
ahiding             = \ v -> X.mkXAttr attrhiding (X.txt v)
ahref               = \ v -> X.mkXAttr attrhref (X.txt v)
aid                 = \ v -> X.mkXAttr attrid (X.txt v)
ainduced_by         = \ v -> X.mkXAttr attrinduced_by (X.txt v)
ainherits           = \ v -> X.mkXAttr attrinherits (X.txt v)
ajust_by            = \ v -> X.mkXAttr attrjust_by (X.txt v)
akind               = \ v -> X.mkXAttr attrkind (X.txt v)
alarg_group         = \ v -> X.mkXAttr attrlarg_group (X.txt v)
albrack             = \ v -> X.mkXAttr attrlbrack (X.txt v)
alinks              = \ v -> X.mkXAttr attrlinks (X.txt v)
alocal              = \ v -> X.mkXAttr attrlocal (X.txt v)
alogic              = \ v -> X.mkXAttr attrlogic (X.txt v)
amid                = \ v -> X.mkXAttr attrmid (X.txt v)
aname               = \ v -> X.mkXAttr attrname (X.txt v)
aomdoc              = \ v -> X.mkXAttr attromdoc (X.txt v)
aparent             = \ v -> X.mkXAttr attrparent (X.txt v)
aprecedence         = \ v -> X.mkXAttr attrprecedence (X.txt v)
aproofs             = \ v -> X.mkXAttr attrproofs (X.txt v)
apto                = \ v -> X.mkXAttr attrpto (X.txt v)
apto_version        = \ v -> X.mkXAttr attrpto_version (X.txt v)
arank               = \ v -> X.mkXAttr attrrank (X.txt v)
ararg_group         = \ v -> X.mkXAttr attrrarg_group (X.txt v)
arbrack             = \ v -> X.mkXAttr attrrbrack (X.txt v)
areplaces           = \ v -> X.mkXAttr attrreplaces (X.txt v)
arequires           = \ v -> X.mkXAttr attrrequires (X.txt v)
arole               = \ v -> X.mkXAttr attrrole (X.txt v)
ascheme             = \ v -> X.mkXAttr attrscheme (X.txt v)
ascope              = \ v -> X.mkXAttr attrscope (X.txt v)
aselect             = \ v -> X.mkXAttr attrselect (X.txt v)
aseparator          = \ v -> X.mkXAttr attrseparator (X.txt v)
asize               = \ v -> X.mkXAttr attrsize (X.txt v)
asort               = \ v -> X.mkXAttr attrsort (X.txt v)
astyle              = \ v -> X.mkXAttr attrstyle (X.txt v)
asystem             = \ v -> X.mkXAttr attrsystem (X.txt v)
atheory             = \ v -> X.mkXAttr attrtheory (X.txt v)
ato                 = \ v -> X.mkXAttr attrto (X.txt v)
atotal              = \ v -> X.mkXAttr attrtotal (X.txt v)
atype               = \ v -> X.mkXAttr attrtype (X.txt v)
averdict            = \ v -> X.mkXAttr attrverdict (X.txt v)
aversion            = \ v -> X.mkXAttr attrversion (X.txt v)
avia                = \ v -> X.mkXAttr attrvia (X.txt v)
awho                = \ v -> X.mkXAttr attrwho (X.txt v)
awidth              = \ v -> X.mkXAttr attrwidth (X.txt v)
axml_lang           = \ v -> X.mkXAttr attrxml_lang (X.txt v)
axmlns              = \ v -> X.mkXAttr attrxmlns (X.txt v)
axmlns_xsi          = \ v -> X.mkXAttr attrxmlns_xsi (X.txt v)
axref               = \ v -> X.mkXAttr attrxref (X.txt v)
axsi_schemaLocation = \ v -> X.mkXAttr attrxsi_schemaLocation (X.txt v)

-- ----------------------------------------
--
-- end of module DTDomdoc

