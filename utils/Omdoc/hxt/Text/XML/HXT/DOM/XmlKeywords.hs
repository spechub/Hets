-- |
-- constants for XML keywords, for special attribute names
-- and special attribute values
--
-- Version : $Id$

module Text.XML.HXT.DOM.XmlKeywords
where

-- ------------------------------------------------------------
--
-- string constants for representing DTD keywords and attributes

t_xml,				-- tag names
 t_root		:: String

a_canonicalize,
 a_default,			-- attribute names
 a_check_namespaces,
 a_contentLength,
 a_collect_errors,
 a_default_baseuri,
 a_do_not_canonicalize,
 a_do_not_check_namespaces,
 a_do_not_issue_errors,
 a_do_not_issue_warnings,
 a_do_not_preserve_comment,
 a_do_not_remove_whitespace,
 a_do_not_use_curl,
 a_do_not_validate,
 a_encoding,
 a_error,
 a_error_log,
 a_help,
 a_indent,
 a_issue_errors,
 a_issue_warnings,
 a_kind,
 a_module,
 a_modifier,
 a_name,
 a_options_curl,
 a_output_encoding,
 a_output_file,
 a_output_xml,
 a_parse_html,
 a_parse_xml,
 a_peref,
 a_preserve_comment,
 a_propagate_errors,
 a_proxy,
 a_remove_whitespace,
 a_show_haskell,
 a_show_tree,
 a_source,
 a_status,
 a_standalone,
 a_trace,
 a_type,
 a_use_curl,
 a_url,
 a_validate,
 a_value,
 a_verbose,
 a_version,
 a_process_dtd :: String

v_0,				-- attribute values
 v_1,
 v_yes,
 v_no,
 v_any,
 v_children,
 v_choice,
 v_empty,
 v_mixed,
 v_seq,
 v_null,
 v_option,
 v_pcdata,
 v_star,
 v_plus		:: String

k_any,				-- DTD keywords
 k_cdata,
 k_empty,
 k_enitity,
 k_entities,
 k_id,
 k_idref,
 k_idrefs,
 k_include,
 k_ignore,
 k_nmtoken,
 k_nmtokens,
 k_peref,
 k_public,
 k_system,
 k_enumeration,
 k_fixed,
 k_implied,
 k_ndata,
 k_notation,
 k_pcdata,
 k_required,
 k_default	:: String

-- ------------------------------------------------------------

t_xml		= "xml"
t_root		= "/"		-- name of root node tag

a_canonicalize			= "canonicalize"
a_check_namespaces		= "check-namespaces"
a_collect_errors		= "collect-errors"
a_contentLength			= "Content-Length"
a_default			= "default"
a_default_baseuri		= "default-base-URI"
a_do_not_canonicalize		= "do-not-canonicalize"
a_do_not_check_namespaces	= "do-not-check-namespaces"
a_do_not_issue_errors		= "do-not-issue-errors"
a_do_not_issue_warnings		= "do-not-issue-warnings"
a_do_not_preserve_comment	= "do-not-preserve-comment"
a_do_not_remove_whitespace	= "do-not-remove-whitespace"
a_do_not_use_curl		= "do-not-use-curl"
a_do_not_validate		= "do-not-validate"
a_encoding			= "encoding"
a_error				= "error"
a_error_log			= "errorLog"
a_help				= "help"
a_indent			= "indent"
a_issue_warnings		= "issue-warnings"
a_issue_errors			= "issue-errors"
a_kind				= "kind"
a_module			= "module"
a_modifier			= "modifier"
a_name				= "name"
a_options_curl			= "options-curl"
a_output_file			= "output-file"
a_output_encoding		= "output-encoding"
a_output_xml			= "output-xml"
a_parse_html			= "parse-html"
a_parse_xml			= "parse-xml"
a_peref				= k_peref
a_preserve_comment 		= "preserve-comment"
a_propagate_errors		= "propagate-errors"
a_proxy				= "proxy"
a_remove_whitespace 		= "remove-whitespace"
a_show_haskell			= "show-haskell"
a_show_tree			= "show-tree"
a_source			= "source"
a_standalone			= "standalone"
a_status			= "status"
a_trace				= "trace"
a_type				= "type"
a_url				= "url"
a_use_curl			= "use-curl"
a_validate			= "validate"
a_value				= "value"
a_verbose			= "verbose"
a_version			= "version"
a_process_dtd		= "process-dtd"

v_yes		= "yes"
v_no		= "no"
v_1		= "1"
v_0		= "0"

v_any		= k_any
v_children	= "children"
v_choice	= "choice"
v_empty		= k_empty
v_pcdata	= k_pcdata
v_mixed		= "mixed"
v_seq		= "seq"

v_null		= ""
v_option	= "?"
v_star		= "*"
v_plus		= "+"

k_any		= "ANY"
k_cdata		= "CDATA"
k_empty		= "EMPTY"
k_enitity	= "ENTITY"
k_entities	= "ENTITIES"
k_id		= "ID"
k_idref		= "IDREF"
k_idrefs	= "IDREFS"
k_include	= "INCLUDE"
k_ignore	= "IGNORE"
k_nmtoken	= "NMTOKEN"
k_nmtokens	= "NMTOKENS"
k_peref		= "PERef"
k_public	= "PUBLIC"
k_system	= "SYSTEM"

k_enumeration	= "#ENUMERATION"
k_fixed		= "#FIXED"
k_implied	= "#IMPLIED"
k_ndata		= "NDATA"
k_notation	= "NOTATION"
k_pcdata	= "#PCDATA"
k_required	= "#REQUIRED"
k_default	= "#DEFAULT"


-- ------------------------------------------------------------
--

-- attribute names for transfer protocol attributes
-- used in XmlInput for describing header information
-- of http and other requests

transferPrefix
 , transferProtocol
 , transferMimeType
 , transferEncoding
 , transferURI
 , transferDefaultURI
 , transferStatus
 , transferMessage
 , transferVersion :: String

transferPrefix		= "transfer-"

transferProtocol	= transferPrefix ++ "Protocol"
transferVersion		= transferPrefix ++ "Version"
transferMimeType	= transferPrefix ++ "MimeType"
transferEncoding	= transferPrefix ++ "Encoding"
transferDefaultURI	= transferPrefix ++ "DefaultURI"
transferStatus		= transferPrefix ++ "Status"
transferMessage		= transferPrefix ++ "Message"
transferURI		= transferPrefix ++ "URI"

-- ------------------------------------------------------------
--

httpPrefix	:: String
httpPrefix	= "http-"

-- ------------------------------------------------------------
--
-- encoding names

isoLatin1, usAscii, ucs2, utf8, utf16, utf16be, utf16le	:: String

isoLatin1	= "ISO-8859-1"
usAscii		= "US-ASCII"
ucs2		= "ISO-10646-UCS-2"
utf8		= "UTF-8"
utf16		= "UTF-16"
utf16be		= "UTF-16BE"
utf16le		= "UTF-16LE"

-- ------------------------------------------------------------
