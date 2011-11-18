exception EnvError of string;;
let getenv env_var =
 try Sys.getenv env_var
 with Not_found -> raise (EnvError (Printf.sprintf "Couldn't find env variable %s" env_var));;
let hol_dir = getenv "HETS_HOL_DIR";;
let ocaml_source_dir = getenv "HETS_OCAML_LIB_DIR";;
let ocaml_tools_dir = getenv "HETS_HOLLIGHT_TOOLS";;
let use_file' s =
  if Toploop.use_file Format.std_formatter s then ()
  else (Format.print_string("Error in included file "^s);
        Format.print_newline());;

use_file' (Filename.concat ocaml_tools_dir "overload_loadfile.ml");;
use_file "hol.ml";;

use_file' (Filename.concat ocaml_tools_dir "export_helper.ml");;

let argv = Sys.argv;;
let f = Array.get argv 1;;
let e = Array.get argv 2;;
inject_hol_include f;;
(*use_file f;;*)
export_libs (get_libs()) e;;
