exception EnvError of string;;
let getenv env_var =
 try Sys.getenv env_var
 with Not_found -> raise (EnvError (Printf.sprintf "Couldn't find env variable %s" env_var));;
let hol_dir = getenv "HETS_HOL_DIR";;
let ocaml_source_dir = getenv "HETS_OCAML_LIB_DIR";;
let ocaml_tools_dir = (Sys.getcwd ())^"/";;
#use "overload_loadfile.ml";;
use_file "hol.ml";;

use_file (ocaml_tools_dir^"export_helper.ml");;

let argv = Sys.argv;;
let f = Array.get argv 1;;
let e = Array.get argv 2;;
inject_hol_include f;;
Sys.chdir ocaml_tools_dir;;
use_file f;;
export_libs (get_libs()) e;;
