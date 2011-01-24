#use "/home/sternk/Hets/HolLight/OcamlTools/overload_loadfile.ml";;

use_file "/home/sternk/binom/binom.ml";;
#use "/home/sternk/Hets/HolLight/OcamlTools/export.ml";;
export_sig_sen_to_file (get_libs()) "/home/sternk/Hets/HolLight/example_binom.hol";;
