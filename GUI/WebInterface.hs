


-- translate to Haskell
fun mapstring  s =
case s of
   "0" => 0
 | "1" => 1
 | "2" => 2
 | "3" => 3
 | "4" => 4
 | "5" => 5
 | "6" => 6
 | "7" => 7
 | "8" => 8
 | "9" => 9
 |"a" => 10
 |"b" => 11
 |"c" => 12
 |"d" => 13
 |"e" => 14
 |"f" => 15
 |"A" => 10
 |"B" => 11
 |"C" => 12
 |"D" => 13
 |"E" => 14
 |"F" => 15
 | s =>  ord(s);


fun  convert_cgi [] = []
|   convert_cgi ("%"::"0"::"D"::s) = convert_cgi s
|   convert_cgi ("%"::s1::s2::rest) = (chr( (mapstring s1) * 16 + mapstring s2)::convert_cgi rest)
|   convert_cgi ("+"::s) = ((" "::(convert_cgi s)))
|   convert_cgi (s::s1) = s::convert_cgi s1

fun convert_arg (_,("s"::"p"::"e"::"c"::"="::s)) =
    implode (convert_cgi s)
  | convert_arg (arg,_) = arg
    
      

-- translate to Haskell

webInterface :: String -> IO()

fun web_interface s =
let val args = scanwords (fn a => not (a="&")) (explode s@["&"])
    val del_blank = implode o (filter_out is_blank) o explode
    val args' = map del_blank args
-- the following line must be adapted, construct a value of type HetcatsOpts
    val pars = ("tree=yes" mem args',"env=yes" mem args',"tex=yes" mem args')
    val sp = foldl convert_arg ("",map explode args')
-- the following line must be adpated to Hets, see hets.hs or Static/AnalysisLibrary.hs
    val res =  parse_and_check (!basic_lib_env) (fn x => ()) true sp
               handle exn => (empty_lib_env,empty_global_env,empty_lib_defn)
in  
    web_interface_aux1 pars res
end

and web_interface_aux1 (show_trees,show_env,latex) (_,genv,trees) =

    ( 
      if show_trees then
      -- use showPretty instead of print
        (print (print_heading true "Parse tree");
         print (AT.mkA (trees)) )
     else ()
     handle exn => print ("Internal error #2. Please send us your specification");
     if show_env then
        (print (print_heading true "Global Environment");
         print (format_text HTML_pre (StructuredPrint.print_global_env genv trees))
        )
     else ();
     if latex then
        (print (print_heading true "LaTeX code");
         (*print (format_text HTML_pre (Makellos.mkTeX (true,genv,trees)) ) *)
         print (format_text HTML_pre "Sorry, not LaTeX output yet. Use CATS 0.56")
        )
     else ()
    )

