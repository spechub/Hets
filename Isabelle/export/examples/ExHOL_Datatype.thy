theory ExHOL_Datatype
 
imports Datatype 

begin

text {*
 The Datatype-Package (http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype)

 The following is a definition introduces the datatype "list" which

 * has an alias list1 which is used for the generated theorems
   Note:
    There is only ever one alias as per the additional outer Syntax introduced by the package
     cf. parse_datatype_decl (http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype.ML#l736)
         which is registered as the parser of the outer syntax command "datatype": http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype.ML#l746
    
    The alias ends up in #alt_names of http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_aux.ML#l16:
     cf. datatype_cmd (http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype.ML#l724)
         which is registered as handler for the parsed data: http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype.ML#l746
	 and passes the data to mk_dt_info (http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_data.ML#l271)
	  cf. gen_add_datatype (http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype.ML#l645
               http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype.ML#l718
                derive_datatype_props (http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_data.ML#l295)
                 http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_data.ML#l324
    In 2010 there was a discussion about the merits of these aliases since nobody in the core distribution seems to be using them (http://www.mail-archive.com/isabelle-dev@mailbroy.informatik.tu-muenchen.de/msg01128.html), but seems that they'll continue to be part of the syntax.
 * is paramtrized over two type variables 'a and 'b
   Note:
    The type variables end up in #sorts of http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype_aux.ML#l16:
     cf. the above and 
    There can be any number of type variables
     cf. http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/Pure/Isar/parse.ML#l267
         http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/Pure/Isar/parse.ML#l262
    Of course, from a practical point of view, the type variable 'b does not add any value. It was only added for demonstration purposes.
    The sort probably almost always is "HOL.type" since there is no way of attaching a different sort than the default sort of the sign of the current theory
     cf. http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/HOL/Tools/Datatype/datatype.ML#l703
    Nonetheless an indirect approach making use of set_defsort (http://isabelle.in.tum.de/repos/isabelle/file/6d736d983d5c/src/Pure/sign.ML#l201) works (see ExampleHOL_DatatypeWithCustomSort.thy for a demonstration) and can be used to achieve a different "default sort" for every single definition. Thus simply ignoring the attached sorts is not a fully safe approach.
 * defines a special syntax ("[]" for the empty list and the infixr operator "#" for list building)
   Note:
    This is not specific to the Datatype-Package and applies to all kinds of definitions of constants. Thus it is dealt with in another section.

*}

datatype (list1) ('a,'b) list = Nil ("[]")
                   | Cons 'a "('a,'b) list" (infixr "#" 65)

end
