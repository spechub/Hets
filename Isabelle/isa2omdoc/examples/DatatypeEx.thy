theory DatatypeEx 
imports Main
begin

datatype NN = S NN | Z

end

(*
ML{*

val t=  ThyInfo.get_theory "DatatypeEx";
val dts= DatatypePackage.get_datatypes t;
val keys= Symtab.keys dts;
Symtab.lookup dts "DatatypeEx.NN";

*}


*)
