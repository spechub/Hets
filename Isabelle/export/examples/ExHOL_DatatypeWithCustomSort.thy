theory ExHOL_DatatypeWithCustomSort
imports Datatype
begin

class s1

setup {* Sign.set_defsort @{sort s1} *}

datatype 'a foo = Bar 'a

setup {* Sign.set_defsort @{sort type} *}

ML {*
 val sorts = #sorts (Option.valOf (Datatype.get_info @{theory} @{type_name foo}));
*}

end
