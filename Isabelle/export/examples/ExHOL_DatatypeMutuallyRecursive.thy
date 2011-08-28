theory ExHOL_DatatypeMutuallyRecursive
 
imports Datatype 

begin

datatype type1 =
       foo |
       bar type2
and type2 = "nat * type1"

end
