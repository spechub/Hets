theory ExHOL_DatatypeMutuallyRecursive
 
imports Datatype 

begin

datatype (type4) type1 =
       foo |
       bar type2
and type2 = "nat * type1"
and type3 = "nat * type2"

end
