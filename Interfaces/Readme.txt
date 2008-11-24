
 There are datastructures and functions that are 
 shared between interfaces (PGIP and GUI). For example
 history should be stored in the same way by both , so 
 that one could in principle switch from one to the other.
 Also there is code that gets duplicated just because 
 both PGIP and GUI need it and the interfaces should be 
 independent one from the other. This folder will contain
 all common functions / datastructures. 

 Initially I wanted to make a new interface (abstract interface)
 that would do history management and report all results through
 strings. The above interfaces would just use this interface
 to transform the development graph, and use the string to 
 find out results about the commands. But I noticed that 
 GUI and PGIP are so different in how they function this 
 would imply altering to much both interfaces, and decided
 just to have common datastructures and functions that could
 be shared.

 Note that PGIP interface is done so that it can support any  
 other type of interface that comunicates through text ( for 
 example remotely through xml blocks send between user/hets, 
 through files that contains commands .. etc.)


 Razvan (r.pascanu@jacobs-university.de)
