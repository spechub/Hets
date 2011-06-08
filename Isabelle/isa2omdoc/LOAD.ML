val explode = SML90.explode;
val implode = SML90.implode;
val foldl = List.foldl;
fun known_thy name = List.exists (fn s1 => 
      case String.compare(s1,name) of 
           EQUAL => true
         | _ => false            ) (Thy_Info.get_names());

use "utility.ML";
use "CDLookup.ML";
use "ParseTyp.ML";
use "ParseTerm.ML";
use "ThyToOMDoc.ML";
val p = ThyToOMDoc.ParseTheory;
