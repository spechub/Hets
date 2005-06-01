import Proofs.Proofs
import Common.ATerm.Lib
import Comorphisms.LogicGraph
import Logic.Logic

instance ShATermConvertible BasicProof where
     toShATerm att0 (BasicProof lid p) = 
	 case toShATerm att0 (language_name lid) of { (att1,i1) ->
         case toShATerm att1 p of { (att2,i2) ->
            addATerm (ShAAppl "BasicProof" [i1,i2] []) att2}}
     toShATerm att0 Guessed =
         case toShATerm att0 (show Guessed) of { (att1, i1) ->
            addATerm (ShAAppl "BasicProof" [i1] []) att1}
     toShATerm att0 Conjectured =
         case toShATerm att0 (show Conjectured) of { (att1, i1) ->
            addATerm (ShAAppl "BasicProof" [i1] []) att1}
     toShATerm att0 Handwritten =
         case toShATerm att0 (show Handwritten) of { (att1, i1) ->
            addATerm (ShAAppl "BasicProof" [i1] []) att1}

     fromShATerm att = 
         case aterm of
	    (ShAAppl "BasicProof" [i1,i2] _) ->
	       case fromShATerm (getATermByIndex1 i1 att) of { i1' ->
               case getATermByIndex1 i2 att of { att' ->
               case lookupLogic_in_LG 
                        ("ShATermConvertible BasicProof") i1'  of {
                    Logic lid -> (BasicProof lid (fromShATerm att'))}}}
            v@(ShAAppl "BasicProof" [i1] _) ->
               case fromShATerm (getATermByIndex1 i1 att) of { i1' ->
               case i1' of
                 "Guessed" -> Guessed
                 "Conjectured" -> Conjectured
                 "Handwritten" -> Handwritten
                 _ -> fromShATermError "BasicProof" v}
	    u     -> fromShATermError "BasicProof" u
         where
         aterm = getATerm att

