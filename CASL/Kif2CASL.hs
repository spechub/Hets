{- |
Module      :  $Header$
Copyright   :  (c) T.Mossakowski, C.Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Parsing lists of lists being MILO (MId-Level Ontology) .kif files
-}

module CASL.Kif2CASL where

import Common.Id
import Common.AS_Annotation
import qualified Text.PrettyPrint.HughesPJ as Doc
import CASL.Kif
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Logic_CASL

string2Id :: String -> Id
string2Id s = mkId [mkSimpleId s]

-- | the universal sort
universe :: SORT
universe = string2Id "U"

-- | translation of formulas
kif2CASLFormula :: ListOfList -> CASLFORMULA
kif2CASLFormula (List (Literal KToken "and" : phis)) =
  Conjunction (map kif2CASLFormula phis) nullRange
kif2CASLFormula (List (Literal KToken "or" : phis)) =
  Disjunction (map kif2CASLFormula phis) nullRange
kif2CASLFormula (List [Literal KToken "=>", phi1, phi2]) =
  Implication (kif2CASLFormula phi1) (kif2CASLFormula phi2) True nullRange
kif2CASLFormula (List [Literal KToken "<=>", phi1, phi2]) =
  Equivalence (kif2CASLFormula phi1) (kif2CASLFormula phi2) nullRange
kif2CASLFormula (List [Literal KToken "True"]) =
  True_atom nullRange
kif2CASLFormula (List [Literal KToken "False"]) =
  False_atom nullRange
kif2CASLFormula (List [Literal KToken "exists", List vl, phi]) =
  Quantification Existential (kif2CASLvardeclList vl) (kif2CASLFormula phi) nullRange
kif2CASLFormula (List [Literal KToken "forall", List vl, phi]) =
  Quantification Universal (kif2CASLvardeclList vl) (kif2CASLFormula phi) nullRange
kif2CASLFormula (List (Literal KToken p:rest)) =
  Predication (Pred_name (string2Id p)) (map kif2CASLTerm rest) nullRange
kif2CASLFormula x = error ("kif2CASLFormula : cannot translate" ++
                       show (ppListOfList x))

kif2CASLTerm :: ListOfList -> TERM ()
kif2CASLTerm (Literal QWord v) = Simple_id (mkSimpleId v)
kif2CASLTerm (Literal _ s) = Simple_id (mkSimpleId s)
kif2CASLTerm (List (Literal _ f:args)) =
  Application (Op_name (string2Id f)) (map kif2CASLTerm args) nullRange
kif2CASLTerm x = error ("kif2CASLTerm : cannot translate" ++
                       show (ppListOfList x))


-- | translation of variable declaration lists
kif2CASLvardeclList :: [ListOfList] -> [VAR_DECL]
kif2CASLvardeclList = map kif2CASLvardecl

-- | translation of variable declarations
kif2CASLvardecl :: ListOfList -> VAR_DECL
kif2CASLvardecl l = case l of  
    Literal _ v -> Var_decl [mkSimpleId (tail v)] universe nullRange
    _ -> error $ "kif2CASLvardecl " ++ show (ppListOfList l)

-- | first pass of translation, just collecting the formulas
kif2CASLpass1 :: [ListOfList] -> [Annoted CASLFORMULA]
kif2CASLpass1 [] = []
kif2CASLpass1 (phi:rest) =
  Annoted { item = phi', opt_pos = nullRange, l_annos = [], r_annos = annos }
    : kif2CASLpass1 rest'
  where phi' = kif2CASLFormula phi
        (annos,rest') = skipComments [] rest

-- | chech for comment
isKifComment (List (Literal KToken "documentation":_)) = True
isKifComment _ = False

-- | convert comment to annotation
toAnno :: ListOfList -> Annotation
toAnno (List (_:l)) = 
  Unparsed_anno Comment_start 
    (Group_anno [show $ Doc.vcat $ map ppListOfList l]) nullRange
toAnno _ = error "Kif2CASL.toAnno: wrong format of comment"

-- | skip the first comments; they belong to the whole file
skipComments :: [Annotation] -> [ListOfList] -> ([Annotation], [ListOfList])
skipComments acc [] = (reverse acc,[])
skipComments acc l@(x:rest) = 
  if isKifComment x 
   then skipComments (toAnno x:acc) rest
   else (reverse acc,l)

-- | main translation function
kif2CASL :: [ListOfList] -> (Sign () (),[Annoted CASLFORMULA])
kif2CASL l = (emptySign (),phis)
  where (ans,rest) = skipComments [] l
        phis = kif2CASLpass1 rest
