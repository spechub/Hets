{- |
Module      :  $Header$
Description :  Abstract syntax for Constraint Satisfaction Problems
Copyright   :  (c) Tilman Thiry, Uni Freiburg 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  thiry@informatik.uni-freiburg.de
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for constraint satisfaction problems
-}




import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.AS_Annotation as AS_Anno


type DOMAIN_ID   = Id.Token
type RELATION_ID = Id.Token
type ELEMENT_ID  = Id.Token
type VARIABLE_ID = Id.Token

                            

data CONSTRAINT = Atomic_Constraint RELATION_ID [VARIABLE_ID] Id.Range
                deriving Show
                         
data TASK = Solve_satisfy


data FORMULA =
       Constraint CONSTRAINT 
     | Task TASK


data BASIC_ITEMS = 
      Domain_item DOMAIN_ID [ELEMENT_ID] Id.Range
      -- case of Domain declaration
    | Relation_item RELATION_ID [DOMAIN_ID] Id.Range
      -- case of relation declaration
    | Definition_item RELATION_ID [[ELEMENT_ID]] Id.Range
      -- case of relation definition
    | Variable_item [VARIABLE_ID] DOMAIN_ID Id.Range
      -- case of variable declaration
    |  Axiom_items [AS_Anno.Annoted (FORMULA)]
