module DevGraph where

import Grothendieck

data DGNode = DGNode {
              dgn_name :: String,
              dgn_sign :: G_sign,
              dgn_sens :: [(String,G_sentence)],
              dgn_external :: Bool }
            
data DGLink = DGLink {
              dgl_name :: String,
              dgl_src, dgl_tar :: DGNode,
              dgl_morphism :: G_morphism,
              dgl_type :: DGLinkType }


data DGLinkType = LocalDef 
            | GlobalDef
            | HidingDef
            | LocalThm Bool  -- is_proved
            | GlobalThm Bool  -- is_proved
            | HidingThm G_morphism Bool  -- reduction mor, is_proved
              -- DGLink S1 S2 m2 (DGLinkType m1 p) n
              -- corresponds to a span of morphisms
              -- S1 <--m1-- S --m2--> S2

data DGraph = DGraph [DGNode] [DGLink]
