{- |
Description :  logic CSL for computer algebra systems
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt

The "CSL" folder contains the skeleton of
an instance of "Logic.Logic" for the logic EnCL used for computer algebra systems, see
Dominik Dietrich, Lutz Schröder, and Ewaryst Schulz:
Formalizing and Operationalizing Industrial Standards.
D. Giannakopoulou and F. Orejas (Eds.): FASE 2011, LNCS 6603, pp. 81–95, 2011.

Industrial standards establish technical criteria for various engineering artifacts, materials, or services, with a view to ensuring their functionality, safety, and reliability. We develop a methodology and tools to systematically formalize such standards, in particular their domain specific calculation methods, in order to support the automatic verification of functional properties for concrete physical artifacts. We approach this problem in the setting of the Bremen heterogeneous tool set Hets, which allows for the integrated use of a wide range of generic and custom-made logics. Specifically, we (i) design a domain specific language for the formalization of industrial standards; (ii) formulate a semantics of this language in terms of a translation into the higher-order specification language HasCasl, and (iii) integrate computer algebra systems (CAS) with the Hets framework via a generic CAS-Interface in order to execute explicit and implicit calculations specified in the standard. This enables a wide variety of added-value services based on formal reasoning, including verification of parameterized designs and simplification of standards for particular configurations. We illustrate our approach using the European standard EN 1591, which concerns calculation methods for gasketed flange connections that assure the impermeability and mechanical strength of the flange-bolt-gasket system.

-}

module CSL where
