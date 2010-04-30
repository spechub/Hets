#!/bin/sh

# Setting uDrawGraph
export UDG_HOME=/usr/local/uDrawGraph-3.1
export PATH=$UDG_HOME/bin:$PATH
export UNIDAVINCI=$UDG_HOME/bin/uDrawGraph

# Setting Hets-lib
export HETS_LIB=/root/Hets-lib
export HETS_ISABELLE_LIB=$HETS_LIB/Isabelle

# Setting Isabelle
export PATH=/usr/local/Isabelle/bin:$PATH

# Setting OWL-Tools
export HETS_OWL_TOOLS=/usr/local/Hets/hets-owl-tools
export HETS_APROVE=$HETS_OWL_TOOLS/AProVE.jar
export HETS_ONTODMU=$HETS_OWL_TOOLS/OntoDMU.jar

# Setting Pellet
export PELLET_PATH=/usr/local/pellet
