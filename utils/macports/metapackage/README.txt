Welcome to the HETS Metapackage.

This Installation Package will install HETS and some runtime dependencies to your system. It is being created from MacPorts (<http://www.macports.org/>) but it doesn't require MacPorts to be installed.

-- I don't use MacPorts.
If you don't have MacPorts installed, you need to set your PATH environment correctly. To do so, please run hets-path.sh in the same directory.

-- What if I already use MacPorts?
In case you already have MacPorts installed, this package might overwrite installed versions of your software. This is a known bug.

You can deselect conflicting packages in "Custom Install". (Click "Customize" in "Installation Type".)

Should this already have happened, not all is lost:
Just 'sudo port deactivate <overwritten package> && sudo port activate <overwritten package>  @<version>', that should restore your installed version. (To determine the version do 'port list <overwritten package>', you will most likely want the highest one.)
In case your version should be lower than the version installed by this Metapackage, HETS might or might not run.

-- Isabelle
To install Isabelle, please refer to <http://www.cl.cam.ac.uk/research/hvg/Isabelle/download.html>.

-- SPASS
For a SPASS binary, please refer to <http://www.spass-prover.org/download/index.html>.