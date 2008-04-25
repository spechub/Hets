In this document the usage of pellet in hets will be introduced.

1. The Setup of pellet:
   1.1. Download the current version of pellet from http://pellet.owldl.com/download;
   1.2. The pellet.x.zip (x is the version number) should be extracted in a directory (e.g. ~/utility/pellet);
   1.3. An environment variable $PELLET_PATH should be setup onto the directory which built in the step 1.2. (e.g. export PELLET_PATH=~/utility/pellet);

2. Consistent checking with pellet in Hets:
   2.1. Run the hets GUI with OWL ontology;
   2.2. Right click on a node which you want to check the consistency, and then choose the "consistent check" in pop-up menu;
   2.3. A message window with "Pellet not found" means the setup of the environment variable $PELLET_PATH was not correct;
   2.4. After a successful call of pellet comes a message window with either "This ontology is consistent" or "This ontology is not consistent". The ontology which is produced by the renderer, is displayed in another window.

3. Prove with Pellet:
   Coming soon.....

