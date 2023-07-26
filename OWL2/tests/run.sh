#!/bin/ksh93

SD=$( cd ${ dirname $0; }; printf "$PWD" )
BD=${SD%/*/*}

. ${BD}/Common/test/checkFunctions.sh

# don't wanna see stack traces
export HETS_OWL_TOOLS=${BD}/OWL2 HETS_LOG_LEVEL=SEVERE

cd ${SD}

for F in ~(N)${SD}/*.rdf ; do
	print "(1) Checking $F ..."
	java -jar ${HETS_OWL_TOOLS}/OWL2Parser.jar file://$F $F.omnm || addErr
done

for F in ~(N)${SD}/*.rdf ; do
	print "(2) Checking $F ..."
	${BD}/hets -v2 -i owl -o th,pp.dol,omn $F || addErr
done

for F in ~(N)${SD}/*.rdf ~(N)${SD}/*.omn ; do
	print "(3) Checking $F ..."
	java -jar ${HETS_OWL_TOOLS}/OWL2Parser.jar file://$F $F.omnm || addErr
	${BD}/hets -v2 -i owl -o th,pp.dol,omn $F || addErr
done

for F in ~(N)${SD}/*.dol ; do
	print "(4) Checking $F ..."
	${BD}/hets -l OWL -v2 -o th,pp.dol,omn $F || addErr
done

# E.g.: /bin/java \
#	-Djava.util.logging.config.class=JulConfig \
#	-Dorg.semanticweb.owlapi.model.parameters.ConfigurationOptions.REPORT_STACK_TRACES=false \
#	-jar OWL2/OWL2Parser.jar \
#	-o xml /tmp/result.xml OWL2/tests/test9_Spec.omn
for F in ~(N)${SD}/*.th ~(N)${SD}/*.pp.dol ~(N)${SD}/*.omn ; do
	print "(5) Checking $F ..."
	${BD}/hets -l OWL -v2 $F || addErr
done

for F in ~(N)${SD}/*.omn ; do
	print "(6) Checking $F ..."
	java -jar ${HETS_OWL_TOOLS}/OWL2Parser.jar file://$F $F.omn2 || addErr
done

#rm -f ${SD}/*.pp.dol ${SD}/*.th ${SD}/*.omn ${SD}/*.omn2

errorMsg ${ERR} "${.sh.file}"
(( ! ERR ))
