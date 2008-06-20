In dieser Dokumentation wird es beschrieben, wie Pellet im Rahmen von Hets benutzt wird.

1. Die Installierung von Pellet:
   1.1. Unter http://pellet.owldl.com/download kann das aktuelle Pellet herunterladen werden;
   1.2. Die herunterladene Zip-Datei in einen Verzeichnis (z.B. ~/utility/pellet) entpacken;
   1.3. Eine Umgebungsvariable $PELLET_PATH auf das in 1.2. hergestellte Verzeichnis einstellen (z.B. export PELLET_PATH=~/utility/pellet);

2. Consistent Checking mit Pellet in Hets:
   2.1. In Hets-GUI klicken Sie rechte Moustast auf einem Knoten, waehlen Sie "consistent check" in der Menue aus;
   2.2. Wenn ein Window mit der Meldung "Pellet not found" kommt, bedeutet, dass die $PELLET_PATH nicht richtig gesetzt wurde;
   2.3. Beim erfolgreichen Aufruf von Pellet wird ein Fernster mit entweder "This Ontology is consistent." oder "This Ontology is not consistent." angezeigt. Daneben wird die vom Renderer hergestellten Ontology in einem anderen Fernster angezeigt.

3. Prove mit Pellet:
   3.1. In der zu pruefenden OWL-Datei muessen folgende Tags fuer
   	zu den pruefenden Axiomen einfuegt werden:

    <EntityAnnotation>
        <ObjectProperty URI="&test1;role1"/>  <!-- Hier ist das zu
   					      	pruefende Axiom -->
        <Annotation annotationURI="&test1;Implied">
            <Constant Datatype="&xsd;boolean">true</Constant>
        </Annotation>
    </EntityAnnotation>

    (Siehe OWL/tests/test1-implied.owl)	


coming soon.....
