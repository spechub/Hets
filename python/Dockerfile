FROM hets-api

RUN apt-get update && apt-get upgrade -y

RUN apt-get install -y python3-gi python3-gi-cairo gir1.2-gtk-3.0 python3-pip graphviz

RUN pip3 install xdot numpy graphviz

ENV PYTHONPATH /hets/python/
