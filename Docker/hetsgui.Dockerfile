FROM hets-api

RUN apt-get update && apt-get upgrade -y

RUN apt-get install -y libgtk-3-dev python3-gi python3-gi-cairo gir1.2-gtk-3.0 python3-pip graphviz

RUN pip3 install xdot numpy graphviz

COPY python/hetsgui /opt/hetsgui

WORKDIR /opt/hetsgui/src

RUN glib-compile-resources hetsgui.gresource.xml

RUN ln -s /opt/hetsgui/src/application.py /usr/bin/hetsgui
RUN chmod +x /usr/bin/hetsgui

ENV PYTHONPATH /hets/python/

ENTRYPOINT /usr/bin/hetsgui
