FROM hets-api

USER root

RUN apt-get update && apt-get upgrade -y && \
        apt-get install -y libgtk-3-dev python3-gi python3-gi-cairo \
            gir1.2-gtk-3.0 python3-pip graphviz \
            libcanberra-gtk-module libcanberra-gtk3-module

RUN python3 -m pip install xdot numpy graphviz

RUN mkdir -p /opt/hetsgui

COPY python/hetsgui /opt/hetsgui

WORKDIR /opt/hetsgui/src
RUN glib-compile-resources hetsgui.gresource.xml

RUN ln -s /opt/hetsgui/src/application.py /usr/bin/hetsgui
RUN chmod +x /usr/bin/hetsgui

USER hets

WORKDIR /home/hets

ENTRYPOINT /usr/bin/hetsgui
