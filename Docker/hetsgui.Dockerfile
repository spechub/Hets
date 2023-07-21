FROM hets-api

USER root

RUN apt-get update && apt-get upgrade -y && \
        apt-get install -y libgtk-3-dev python3-gi python3-gi-cairo \
            gir1.2-gtk-3.0 python3-pip graphviz \
            libcanberra-gtk-module libcanberra-gtk3-module

# RUN python3 -m pip install xdot numpy graphviz

RUN mkdir -p /opt/hetsgui

COPY python/gui /opt/hetsgui

WORKDIR /opt/hetsgui/src/hetsgui
RUN glib-compile-resources hetsgui.gresource.xml

RUN python3 -m pip install /opt/hetsgui

RUN rm -rf /opt/hetsgui

WORKDIR /home/hets

USER hets

ENTRYPOINT /usr/local/bin/hets
