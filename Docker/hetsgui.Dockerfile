FROM hets-api

USER root

COPY python/gui /opt/hetsgui

RUN apt-get update && apt-get upgrade -y && \
        apt-get install -y libgtk-3-dev python3-gi python3-gi-cairo \
            gir1.2-gtk-3.0 python3-pip graphviz \
            libcanberra-gtk-module libcanberra-gtk3-module && \
    mkdir -p /opt/hetsgui && \
    cd /opt/hetsgui/src/hetsgui && \
    glib-compile-resources hetsgui.gresource.xml && \
    python3 -m pip install /opt/hetsgui && \
    rm -rf /opt/hetsgui

WORKDIR /home/hets

USER hets

ENTRYPOINT /usr/local/bin/hets
