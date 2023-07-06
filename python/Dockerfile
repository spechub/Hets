FROM hets-api

RUN apt-get update && apt-get upgrade -y
RUN apt-get install curl

RUN curl -o /tmp/miniconda.sh https://repo.anaconda.com/miniconda/Miniconda3-py38_23.3.1-0-Linux-x86_64.sh
RUN bash /tmp/miniconda.sh -b -p /opt/miniconda/

ENV PATH="${PATH}:/opt/miniconda/bin"

COPY hetsgui/environment.yml /tmp/environment.yml
RUN conda env create -f /tmp/environment.yml --name app
