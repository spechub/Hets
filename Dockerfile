FROM ubuntu:16.04

ENV LANG C.UTF-8

# add http://pkg.cs.ovgu.de/LNF/linux/ubuntu/16.04/ to package sources
# see issue #1869 for more information
RUN echo "deb [trusted=yes] http://pkg.cs.ovgu.de/LNF/linux/ubuntu 16.04/" > /etc/apt/sources.list.d/ovgu.list
# Always prefer packages from our local pkg repo even if the package has a lower version than the one in the distro repo!
RUN echo "Package: *" > /etc/apt/preferences.d/ovgu.pref
RUN echo "Pin: origin \"pkg.cs.ovgu.de\"" >> /etc/apt/preferences.d/ovgu.pref
RUN echo "Pin-Priority: 999" >> /etc/apt/preferences.d/ovgu.pref

RUN apt-get update && apt-get install software-properties-common -y
RUN apt-add-repository ppa:hets/hets
RUN apt-get update && apt-get install -y hets-server && rm -rf /var/lib/apt/lists/*

RUN mkdir /data
VOLUME /data

WORKDIR /data

EXPOSE 8000

# TODO: add Hets-lib
CMD ["hets-server", "--server"]