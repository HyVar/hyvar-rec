FROM python:2-onbuild
MAINTAINER Jacopo Mauro

RUN cd / && \
	###############
	# install java + needed packages
	###############
	echo deb http://http.debian.net/debian jessie-backports main >> /etc/apt/sources.list && \
	apt-get update && \
	apt-get install -y unzip openjdk-8-jdk ant && \
	rm -rf /var/lib/apt/lists/* && \
	/usr/sbin/update-java-alternatives -s java-1.8.0-openjdk-amd64

RUN cd / && \
	###############
	# install z3
	###############
	wget https://github.com/Z3Prover/z3/releases/download/z3-4.5.0/z3-4.5.0-x64-debian-8.5.zip && \
	unzip z3-4.5.0-x64-debian-8.5.zip && \
	rm z3-4.5.0-x64-debian-8.5.zip
ENV LD_LIBRARY_PATH /z3-4.5.0-x64-debian-8.5/bin:$LD_LIBRARY_PATH
ENV PYTHONPATH /z3-4.5.0-x64-debian-8.5/bin/python:$PYTHONPATH

RUN cd / && \
	###############
	# install hyvarrec
	###############
	cd / && \
	git clone --recursive https://github.com/HyVar/hyvar-rec.git
ENV PATH /hyvar-rec:$PATH

RUN cd / && \
	###############
	# install jolie
	###############
	git clone https://github.com/jolie/jolie.git && \
	cd jolie && \
    ant && ant install
ENV JOLIE_HOME /usr/lib/jolie

EXPOSE 9001
WORKDIR /hyvar-rec
CMD ["jolie", "hyvar-rec.ol"]
