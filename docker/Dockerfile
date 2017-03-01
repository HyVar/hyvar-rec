FROM python:2-onbuild
MAINTAINER Jacopo Mauro

RUN cd / && \
	###############
	# install java + needed packages
	###############
	echo deb http://http.debian.net/debian jessie-backports main >> /etc/apt/sources.list && \
	apt-get update && \
	apt-get install -y -t jessie-backports unzip openjdk-8-jdk ant ca-certificates-java && \
	rm -rf /var/lib/apt/lists/* && \
	/usr/sbin/update-java-alternatives -s java-1.8.0-openjdk-amd64

RUN cd / && \
	###############
	# install z3
	###############
	git clone --depth 1 https://github.com/Z3Prover/z3.git && \
	cd z3 && \
	python scripts/mk_make.py --python && \
	cd build && \
	make && \
	make install	

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
