FROM python:3-buster
MAINTAINER Jacopo Mauro

RUN pip3 install click z3-solver antlr4-python3-runtime

#RUN cd / && \
#	###############
#	# install z3
#	###############
#	git clone --depth 1 https://github.com/Z3Prover/z3.git && \
#	cd z3 && \
#	python scripts/mk_make.py --python && \
#	cd build && \
#	make && \
#	make install

# install java
RUN apt-get update && \
	apt-get install -y openjdk-11-jdk-headless && \
	rm -rf /var/lib/apt/lists/*

# install jolie
RUN cd / && \
    wget https://www.jolie-lang.org/files/releases/jolie-1.8.2.jar && \
	java -jar jolie-1.8.2.jar -jh /usr/lib/jolie -jl /usr/bin && \
	rm jolie-1.8.2.jar
ENV JOLIE_HOME /usr/lib/jolie


RUN cd / && \
	###############
	# install hyvarrec
	###############
	git clone https://github.com/HyVar/hyvar-rec.git
ENV PATH /hyvar-rec:$PATH

EXPOSE 9001
WORKDIR /hyvar-rec
CMD ["jolie", "hyvar-rec.ol"]
