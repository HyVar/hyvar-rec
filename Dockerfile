FROM python:3-buster
MAINTAINER Jacopo Mauro

RUN pip3 install click z3-solver antlr4-python3-runtime

# install java
#RUN apt-get update && \
#	apt-get install -y openjdk-11-jdk-headless && \
#	rm -rf /var/lib/apt/lists/*

# install jolie
#RUN cd / && \
#    wget https://www.jolie-lang.org/files/releases/jolie-1.8.2.jar && \
#	java -jar jolie-1.8.2.jar -jh /usr/lib/jolie -jl /usr/bin && \
#	rm jolie-1.8.2.jar
#ENV JOLIE_HOME /usr/lib/jolie


RUN cd / && \
	git clone https://github.com/HyVar/hyvar-rec.git && \
	cd hyvar-rec/test/cafm_generator && \
	git clone https://github.com/RalfRothenberger/Power-Law-Random-SAT-Generator && \
	cd Power-Law-Random-SAT-Generator && \
	make
ENV PATH /hyvar-rec:$PATH
ENV PATH /hyvar-rec/test/cafm_generator/Power-Law-Random-SAT-Generator:$PATH

#EXPOSE 9001
WORKDIR /hyvar-rec
CMD ["python3", "hyvar-rec.py"]
