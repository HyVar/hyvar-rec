FROM python:2-onbuild
MAINTAINER Jacopo Mauro

RUN cd / && \
	###############
	# install needed packages
	###############  
	apt-get update && \
	apt-get install -y cmake bison flex openjdk-7-jdk ant && \
	rm -rf /var/lib/apt/lists/* && \
	###############
	# install jolie
	###############
  git clone https://github.com/jolie/jolie.git && \
  cd jolie && \
  ant && ant install && \
	###############
	# compile gecode
	###############
	cd / && \
  wget http://www.gecode.org/download/gecode-4.4.0.tar.gz && \
  tar -zxvf gecode-4.4.0.tar.gz && \
  cd gecode-4.4.0 && \
  ./configure --disable-examples --prefix=/gecode-4.4.0 && \
  make && make install && \
  rm -rf /gecode-4.4.0.tar.gz && \
  ###############
	# download MiniZincIDE-2.0.11-bundle-linux-x86_64.tgz
	###############
	###wget https://github.com/MiniZinc/MiniZincIDE/releases/download/2.0.11/MiniZincIDE-2.0.11-bundle-linux-x86_64.tgz && \
	###tar -zxvf MiniZincIDE-2.0.11-bundle-linux-x86_64.tgz && \
	###############
	# download minisearch binary
	###############
	cd / && \
  wget http://www.minizinc.org/minisearch/minisearch-0.1.0b1-Linux64.tar.gz && \
  tar -zxvf minisearch-0.1.0b1-Linux64.tar.gz && \
  rm -rf minisearch-0.1.0b1-Linux64.tar.gz && \
	###############
  # compile minisearch
  ###############
	###cd / && \
	###git clone -b feature/minisearch https://github.com/MiniZinc/libminizinc.git && \
	###cd libminizinc && \
	###mkdir build && \
	###cd build  && \
	###cmake .. && \
	###make && \
	###############
	# install hyvarrec
	###############
	cd / && \
	git clone https://github.com/HyVar/hyvar-rec.git


# Update the paths
ENV JOLIE_HOME /usr/lib/jolie
ENV PATH /minisearch-0.1.0b1-Linux/bin:$PATH
ENV PATH /hyvar-rec:$PATH
# update variables for gecode
ENV PATH /gecode-4.4.0/bin:$PATH
ENV LD_LIBRARY_PATH=/gecode-4.4.0/lib:$LD_LIBRARY_PATH


EXPOSE 9001
WORKDIR /hyvar-rec
CMD ["jolie", "hyvar-rec.ol"]
