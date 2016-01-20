FROM python:2-onbuild
MAINTAINER Jacopo Mauro

RUN cd / && \
  # download the source code
  git clone https://github.com/HyVar/hyvar-rec.git && \
  # install minizinc search
  wget http://www.minizinc.org/minisearch/minisearch-0.1.0b1-Linux64.tar.gz && \
  tar -zxvf minisearch-0.1.0b1-Linux64.tar.gz && \
  rm -rf minisearch-0.1.0b1-Linux64.tar.gz

ENV PATH /hyvar-rec:$PATH
ENV PATH /minisearch-0.1.0b1-Linux/bin:$PATH

# install jolie
RUN apt-get update && \
  apt-get install -y openjdk-7-jdk ant && \
  rm -rf /var/lib/apt/lists/* && \
  cd /  && \
  git clone https://github.com/jolie/jolie.git && \
  cd jolie && \
  ant && ant install

ENV PATH /jrc:$PATH
ENV JOLIE_HOME /usr/lib/jolie

EXPOSE 9001
WORKDIR /hyvar-rec
CMD ["jolie", "hyvar-rec.ol"]
