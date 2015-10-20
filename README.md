# hyvar-rec

hyvar-rec is a tool that allows to reconfigure an existing product P valid for a given SPL when it is subject to contextual changes.

Given an existing product with its features and attributes hyvar-rec first checks if the product is valid according to the current context. If not, it tries to compute a new set of features and attributes that the new product should support in order to be valid w.r.t. contextual information.

hyvar-rec uses MiniZinc Search and in particular the Gecode solver to solve the optimization problems involved in the reconfiguration. Other solver could be easily supported.

----
Requirements:
 - docker

Requirement to install hyvar-rec from sources:
 - Python 2.7
 - antlr4-python2-runtime module for python
 - MiniZinc Search (http://www.minizinc.org/minisearch/)
 - psutil module

Docker Installation
----------------------
hyvar-rec could be installed using docker container technology (https://www.docker.com/) available for the majority of the operating systems.

The file to build the docker images is contained in the docker folder.
In the following we will give the instructions to use the tool on Linux machines. Similar task can be performed on other operating systems and we invite the interested user to consult the docker manual to find out how to perform the same task on his/her operating system.

Assuming `<hyvar_home>` is the directory path of the hyvar code, to build the docker image in Linux it is possible to run the following command.

```
sudo docker build -t hyvar:rec <hyvar_home>/docker
```

To run then the tool it is possible to use the docker run command.
As an example to print the help the command to run is the following.
```
sudo docker run -i --rm -t hyvar:rec -h
```

To test the application it is possible to use the test files contained in the test directory of the images as follows.
```
 sudo docker run -i --rm -t hyvar:rec test/test_fm.txt test/test_context.txt
```

Files can be given as input to hyvar-rec using docker volumes (e.g., -v option of docker  -https://docs.docker.com/userguide/dockervolumes/).




