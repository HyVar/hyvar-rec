# hyvar-rec

hyvar-rec is a tool that allows to reconfigure an existing configuration 
for a given SPL when it is subject to contextual changes.

Given an existing configuration C with its features and attributes, hyvar-rec
returns the best configuration that maximises the user preferences and is
the most similar to the initial configuration C.

hyvar-rec uses MiniZinc Search and in particular the Gecode solver to solve the 
optimization problems involved in the reconfiguration.

----

Requirement to install hyvar-rec from sources:
 - Python 2.7
 - antlr4-python2-runtime module for python
 - MiniZinc Search (http://www.minizinc.org/minisearch/)
 - psutil module

Docker Installation & Use as a Service
----------------------
hyvar-rec could be installed using docker container technology
(https://www.docker.com/) available for the majority of the operating systems.
It can therefore be used simply sending a post request to the server deployed
by using docker.

The file to build the docker images is contained in the docker folder. In the
following we will give the instructions to deploy hyvar-rec locally via docker
assuming the use of a Linux machine.  Similar task can be performed on other
operating systems and we invite the interested user to consult the docker
manual to find out how to perform the same task on his/her operating system.

The Dockerfile needed to generate the container image is stored in the
docker subfolder. Assuming Docker is installed and \<PATH\> is the path to
the hyvar-rec folder, it is possible to deploy hyvar-rec with:

```
sudo docker build -t hyvarrec <PATH>/docker
sudo docker run -d -p <PORT>:9001 --name hyvarrec_container hyvarrec
```

where \<PORT\> is the port used to use the functionalities of the service.

Assuming \<JSON\> is the json input file (please see below for more details
about the input format), to obtain the desired configuration it is possible
to perform the following post request.

```
curl -H "Content-Type: application/json" -X POST -d @<JSON> http://localhost:<PORT>/process
```

To check if the service is responding it is possible to use the following
post request.
```
curl -X POST -d '{}' http://localhost:<PORT>/health
```

To clean up please lunch the following commands:

```
sudo docker stop hyvarrec_container
sudo docker rm hyvarrec_container
sudo docker rmi hyvarrec
```

For more information, please see the Docker documentation at docs.docker.com

Input Specification
----------------------
hyvar-rec requires a unique JSON file in input that formalizes the FM, the
initial configuration, the contextual information, and the user preferences.
All these information are encoded into a JSON object following the JSON
schema defined in spec/hyvar_input_schema.json .

Since hyvar-rec is an anytime solver it produces valid configurations during
the search. In particular, after printing a valid configuration, if it
finds another one that satisfy more user preferences this configuration is
printed too.  Every configuration is outputted in a JSON object following
the schema defined in spec/hyvar_output_schema.json .  After printing the
configuration that maximize the user preferences and is
closer to the initial configuration the tool exits.

Please note that when the tool is deployed using docker and used via POST 
requests, the output obtained is only the final optimal configuration, if any.
If no valid solution exists for the considered problem the output of the POST
request will be the following JSON object.
```
{"no_solution": 1}
```
