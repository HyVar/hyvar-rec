# hyvar-rec

hyvar-rec is a tool that allows to reconfigure an existing configuration 
for a given SPL when it is subject to contextual changes.

Given an existing configuration C with its features and attributes, hyvar-rec
returns the best configuration that maximises the user preferences and is
the most similar to the initial configuration C.

hyvar-rec uses the SMT solver Z3 to solve the
optimization problems involved in the reconfiguration.

----

Requirement to install hyvar-rec from sources:
 - Python 2.7
 - antlr4-python2-runtime module for python
 - Z3 (https://github.com/Z3Prover/z3)

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
schema defined in spec/hyvar_input_schema.json.

The output is a JSON object following
the schema defined in spec/hyvar_output_schema.json.

Validate and Explain Modalities
----------------------

hyvar-rec can also be used to check if a given FM is non void for all the possible context.
This can be done by running the following POST request.

```
curl -H "Content-Type: application/json" -X POST -d @<JSON> http://localhost:<PORT>/validate
```

where \<JSON\> is the json input file as specified in the input format.
In this case, the information related to the initial configuration are discarded.

The answer is a JSON object having the schema defined in spec/hyvar_output_validate.json.
Basically, in the field "result" it will report the result of the analysis (either "valid" or "not_valid").
If the FM is void for certain context then the output will also provide the list of one context
assignement that makes the model void.

When a model is void hyvar-rec can be used to check the set of constraints that makes the model void.
This can be done by running the following POST request.

```
curl -H "Content-Type: application/json" -X POST -d @<JSON> http://localhost:<PORT>/validate
```

where \<JSON\> is the json input file as specified in the input format. In this case it is
important to define into the initial configuration the values of the context
that makes the FM void.

The answer is a JSON object having the schema defined in spec/hyvar_output_explain.json.
Basically, in the field "result" it will report if the FM is void or not (either "sat" or "unsat").
If the FM is void with the keyword "constraints" the list of the constraint responsible for the
voidness of the FM is returned.