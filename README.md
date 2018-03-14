# HyVarRec

HyVarRec is a tool that allows to reconfigure an existing configuration 
for a given SPL when it is subject to contextual changes.

Given an existing configuration C with its features and attributes, HyVarRec
returns the best configuration that maximises the user preferences and is
the most similar to the initial configuration C.

HyVarRec uses the SMT solver Z3 to solve the
optimization problems involved in the reconfiguration.

----

Requirement to install HyVarRec from sources:
 - Python 2.7
 - antlr4-python2-runtime and click modules for python
 - Z3 Version 4.5.0 or above (https://github.com/Z3Prover/z3)

Docker Installation & Use as a Service
----------------------
HyVarRec could be installed using docker container technology
(https://www.docker.com/) available for the majority of the operating systems.
It can therefore be used simply sending a post request to the server deployed
by using docker.

The file to build the docker images is contained in the docker folder. In the
following we will give the instructions to deploy HyVarRec locally via docker
assuming the use of a Linux machine.  Similar task can be performed on other
operating systems and we invite the interested user to consult the docker
manual to find out how to perform the same task on his/her operating system.

The image of HyVarRec is available on Docker Hub. To run it please execute the
following commands.

```
sudo docker pull jacopomauro/hyvarrec
sudo docker run -d -p <PORT>:9001 --name hyvarrec_container jacopomauro/hyvarrec
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
sudo docker rmi jacopomauro/hyvarrec
```

For more information, please see the Docker documentation at docs.docker.com
Examples of input files for HyVarRec are available in the test directory.

Input Specification
----------------------
HyVarRec requires a unique JSON file in input that formalizes the FM, the
initial configuration, the contextual information, and the user preferences.
All these information are encoded into a JSON object following the JSON
schema defined in spec/hyvar_input_schema.json.

The output is a JSON object following
the schema defined in spec/hyvar_output_schema.json.

Validate and Explain Modalities
----------------------

HyVarRec can also be used to check if a given FM is non void for all the possible context.
This can be done by running the following POST request.

```
curl -H "Content-Type: application/json" -X POST -d @<JSON> http://localhost:<PORT>/validate
```

where \<JSON\> is the json input file as specified in the input format.
In this case, the information related to the initial configuration are discarded.

The answer is a JSON object having the schema defined in spec/hyvar_output_validate.json.
Basically, in the field "result" it will report the result of the analysis (either "valid" or "not_valid").
If the FM is void for certain context then the output will also provide the list of one context
assignment that makes the model void.

When a model is void HyVarRec can be used to check the set of constraints that makes the model void.
This can be done by running the following POST request.

```
curl -H "Content-Type: application/json" -X POST -d @<JSON> http://localhost:<PORT>/explain
```

where \<JSON\> is the json input file as specified in the input format. In this case it is
important to define into the initial configuration the values of the context
that makes the FM void.

The answer is a JSON object having the schema defined in spec/hyvar_output_explain.json.
Basically, in the field "result" it will report if the FM is void or not (either "sat" or "unsat").
If the FM is void with the keyword "constraints" the list of the constraint responsible for the
voidness of the FM is returned. Note that it is possible to select the option --constraints-minimization
to get the minimal (not minimum) explanation.

Check Features Modality
----------------------

HyVarRec can be used to provide the list of the dead and false optional features.
Dead features are optional features that can not be selected.
Mandatory features instead are optional features that must be selected.
The check can be done by running the following POST request.

```
curl -H "Content-Type: application/json" -X POST -d @<JSON> http://localhost:<PORT>/check_features
```

where \<JSON\> is the json input file as specified in the input format.
In this case, the information related to the initial configuration are discarded.

Note that that the only features that are checked are those declared as optional. This can be done by
using the optional field "optional_features" in the input specification. In case evolution is considered
(i.e., a context is used to express the time) then it is possible to define the exact time points where the
feature are optional. In this case, the check is performed for these time point only.

The answer is a JSON object having the schema defined in spec/hyvar_output_check_features.json.

MSPL: Interface Check
----------------------
HyVarRec allows to validate if a given I SPL is an interface of another SPL S. Being an interface
means that every configuration of I can be extended to form a valid configuration of S.
  
This can be done by running the following POST request.

```
curl -H "Content-Type: application/json" -X POST -d @<JSON> http://localhost:<PORT>/check_interface
```

where \<JSON\> is a JSON file defining both the software product lines.
In particular, assuming { I } is the JSON object defining the FM of I and { S } the feature model
defining the FM of S according to the json schema in spec/hyvar_input_schema.json, the JSON input
to submit to HyVarRec is the following one.
 
```
{ "interface" : { I }, "spl" : { S } }
```

The output obtained is a JSON object having the JSON schema spec/hyvar_output_validate.json.
In particular, when the interface is not a valid interface HyVarRec returns the context, features,
and attributes that can not be extended in the SPL S.

Features as Booleans
--------------------
It is possible to use HyVarRec in explain and reconfiguring modality by entering features directly
as booleans by using the option --features-as-boolean. In this case the feature name needs to
start with a letter.

For example: the constraint 'feature[f111] = 1' can be encoded as 'f111'

To activate the --features-as-boolean option using the HTTP interface the JSON input should be
extended with the following property when used in reconfiguration modality.

```
"hyvar_options" : ["--features-as-boolean"]
```

Direct encoding into SMT formulas
---------------------------------

For performances reason it is possible to enter the formulas directly into SMT format.

For example the constraint 'feature[f111] = 1' can be encoded as follows.

```
"smt_constraints" : {
		"formulas": ["(declare-fun f111 () Int) (assert  (= f111 1))"],
    "features": ["_id0"]
		}
```

The keyword "features" is used to add all the feature introduced by the constraints.

If the --features-as-boolean option is activated then the constraint can be enter as follows.

```
"smt_constraints" : {
		"formulas": ["(declare-fun f111 () Bool) (assert  (= f111))"],
    "features": []
		}
```

Note that in this case it is not needed to specify the list of the features introduced.

Limitations & Notes
------------
Operator have left associativity: e.g., x + x * y is interpreted as (x + x) * y
