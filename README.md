# hyvar-rec

hyvar-rec is a tool that allows to reconfigure an existing configuration C valid for a 
given SPL when it is subject to contextual changes.

Given an existing configuration C with its features and attributes hyvar-rec returns the
best configuration that maximises the user preferences and is the most similar to
the initial configuration C.

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
It can therefore be used simply sending a get request to the server deployed by
using docker.

The file to build the docker images is contained in the docker folder. In the
following we will give the instructions to deploy hyvar-rec locally via docker
assuming
the use of a Linux machine.  Similar task can be performed on other operating
systems and we invite the interested user to consult the docker manual to
find out how to perform the same task on his/her operating system.

The Dockerfile needed to generate the container image is stored in the
docker subfolder. Assuming Docker is installed and \<PATH\> is the path to
the hyvar-rec folder, it is possible to deploy hyvar-rec with:

```
sudo docker build -t hyvarrec <PATH>/docker
sudo docker run -d -p 9000:9001 --name hyvarrec_container hyvarrec
```

Assuming \<SPEC\> is the string containing the fm specification and \<CONTEXT\>
the string containing the contextual information (please see below for the formal
definition of these two inputs), to obtain the desired configuration it
is possible to perform the following get requests

```
http://<IP>:9000/process?specification=<SPEC>&context=<CONTEXT>
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
hyvar-rec requires two files as input: the Configuration Specification
(ConfS) and the Context Specification (ContS).

The ConfS is the file containing the definition of the constraints specified
by the FM and the actual configuration of the product. The ANTLR grammar of
the ConfS is defined in the SpecificationGrammar/ SpecificationGrammar.g4 file.

The ConfS starts by defining the number of feature #f by using the keyword 
FEATURE_NUM, the number of context #c by using the keyword CONTEXT_NUM.
We assumed that the features are numbered from 0 to  #f-1 and the number of 
context from 0 to #c.

The keyword ATTRIBUTES_NUM is used to specify the number of attributes for 
every feature. This is done by means of a list of integers where the i-th 
integer represents is the number of attributes of the i-th feature.

The keyword DOMAIN_ATTRIBUTES is used to specify the domains of the attributes. 
The attributes are enumerated starting from the first attribute of feature 0, if 
any, to the last attribute of feature #f-1 with an increasing number starting 
from 0. The domain of an attribute is represented by a pair of number 
representing the lower bound and the upper bound of the domain. We assume that 
the domains are continuous and include all the values between the lower bound 
and upper bound, extremes included. The domain of the attributes is specified by 
a list of integers where the number in the 2i position represents the lower 
bound of the domain of the i-th attribute while the 2i+1 represent the upper 
bound of the i-th attribute. 

The keyword DOMAIN_CONTEXT is used to specify the domains of the contexts. 
Similarly to what happens for the domains of the attributes the domain of the 
context are specified by a list of integers where the 2i position represent the 
lower bound of the domain of the i-th context while the 2i+1 represent the upper 
bound of the i-th context.

The keyword INITIAL_FEATURES and INITIAL_ATTRIBUTES specify the current 
configuration of the product. In particular the presence or absence of feature 
is specified by a list associated to the keyword INITIAL_FEATURES. If feature i 
is selected in the configuration then the element in the i position of the list 
is 1, 0 otherwise. Similarly, the value of the attributes is specified with a 
list associated to the keyword INITIAL_ATTRIBUTES. The value of the attribute i 
is specified in position i. The enumeration used for the attributes is the one 
adopted to specify their domains.

After specifying all these detail the constrains derived by the FM must be 
defined in a comma separated list. A constraint is a logical expression using 
the standard logical operators (viz., and, or, xor, not, impl, iff), boolean 
constants (viz., true, false), and arithmetical comparison. The arithmetical 
comparison uses the standard operators (viz., <=, =, >=, <, >, !=)  between 
arithmetical expressions. An arithmetical expression is built using standard 
arithmetic operators (viz., +, -, *) using as terms numbers, context, feature, 
and attributes. In particular the i-th context is represented with the term 
context[i], the i-th feature with the term feature[i] and the j attribute of 
feature i is represented with the term attribute[i][j].

The ContS file contains the specification of the value of the current context. 
These are given by means of integer values, one per line starting from the first 
to the last one. The ContS should contain #c lines.

For an example of the ConfS file we invite the reader to see the file 
test/example.txt. An example of the ContS is the test/example_context.txt file

Output Specification
----------------------

If the given configuration is valid the output of the tool is the following.

```
%VALID
<CONFIG>
----------
```

where <CONFIG> is the representation of the configuration defined by the
following grammar:

<CONFIG> ::=
	'feature' '=' '[' INT (',' INT)* ']\n'
	'attributes' '=' '[' INT (',' INT)* ']\n'
	'%OBJVAR' '[' INT (',' INT)* ']\n'

The keyword feature and attributes define arrays of integer stating the
values of the features and the value of the attributes as specified by the
arrays associated with the keywords INITIAL_FEATURES and INITIAL_ATTRIBUTES
in the ConfS file. The line starting with %OBJVAR is a comment representing
the quality of the solution and is required by MiniSearch.

When hyvar-rec detects that the configuration is not valid it tries to compute
a valid one and then it tries to improve it. hyvar-rec is an anytime solver,
i.e., it prints valid configurations until the optimal one is founded. Then
it exist. The new recomputed configuration have the following structure.
```
%RECOMPUTING
<CONFIG>
----------
```
where <CONFIG> is as defined above and is used to specify what are the selected
features and what are their attributes.

The configuration are printed sequentially. A configuration is always better
than the ones that are printed earlier. The last printed configuration is
the optimal one.  To signal that the tool has explore all the search space
hyvar-rec outputs the following line.
```
==========
```

Please note that this line is the only output obtained if no valid
configuration is possible for the given context.
