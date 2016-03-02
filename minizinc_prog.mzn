% Copyright (c) 2016, Jacopo Mauro. All rights reserved. 
% This file is licensed under the terms of the ISC License.

include "minisearch.mzn";

% Please note that you will need to set the MiniZinc standard library 
% environement variable $MZN_STDLIB_PATH to share/minizinc to include 
% the MiniSearch builtins

% e.g., --stdlib-dir ~/programmi/minizinc/minisearch-0.1.0b1-Linux/share/minizinc

%%%%%%%%%%%%%%%%
% Input parameters
%%%%%%%%%%%%%%%%

% maximumn domain value
int: MAX_INT;
% minimum domain value
int: MIN_INT;

% features
set of int: feats;

% context
set of int: contexts;

% attributes
set of int: attrs;

% feature array
array[feats] of var 0..1: feat;

% context array
array[contexts] of var MIN_INT..MAX_INT: context;

% attributes array
array[attrs] of var MIN_INT..MAX_INT: attr;

% initial features
array[feats] of int: init_feat;

% initial attributes
array[attrs] of int: init_attr;

% initial contexts
array[contexts] of int: init_context;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Domain constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% context domains bounds
array[contexts] of int: context_min;
array[contexts] of int: context_max;

constraint forall(c in contexts) (
  context[c] >= context_min[c] /\
  context[c] <= context_max[c]
);

% attribute domains bounds
array[attrs] of int: attr_min;
array[attrs] of int: attr_max;

constraint forall(a in attrs) (
  attr[a] >= attr_min[a] /\
  attr[a] <= attr_max[a]
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Set initial values for context
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(c in contexts) (
  context[c] = init_context[c]
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% FM constraints are added dynamically
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% search function
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

array[feats] of var 0..1: diff_feat;
constraint forall( f in feats) (
  diff_feat[f] = 0 <-> feat[f] >= init_feat[f] 
);

array[attrs] of var 0..1: diff_attr;
constraint forall( a in attrs) (
  diff_attr[a] = 0 <-> attr[a] = init_attr[a]
);

function ann: my_search(array[int] of var int: objs) = (
  % TODO: use initial values when starting to check the solutions
  %repeat (i in 1..1) ( scope( 
  %  post (
  %    forall( f in feats) (
  %      feat[f] = init_feat[f]
  %    ) /\ 
  %    forall( a in attrs) (
  %      attr[a] = init_attr[a]
  %    ) 
  %  )
  %  /\
  %  next() /\ commit() /\ print("%VALID\n") /\ print()
  %))
  if next()
  then 
    commit() /\
    %print("%SOLUTION\n") /\
    print() /\
    repeat( scope( 
      let {array[1..length(objs)] of int:v=[ sol(objs[i])| i in 1..length(objs)]}
        in  post(lex_greater(objs,v)) /\
            (next() /\ commit() /\ print("%RECOMPUTING\n") /\ print())  \/  break
          )
    )
  else
    print("%NO SOLUTION\n")
  endif  
);

solve search my_search(obj_array);

output ["features = " ++ show(feat) ++ "\n",
   "attributes = " ++ show(attr) ++ "\n",
   "%OBJVAR " ++ show(obj_array) ++ "\n" ];