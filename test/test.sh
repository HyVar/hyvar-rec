#!/bin/bash

LOG_FILE='/tmp/hyvar_test.log'

python ../hyvar-rec.py sat.json > $LOG_FILE
python ../hyvar-rec.py unsat.json >> $LOG_FILE
python ../hyvar-rec.py --explain unsat.json >> $LOG_FILE
python ../hyvar-rec.py --validate sat.json >> $LOG_FILE
python ../hyvar-rec.py --validate unsat.json >> $LOG_FILE
python ../hyvar-rec.py --check-interface interface.json sat.json >> $LOG_FILE
python ../hyvar-rec.py --check-interface no_interface.json sat.json >> $LOG_FILE
python ../hyvar-rec.py test1.json >> $LOG_FILE
python ../hyvar-rec.py --features-as-boolean sat_bool.json >> $LOG_FILE
python ../hyvar-rec.py -v --check-features sat.json >> $LOG_FILE
python ../hyvar-rec.py -v --check-features unsat.json >> $LOG_FILE
python ../hyvar-rec.py sat_special_smt_constraints.json >> $LOG_FILE

diff $LOG_FILE output.txt
rm $LOG_FILE



