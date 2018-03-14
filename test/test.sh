#!/bin/bash

LOG_FILE='/tmp/hyvar_test.log'

python ../hyvar-rec.py sat.json > $LOG_FILE
python ../hyvar-rec.py unsat.json >> $LOG_FILE
python ../hyvar-rec.py --explain unsat.json >> $LOG_FILE
python ../hyvar-rec.py --validate sat.json >> $LOG_FILE
python ../hyvar-rec.py --validate --non-incremental-solver sat.json >> $LOG_FILE
python ../hyvar-rec.py --validate unsat.json >> $LOG_FILE
python ../hyvar-rec.py --validate --non-incremental-solver unsat.json >> $LOG_FILE
python ../hyvar-rec.py --validate --validate-modality grid unsat.json >> $LOG_FILE
python ../hyvar-rec.py --validate --validate-modality grid --non-incremental-solver unsat.json >> $LOG_FILE
python ../hyvar-rec.py --check-interface interface.json sat.json >> $LOG_FILE
python ../hyvar-rec.py --check-interface no_interface.json sat.json >> $LOG_FILE
python ../hyvar-rec.py test1.json >> $LOG_FILE
python ../hyvar-rec.py --features-as-boolean sat_bool.json >> $LOG_FILE
python ../hyvar-rec.py sat_special_smt_constraints.json >> $LOG_FILE
python ../hyvar-rec.py --check-features evolution_sat.json >> $LOG_FILE
python ../hyvar-rec.py --check-features --non-incremental-solver evolution_sat.json >> $LOG_FILE
python ../hyvar-rec.py --check-features --check-features-modality forall evolution_sat.json >> $LOG_FILE
python ../hyvar-rec.py --check-features --check-features-modality forall --non-incremental-solver evolution_sat.json >> $LOG_FILE
python ../hyvar-rec.py --check-features --check-features-modality pruning evolution_sat.json >> $LOG_FILE
python ../hyvar-rec.py --check-features --check-features-modality pruning --non-incremental-solver evolution_sat.json >> $LOG_FILE
python ../hyvar-rec.py --features-as-boolean test3_oneonly.json >> $LOG_FILE

diff $LOG_FILE output.txt
rm $LOG_FILE



