python3 writeb.py let 1024 64 1 > writeb_1024_64_let_sat.smt2
python3 writeb.py def1 1024 64 1 > writeb_1024_64_def1_sat.smt2
python3 writeb.py def2 1024 64 1 > writeb_1024_64_def2_sat.smt2
python3 writeb.py let 1024 64 2 > writeb_1024_64_let_unsat.smt2
python3 writeb.py def1 1024 64 2 > writeb_1024_64_def1_unsat.smt2
python3 writeb.py def2 1024 64 2 > writeb_1024_64_def2_unsat.smt2
