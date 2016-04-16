for mode in let def1 def2 declet declet2; do
	python3 writeb.py $mode 1024 64 1 > writeb_1024_64_"$mode"_sat.smt2
	python3 writeb.py $mode 1024 64 2 > writeb_1024_64_"$mode"_unsat.smt2
done

for mode in let def dec; do
	python3 op2.py $mode 2048 4 1 > op2_"$mode"_sat.smt2
	python3 op2.py $mode 2048 4 8 > op2_"$mode"_unsat.smt2
done

for mode in def1 unroll inst; do
	#python3 memset.py $mode 256 16 16 2 > memset_"$mode"_sat.smt2
	#python3 memset.py $mode 256 16 16 5 > memset_"$mode"_unsat.smt2
	#python3 memset.py $mode 128 10 5 5 > memset_"$mode"_hard.smt2
	python3 memset.py $mode 64 10 4 5 > memset_"$mode"_64_4.smt2
	python3 memset.py $mode 128 10 4 5 > memset_"$mode"_128_4.smt2
	python3 memset.py $mode 64 10 5 5 > memset_"$mode"_64_5.smt2
done
