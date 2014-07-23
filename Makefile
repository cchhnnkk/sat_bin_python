
run_all:
		run_all.py

sat_bin:
		sat_bin.py --filename bram_input.txt --log2file 1 --loglevel 20

partition:
		partitioncnf.py --i input.cnf --o bram_input.txt

gen_bm_tb:
	    gen_bm_tb.py > bm_test_case.sv

