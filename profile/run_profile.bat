python -m cProfile -o output.pstats ../run_all.py
python gprof2dot.py -f pstats output.pstats | dot -Tpng -o output.png