#!python

import sys
import partitioncnf as pcnf
import convert_csr_to_bram_data as cvt_bram
import sat_bin_lvlstate as sat
import logging

vmax = 64
cmax = 64
# loglevel = logging.WARNING
loglevel = logging.DEBUG
log2file = True


def run_all(filename):
    print filename
    binfile = 'bin.txt'
    print '\tpartition the CNF'
    pcnf.vmax = vmax
    pcnf.cmax = cmax
    pcnf.run(filename, binfile)
    bramfile = 'bram.txt'
    cvt_bram.convert_csr_to_bram_data(binfile, bramfile)
    print '\tsolve the sat'
    sat.loglevel = loglevel
    sat.log2file = log2file
    sat.run(bramfile)


def test_uf20_91_100(n_test):
    if n_test > 100:
        n_test = 100

    path = "testdata\\uf20-91\\"
    if len(sys.argv) == 2:
        start = int(sys.argv[1])
    else:
        start = 0

    for i in xrange(start, n_test, 1):
        filename = "uf20-0%d.cnf" % (i + 1)
        run_all(path + filename)


def test_uf50():
    filename = 'testdata/uf50-01.cnf'

    sat.CNT_ACROSS_BKT = 500
    sat.TIME_OUT_LIMIT = 10     # 60s
    run_all(filename)


def test_file(filename, vmax_i, cmax_i):
    global vmax, cmax
    vmax = vmax_i
    cmax = cmax_i
    sat.set_logging_file(logging.DEBUG)
    run_all(filename)

if __name__ == '__main__':
    test_uf20_91_100(10)
    # test_uf50()
