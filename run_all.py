
import sys
import partitioncnf as pcnf
import convert_csr_to_bram_data as cvt_bram
import sat_bin_lvlstate as sat
import logging

vmax = 16
cmax = 8


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
    sat.control(bramfile)


def test_uf20_91_100(n_test):
    if n_test > 100:
        n_test = 100

    path = "testdata\\uf20-91\\"
    if len(sys.argv) == 2:
        start = int(sys.argv[1])
    else:
        start = 0

    sat.logger.setLevel(logging.CRITICAL)

    for i in xrange(start, n_test, 1):
        filename = "uf20-0%d.cnf" % (i + 1)
        run_all(path + filename)


def test_uuf50():
    filename = 'testdata/uf50-01.cnf'

    sat.logger.setLevel(logging.INFO)

    sat.logging.basicConfig(level=logging.INFO)
    run_all(filename)


if __name__ == '__main__':
    # test_uf20_91_1000()
    test_uf20_91_100(10)
