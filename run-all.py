
import sys
import partitioncnf as pcnf
import convert_csr_to_bram_data as cvt_bram
import sat_bin_lvlstate as sat


def run_all(filename):
    print filename
    binfile = 'bin.txt'
    print '\tpartition the CNF'
    pcnf.run(filename, binfile)
    bramfile = 'bram.txt'
    cvt_bram.convert_csr_to_bram_data(binfile, bramfile)
    print '\tsolve the sat'
    sat.control(bramfile)


def test_uf20_91_1000():
    # path = "E:\\sat\\workspace\\partitionCNF\\cnfdata\\"
    path = "E:\\sat\\reference\\benchmarks\\satlib-benchmark\\uf20-91\\"
    if len(sys.argv) == 2:
        start = int(sys.argv[1])
    else:
        start = 1

    for i in xrange(start, 1000, 1):
        filename = "uf20-0%d.cnf" % i
        run_all(path + filename)

if __name__ == '__main__':
    test_uf20_91_1000()
