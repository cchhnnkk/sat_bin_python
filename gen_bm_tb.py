#!python
# -*- coding: utf-8 -*-

# 截取sat_bin的代码，用于生成verilog中bin_manager模块的testbench

class GenBmTb(object):

    """docstring for BinManager"""

    def __init__(self):
        self.clauses_bins = []
        self.n_oc_bin = []        # the Num of the origin clauses in the bins
        self.n_lc_bin = []        # the Num of the learnt clauses in the bins
        self.vars_bins = []
        self.nb = 0               # Num of the bins
        self.nc = 0               # total clauses Num
        self.nv = 0               # total vars Num
        self.cmax = 0
        self.vmax = 0

    def init_bins(self, filename):
        lists = [l for l in file(filename) if l[0] not in '\n']
        i = 0
        while i < len(lists):
            liststrip = lists[i].strip().split()
            if liststrip == []:
                pass
            elif liststrip[0] == 'total':
                if liststrip[3] == 'bins':
                    self.nb = int(liststrip[-1])
                elif liststrip[3] == 'variables':
                    self.nv = int(liststrip[-1])
                elif liststrip[3] == 'clauses':
                    self.nc = int(liststrip[-1])

            elif liststrip[0] == 'cmax':
                self.cmax = int(liststrip[-1])
                self.cmax = self.cmax * 2
            elif liststrip[0] == 'vmax':
                self.vmax = int(liststrip[-1])

            elif liststrip[0] == 'bin':
                cntc_bin = 0
                cbin = []

            elif liststrip[0] == 'variables':
                i += 1
                vbin = [int(l) - 1 for l in lists[i].strip().split()]
                self.vars_bins += [vbin]

            elif liststrip[0] == 'clauses':
                nc_bin = int(liststrip[-1])

            else:
                c = [int(l) for l in liststrip]
                cbin += [c]
                cntc_bin += 1
                if cntc_bin == nc_bin:
                    self.clauses_bins += [cbin]
                    self.n_oc_bin += [nc_bin]
                    self.n_lc_bin += [0]

            i += 1
    
    def get_one_bin(self, clauses, variables):
        cmax = self.cmax
        vmax = self.vmax
        ci = 1
        str_cbin = ""
        for ci in xrange(cmax):
            if ci < len(clauses):
                c = clauses[ci]
            else:
                c = [0] * vmax
            strc = "\t'{"
            # print len(c), len(variables)
            for vi in xrange(vmax):
                if vi < len(c):
                    lit = c[vi]
                else:
                    lit = 0
                strc += str(lit)
                if vi != vmax - 1:
                    strc += ', '
            if ci != cmax - 1:
                str_cbin += strc + '},\n'
            else:
                str_cbin += strc + '}'

        str_vbin = "\t"
        for vi in xrange(vmax):
            if vi < len(variables):
                v = variables[vi]
                v += 1
            else:
                v = 0
            if vi != vmax - 1:
                str_vbin += str(v) + ', '
            else:
                str_vbin += str(v)

        return str_cbin, str_vbin

    def get_all_bins(self):
        cmax = self.cmax
        vmax = self.vmax
        ci = 1
        str_info = "int nb = %d;\n" % self.nb
        str_info += "int cmax = %d;\n" % self.cmax
        str_info += "int vmax = %d;\n\n" % self.vmax

        str_cbin = "int cbin[%d][%d] = '{\n" % (cmax*self.nb, vmax)
        str_vbin = "int vbin[%d] = '{\n" % (cmax*self.nb)
        for i in xrange(self.nb):

            strc, strv = self.get_one_bin(self.clauses_bins[i], self.vars_bins[i])
            strc = "\t//bin %d\n" % (i + 1) + strc
            strv = "\t//bin %d\n" % (i + 1) + strv
            if i != self.nb - 1:
                str_cbin += strc + ',\n\n'
                str_vbin += strv + ',\n'
            else:
                str_cbin += strc + '\n'
                str_vbin += strv + '\n'

        str_cbin += '};\n\n'
        str_vbin += '};\n\n'
        return str_info + str_cbin + str_vbin


filename = 'testdata/bram_bins_sat7.txt'
gen_bm_tb = GenBmTb();
gen_bm_tb.init_bins(filename)
print gen_bm_tb.get_all_bins()

