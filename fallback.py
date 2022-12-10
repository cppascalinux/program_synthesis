import sys
import sexp
import pprint
import translator

tot = 0
synFunExpr = []
synFunName = ''
synFunName2Num = {}
startSym = 'My-Start-Symbol'
prodRules = {startSym: []}
retType = {}
depFunExpr = {startSym: [[] for i in range(100)]}
listAllFunExpr = []


class FunExpr:
    def __init__(self, term, expr, leng):
        super().__init__()
        self.term = term
        self.expr = expr
        self.leng = leng
        self.lExp = len(str(expr))


def stripComments(bmFile):
    noComments = "(\n"
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + "\n)"


def parseRule(expr):

    idx, idy = 0, 0
    listT = []

    def g(e):
        if type(e) == list:
            ret = [g(w) for w in e[1:]]
            return lambda *a: e[:1] + [gg(*a) for gg in ret]
        elif type(e) == tuple:
            return lambda *a: e
        elif e in prodRules:
            nonlocal idy
            idy += 1
            listT.append(e)
            return lambda *a, i=idy - 1: a[i]
        else:
            return lambda *a: e

    s = (expr, listT, g(expr))
    # print('qwq',expr,listT)
    # if type(expr)==list and expr[0]=='bvnot':
    #     print(s[2]('x')((['BitVec',('Int',64)],0)))
    return s


def synFun2Def(expr):
    global synFunExpr
    return ['define-fun'] + synFunExpr[1:4] + [expr]


def genDepExpr(term, dep):
    # print('term:',term,'dep:',dep)
    for expr, listT, exprF in prodRules[term]:
        numT = len(listT)
        listFE = [None] * numT

        def dfsExpr(idx, leng):
            global tot
            tot += 1
            if idx == numT:
                if leng != dep:
                    return
                if type(expr) == list and numT == 2 and len(expr) == 3:
                    if (
                        expr[0] == 'and'
                        or expr[0] == 'or'
                        or expr[0] == '+'
                        or expr[0] == '*'
                        or expr[0] == '='
                    ) and listFE[0].lExp > listFE[1].lExp:
                        return

                newExpr = exprF(*[w.expr for w in listFE])
                # print('newExpr:',newExpr)

                fe = FunExpr(term, newExpr, dep)
                depFunExpr[term][dep].append(fe)
            else:
                dn = 1
                up = dep - leng - (numT - (idx + 1))
                if up < dn:
                    return
                if idx == numT - 1:
                    dn = up
                for cur in range(dn, up + 1):
                    for ef in depFunExpr[listT[idx]][cur]:
                        # print('idx:',idx,'numT',numT)
                        listFE[idx] = ef
                        dfsExpr(idx + 1, leng + cur)

        dfsExpr(0, 1)


def outpExpr(expr):
    fullExpr = synFun2Def(expr)
    # print('expr', expr)
    # print('fullExpr', fullExpr)
    strExpr = translator.toString(fullExpr, ForceBracket=True)
    # print(strExpr)
    return strExpr


def solve(bmExpr):
    global tot, synFunExpr, synFunName, synFunName2Num, startSym, prodRules, retType
    global depFunExpr, listAllFunExpr
    checker = translator.ReadQuery(bmExpr)

    for expr in bmExpr:

        if expr[0] == 'synth-fun':
            synFunExpr = expr
            synFunName = expr[1]
            for i, e in enumerate(expr[2]):
                synFunName2Num[e[0]] = i

    # print(allFInp)
    retType = {startSym: synFunExpr[3]}

    # print('qwq',evalExpr(['bvand',(['BitVec',('Int',64)],3),(['BitVec',('Int',64)],6)]))

    for term in synFunExpr[4]:
        tName = term[0]
        prodRules[tName] = []

    for term in synFunExpr[4]:
        # print(term)
        tName = term[0]
        tType = term[1]

        if tType == retType[startSym]:
            prodRules[startSym].append(parseRule(tName))

        retType[tName] = tType
        for expr in term[2]:
            prodRules[tName].append(parseRule(expr))
        depFunExpr[tName] = [[] for i in range(100)]

    if len(synFunExpr[4]) == 1:
        prodRules.pop(startSym)
        startSym = synFunExpr[4][0][0]

    for dep in range(1, 40):
        for term in prodRules.keys():
            # print(term)
            genDepExpr(term, dep)
        for funExpr in depFunExpr[startSym][dep]:
            # print('dep:', dep, 'expr:', funExpr.expr)
            strExpr = outpExpr(funExpr.expr)
            if checker.check(strExpr) is None:
                print(strExpr)
                return
            # print(tot, len(depFunExpr[startSym][dep]))


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
    solve(bmExpr)
