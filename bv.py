import sys
import sexp
import pprint
import translator
import functools


mask = (1 << 64) - 1
bvFun = {
    'bvnot': lambda x: x ^ mask,
    'bvand': lambda x, y: x & y,
    'bvor': lambda x, y: x | y,
    'bvxor': lambda x, y: x ^ y,
    'bvadd': lambda x, y: (x + y) & mask,
    'bvlshr': lambda x, y: x >> y,
    'bvshl': lambda x, y: (x << y) & mask,
    'not': lambda x: not x,
    'and': lambda x, y: x and y,
    'or': lambda x, y: x or y,
    '+': lambda x, y: x + y,
    '-': lambda x, y: x - y,
    '*': lambda x, y: x * y,
    'mod': lambda x, y: x % y,
    '<=': lambda x, y: x <= y,
    '>=': lambda x, y: x >= y,
    '=': lambda x, y: x == y,
    'ite': lambda x, y, z: y if x else z,
}
allFun = bvFun.copy()
tot = 0
cons = []
allFInp = []
synFunExpr = []
synFunName = ''
synFunName2Num = {}
startSym = 'My-Start-Symbol'
prodRules = {startSym: []}
retType = {}

setFunExpr = {startSym: set()}
depFunExpr = {startSym: [[] for i in range(100)]}


class FunExpr:
    def __init__(self, term, expr, leng, f, ret):
        super().__init__()
        self.term = term
        self.expr = expr
        self.leng = leng
        self.f = f
        self.ret = tuple(ret)
        self.hs = hash(self.ret)

    def __hash__(self):
        return self.hs

    def __eq__(self, other):
        if type(other) == FunExpr:
            if self.hs != other.hs:
                return False
            return self.ret == other.ret
        return False


def stripComments(bmFile):
    noComments = "(\n"
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + "\n)"


def mergeFunExpr(term, opr, *args):
    newExpr = [opr] + [fe.expr for fe in args]
    newLen = 1 + sum((fe.leng for fe in args))
    oprF = allFun[opr]
    newF = lambda *a: oprF(*[fe.f(*a) for fe in args])
    newRet = map(oprF, zip(*[fe.ret for fe in args]))
    return FunExpr(term, newExpr, newLen, newF, newRet)


def getFun(expr):
    assert expr[0] == 'define-fun'
    inFormat = expr[2]
    fun = expr[4]
    numIn = len(inFormat)
    name2Num = {}

    for i, v in enumerate(inFormat):
        name2Num[v[0]] = i

    def f(expr):
        if type(expr) == list:
            ret = [f(e) for e in expr[1:]]
            oprF = allFun[expr[0]]
            return lambda *a: oprF(*[f(*a) for f in ret])
        elif type(expr) == tuple:
            return lambda *a: expr[1]
        else:
            return lambda *a, i=name2Num[expr]: a[i]

    return f(fun)


def evalExpr(expr):
    if type(expr) == list:
        ret = [evalExpr(term) for term in expr[1:]]
        return allFun[expr[0]](*ret)
    elif type(expr) == tuple:
        return expr[1]
    else:
        assert False


def parseDefFun(expr):
    name = expr[1]
    allFun[name] = getFun(expr)


def parseCons(expr):
    if type(expr) == list:
        if expr[0] == synFunName:
            allFInp.append(expr)
        for e in expr[1:]:
            parseCons(e)


def parseRule(expr):

    idx, idy = 0, 0
    listT = []

    def f(e):
        if type(e) == list:
            ret = [f(w) for w in e[1:]]
            oprF = allFun[e[0]]
            return lambda *a: lambda *b: oprF(*[ff(*a)(*b) for ff in ret])
        elif type(e) == tuple:
            return lambda *a: lambda *b: e[1]
        elif e in prodRules:
            nonlocal idx
            idx += 1
            return lambda *a, i=idx - 1: a[i]
        else:
            return lambda *a, i=synFunName2Num[e]: lambda *b: b[i]

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

    s = (expr, listT, f(expr), g(expr))
    # print('qwq',expr,listT)
    # if type(expr)==list and expr[0]=='bvnot':
    #     print(s[2]('x')((['BitVec',('Int',64)],0)))
    return s


def calAllInp(f):
    allFun[synFunName] = f
    ret = [evalExpr(expr) for expr in allFInp]
    allFun[synFunName] = None
    return ret


def synFun2Def(expr):
    global synFunExpr
    return ['define-fun'] + synFunExpr[1:4] + [expr]


def genDepExpr(term, dep):
    # print('term:',term,'dep:',dep)
    for expr, listT, funF, exprF in prodRules[term]:
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
                        expr[0] == 'bvand'
                        or expr[0] == 'bvor'
                        or expr[0] == 'bvxor'
                        or expr[0] == 'bvadd'
                    ) and listFE[0].__hash__() > listFE[1].__hash__():
                        return

                newExpr = exprF(*[w.expr for w in listFE])
                # print('newExpr:',newExpr)
                fl = [w.f for w in listFE]
                # print('fl:',fl)
                newF = lambda *a, tf=funF: tf(*fl)(*a)
                if type(expr) == list and numT + 1 == len(expr) and expr[0] in allFun:
                    tf = allFun[expr[0]]
                    newRet = [tf(*w) for w in zip(*[fe.ret for fe in listFE])]
                else:
                    newRet = calAllInp(newF)
                # print('newRet:',newRet)
                fe = FunExpr(term, newExpr, dep, newF, newRet)
                if fe not in setFunExpr[term]:
                    setFunExpr[term].add(fe)
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


def checkFun(f):
    allFun[synFunName] = f
    for expr in cons:
        if not evalExpr(expr):
            allFun[synFunName] = None
            return False
    allFun[synFunName] = None
    return True


def outpExpr(expr):
    fullExpr = synFun2Def(expr)
    print('expr', expr)
    print('fullExpr', fullExpr)
    strExpr = translator.toString(fullExpr)
    print(strExpr)


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]

    for expr in bmExpr:
        print(expr)
        if expr[0] == 'synth-fun':
            synFunExpr = expr
            synFunName = expr[1]
            mask = (1 << expr[3][1][1]) - 1
            for i, e in enumerate(expr[2]):
                synFunName2Num[e[0]] = i
        elif expr[0] == 'define-fun':
            parseDefFun(expr)
        elif expr[0] == 'constraint':
            parseCons(expr[1])
            cons.append(expr[1])

    retType = {startSym: synFunExpr[3]}

    # print('qwq',evalExpr(['bvand',(['BitVec',('Int',64)],3),(['BitVec',('Int',64)],6)]))

    for term in synFunExpr[4]:
        tName = term[0]
        prodRules[tName] = []

    for term in synFunExpr[4]:
        print(term)
        tName = term[0]
        tType = term[1]

        if tType == retType[startSym]:
            prodRules[startSym].append(parseRule(tName))

        retType[tName] = tType
        for expr in term[2]:
            prodRules[tName].append(parseRule(expr))
        setFunExpr[tName] = set()
        depFunExpr[tName] = [[] for i in range(100)]

    if len(synFunExpr[4]) == 1:
        prodRules.pop(startSym)
        startSym = synFunExpr[4][0][0]

    for dep in range(1, 12):
        for term in prodRules.keys():
            print(term)
            genDepExpr(term, dep)
        for funExpr in depFunExpr[startSym][dep]:
            print('dep:', dep, 'expr:', funExpr.expr)
            if checkFun(funExpr.f):
                outpExpr(funExpr.expr)
                exit(0)
        print(tot, len(depFunExpr[startSym][dep]))
