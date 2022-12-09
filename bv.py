import sys
import sexp
import pprint
import translator
import numpy as np


mask = (1 << 64) - 1
bvFun = {
    'bvnot': lambda x: x ^ mask,
    'bvand': lambda x, y: x & y,
    'bvor': lambda x, y: x | y,
    'bvxor': lambda x, y: x ^ y,
    'bvadd': lambda x, y: x + y,
    'bvlshr': lambda x, y: x >> y,
    'bvshl': lambda x, y: x << y,
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
    'ite': lambda x, y, z: (x != 0) * y + (x == 0) * z,
}
allFun = bvFun.copy()
tot = 0
cons = []
allFInp = []
allFOutp = []
synFunExpr = []
synFunName = ''
synFunName2Num = {}
startSym = 'My-Start-Symbol'
prodRules = {startSym: []}
retType = {}
hashMul = []
setFunExpr = {startSym: set()}
depFunExpr = {startSym: [[] for i in range(100)]}
listAllFunExpr = []
exprCons = []


class FunExpr:
    def __init__(self, term, expr, leng, f, ret):
        super().__init__()
        self.term = term
        self.expr = expr
        self.leng = leng
        self.f = f
        self.ret = np.array(ret, dtype='uint64')
        self.hs = int((self.ret * hashMul).sum())

    def __hash__(self):
        return self.hs

    def __eq__(self, other):
        if type(other) == FunExpr:
            if self.hs != other.hs:
                return False
            return np.all(self.ret == other.ret)
        return False


class treeNode:
    def __init__(self, ls, rs, classFun, evalFun, consL):
        super().__init__()
        self.ls = ls
        self.rs = rs
        self.classFun = classFun
        self.evalFun = evalFun
        self.consL = consL

    def reinit(self, ls, rs, classFun, evalFun, consL):
        self.ls = ls
        self.rs = rs
        self.classFun = classFun
        self.evalFun = evalFun
        self.consL = consL

    def isLeaf(self):
        return self.ls == None and self.rs == None

    def getNext(self, x):
        return self.ls if listAllFunExpr[self.classFun].f(x) == 1 else self.rs


def stripComments(bmFile):
    noComments = "(\n"
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + "\n)"


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
            return lambda *a: np.uint64(expr[1])
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
    # if type(expr) == list:
    #     if expr[0] == synFunName:
    #         allFInp.append(expr)
    #     for e in expr[1:]:
    #         parseCons(e)
    allFInp.append(expr[1][1][1])
    allFOutp.append(expr[2][1])


def parseRule(expr):

    idx, idy = 0, 0
    listT = []

    def f(e):
        if type(e) == list:
            ret = [f(w) for w in e[1:]]
            oprF = allFun[e[0]]
            return lambda *a: lambda *b: oprF(*[ff(*a)(*b) for ff in ret])
        elif type(e) == tuple:
            return lambda *a: lambda *b: np.uint64(e[1])
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
                    # tf = allFun[expr[0]]
                    # newRet = [tf(*w) for w in zip(*[fe.ret for fe in listFE])]
                    # print("expr:", expr[0])
                    # print(*[fe.ret for fe in listFE])
                    newRet = allFun[expr[0]](*[fe.ret for fe in listFE])
                else:
                    # newRet = calAllInp(newF)
                    newRet = newF(allFInp)
                    # print('newRet:', newRet)
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
    # allFun[synFunName] = f
    # for expr in cons:
    #     if not evalExpr(expr):
    #         allFun[synFunName] = None
    #         return False
    # allFun[synFunName] = None
    # return True
    return np.all(f.ret == allFOutp)


def outpExpr(expr):
    fullExpr = synFun2Def(expr)
    # print('expr', expr)
    # print('fullExpr', fullExpr)
    strExpr = translator.toString(fullExpr, ForceBracket=True)
    print(strExpr)
    return strExpr


def walkTree(node, x):
    if node.isLeaf():
        return node
    return walkTree(node.getNext(x), x)


def getTreeExpr(node):
    if node.isLeaf():
        return listAllFunExpr[node.evalFun].expr
    else:
        lExpr = getTreeExpr(node.ls)
        rExpr = getTreeExpr(node.rs)
        return ['if0', listAllFunExpr[node.classFun].expr, lExpr, rExpr]


if __name__ == '__main__':
    np.seterr(all="ignore")
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
    checker = translator.ReadQuery(bmExpr)

    for expr in bmExpr:
        # print(expr)
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

    hashMul = np.array(
        [pow(19260817, i, 1 << 64) for i in range(len(allFInp))], dtype='uint64'
    )
    remCons = len(allFInp)
    exprCons = [set() for i in range(remCons)]
    allFInp = np.array(allFInp, dtype='uint64')
    allFOutp = np.array(allFOutp, dtype='uint64')
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
            if type(expr) == list and expr[0] == 'if0':
                continue
            prodRules[tName].append(parseRule(expr))
        setFunExpr[tName] = set()
        depFunExpr[tName] = [[] for i in range(100)]

    if len(synFunExpr[4]) == 1:
        prodRules.pop(startSym)
        startSym = synFunExpr[4][0][0]

    # for dep in range(1, 12):
    #     for term in prodRules.keys():
    #         print(term)
    #         genDepExpr(term, dep)
    #     for funExpr in depFunExpr[startSym][dep]:
    #         print('dep:', dep, 'expr:', funExpr.expr)
    #         if checkFun(funExpr):
    #             outpExpr(funExpr.expr)
    #             exit(0)
    #     print(tot, len(depFunExpr[startSym][dep]))

    genDep = 0

    for dep in range(1, 20):
        for term in prodRules.keys():
            genDepExpr(term, dep)
        genDep = dep
        for fe in depFunExpr[startSym][dep]:
            idxFE = len(listAllFunExpr)
            listAllFunExpr.append(fe)
            outp = fe.ret == allFOutp
            pos = list(np.where(outp)[0])
            for p in pos:
                if len(exprCons[p]) == 0:
                    remCons -= 1
                exprCons[p].add(idxFE)
        if remCons == 0:
            # for ls in exprCons:
            #     print(ls)
            break

    # for dep in range(genDep+1,10):
    #     for term in prodRules.keys():
    #         genDepExpr(term, dep)

    lsCons = [(i, len(ls)) for i, ls in enumerate(exprCons)]
    lsCons = sorted(lsCons, key=lambda x: x[1])
    treeRoot = treeNode(None, None, None, None, [])
    for i, _ in lsCons:
        inp, outp = allFInp[i], allFOutp[i]
        node = walkTree(treeRoot, inp)
        if node.evalFun is None:
            for w in exprCons[i]:
                node.evalFun = w
                break
        if node.evalFun in exprCons[i]:
            node.consL.append(i)
            continue
        arrInp = allFInp[node.consL]
        arrOutp = allFOutp[node.consL]
        evalI = None
        for w in exprCons[i]:
            evalI = w
            break
        # print('evalI:',evalI)

        fg = False
        for idFE, fe in enumerate(listAllFunExpr):
            arr1 = fe.f(arrInp) == 1
            i1 = fe.f(inp) == 1
            if np.all(arr1) and not i1:
                lsNode = treeNode(None, None, None, node.evalFun, node.consL)
                rsNode = treeNode(None, None, None, evalI, [i])
                node.reinit(lsNode, rsNode, idFE, None, [])
                fg = True
                break
            elif not np.any(arr1) and i1:
                lsNode = treeNode(None, None, None, evalI, [i])
                rsNode = treeNode(None, None, None, node.evalFun, node.consL)
                node.reinit(lsNode, rsNode, idFE, None, [])
                fg = True
                break

        while not fg:
            # print('qwqwqwqw')
            genDep += 1
            for term in prodRules.keys():
                genDepExpr(term, genDep)
            startId = len(listAllFunExpr)
            # print('startID', startId)
            for fe in depFunExpr[startSym][genDep]:
                listAllFunExpr.append(fe)
            for tid, fe in enumerate(listAllFunExpr[startId:]):
                idFE = tid + startId
                arr1 = fe.f(arrInp) == 1
                i1 = fe.f(inp) == 1
                if np.all(arr1) and not i1:
                    lsNode = treeNode(None, None, None, node.evalFun, node.consL)
                    rsNode = treeNode(None, None, None, evalI, [i])
                    node.reinit(lsNode, rsNode, idFE, None, [])
                    fg = True
                    break
                elif not np.any(arr1) and i1:
                    lsNode = treeNode(None, None, None, evalI, [i])
                    rsNode = treeNode(None, None, None, node.evalFun, node.consL)
                    node.reinit(lsNode, rsNode, idFE, None, [])
                    fg = True
                    break

    expr = getTreeExpr(treeRoot)
    # print(expr)
    assert checker.check(outpExpr(expr)) is None
