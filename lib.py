


import sys
import sexp
import translator
import numpy as np
import z3



liaAllLambda = {
    'not': lambda x: np.logical_not(x),
    'and': lambda x, y: np.logical_and(x,y),
    'or': lambda x, y: np.logical_or(x,y),
    '+': lambda x, y: x + y,
    '-': lambda x, y: x - y,
    '*': lambda x, y: x * y,
    'mod': lambda x, y: x % y,
    '<=': lambda x, y: x <= y,
    '>=': lambda x, y: x >= y,
    '<': lambda x, y: x < y,
    '>': lambda x, y: x > y,
    '=': lambda x, y: x == y,
    '=>': lambda x, y: y if x else True,
    'ite': lambda x, y, z: y if x else z
}

AllFunctions = liaAllLambda.copy()

listConstraint = []

AllExamplesInput=[]
# AllExamplesOutput=[]
AllExampleCnt=0


startSym = None
prodRules = {}

depFunExpr = {}

listAllFunExpr=[]

synFunName2Num = {}
decName2Num = {}
declaredNames = []

class FunExpr:
    def __init__(self, term, expr, length, func):
        super().__init__()
        self.term = term
        self.expr = expr
        self.length = length
        self.func = func

class treeNode:
    def __init__(self, ls, rs, classFunc, evalFunc, todoExamples):
        super().__init__()
        self.ls = ls
        self.rs = rs
        self.classFunc = classFunc
        self.evalFunc = evalFunc
        self.todoExamples = todoExamples
    
    def reinit(self, ls, rs, classFunc, evalFunc, todoExamples):
        self.ls = ls
        self.rs = rs
        self.classFunc = classFunc
        self.evalFunc = evalFunc
        self.todoExamples = todoExamples
    
    def isLeaf(self):
        return self.ls == None and self.rs == None
    
    def getNext(self, x):
        return self.ls if listAllFunExpr[self.classFunc].func(*x) else self.rs

def stripComments(bmFile):
    noComments = "(\n"
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + "\n)"


def parseRule(expr):

    idx, idy = 0, 0
    listT = []

    def f(e):
        if type(e) == list:
            ret = [f(w) for w in e[1:]]
            oprF = AllFunctions[e[0]]
            return lambda *a: lambda *b: oprF(*[ff(*a)(*b) for ff in ret])
        elif type(e) == tuple:
            return lambda *a: lambda *b: np.int64(e[1])
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
    return s


def genDepExpr(term, dep):

    # print('term:',term,'dep:',dep)

    for expr, listT, funF, exprF in prodRules[term]:
        numT = len(listT)
        listFE = [None] * numT

        def dfsExpr(idx, leng):
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
                    ) and listFE[0].__hash__() > listFE[1].__hash__():
                        return

                newExpr = exprF(*[w.expr for w in listFE])
                fl = [w.func for w in listFE]
                newF = lambda *a, tf=funF: tf(*fl)(*a)
                fe = FunExpr(term, newExpr, dep, newF)
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

def synFun2Def(expr):
    global synFunExpr
    return ['define-fun'] + synFunExpr[1:4] + [expr]

def outpExpr(expr):
    fullExpr = synFun2Def(expr)
    strExpr = translator.toString(fullExpr, ForceBracket=True)
    # print(strExpr)
    return strExpr

def walkTree(node, x):
    if node.isLeaf():
        return node
    return walkTree(node.getNext(x), x)


def getTreeExpr(node):
    if node.isLeaf():
        return listAllFunExpr[node.evalFunc].expr
    else:
        lExpr = getTreeExpr(node.ls)
        rExpr = getTreeExpr(node.rs)
        return ['ite', listAllFunExpr[node.classFunc].expr, lExpr, rExpr]


genDep = 0
finalExpr = []
example2Expr = []

def genCounterExample(Str):
    cexample = checker.check(Str)
    if cexample == None:
        return None
    ret = []
    for param in declaredNames:
        # TODO what if it is not Int?
        if cexample[z3.Int(param)] == None:
            ret.append(0)
        else:
            ret.append(int(str(cexample[z3.Int(param)])))   # TODO ugly
    return ret

def evalExpr(expr, exampleinput):
    if type(expr) == list:
        ret = [evalExpr(term, exampleinput) for term in expr[1:]]
        return AllFunctions[expr[0]](*ret)
    elif type(expr) == tuple:
        return expr[1]
    else:
        return exampleinput[decName2Num[expr]]

def checkCons(funcexpr, example):
    ret = True
    AllFunctions[synFunName] = funcexpr.func
    for expr in listConstraint:
        if not evalExpr(expr, example):
            ret = False
            break
    AllFunctions[synFunName] = None
    return ret

def addExample(exampleInput):
    global AllExamplesInput
    global AllExampleCnt
    global listAllFunExpr
    global genDep
    for i, inparam in enumerate(exampleInput):
        AllExamplesInput[i] = np.append(AllExamplesInput[i], inparam)
    
    AllExampleCnt += 1
    feSet = set()   # avaliable expr for this example.
    for i, funcexpr in enumerate(listAllFunExpr):
        if funcexpr.term != startSym:
            continue
        # NOTE check constraints with target = funcexpr and input = exampleInput
        if checkCons(funcexpr, exampleInput):
            feSet.add(i)
    example2Expr.append(feSet)
    while not example2Expr[-1]:
        genDep += 1
        for term in prodRules.keys():
            genDepExpr(term, genDep)
            for fe in depFunExpr[term][genDep]:
                listAllFunExpr.append(fe)
                if fe.term == startSym:
                    feidx = len(listAllFunExpr)-1
                    for exid in range(AllExampleCnt):
                        exinput = [inputlist[exid] for inputlist in AllExamplesInput]
                        if checkCons(fe, exinput):
                            example2Expr[exid].add(feidx)
    


if __name__ == "__main__":
    
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
    checker = translator.ReadQuery(bmExpr)

    for expr in bmExpr:
        if expr[0] == 'synth-fun':
            synFunExpr = expr
            synFunName = expr[1]
            for i, e in enumerate(expr[2]): # Params
                synFunName2Num[e[0]] = i
        elif expr[0] == 'define-fun':
            # no define-fun in open_tests
            # TODO

            pass
        elif expr[0] == 'declare-var':
            decName2Num[expr[1]]=len(declaredNames)
            declaredNames.append(expr[1])
            AllExamplesInput.append(np.array([], dtype='int64'))
        elif expr[0] == 'constraint':
            listConstraint.append(expr[1])
    

    targetRetType = synFunExpr[3]

    for term in synFunExpr[4]:
        tName = term[0]
        prodRules[tName] = []   # add tName to Rules

    for term in synFunExpr[4]:  # Start and StartBool
        tName = term[0]
        tType = term[1]

        if tType == targetRetType:
            assert startSym == None
            startSym = tName
        
        # retType[tName] = tType
        for expr in term[2]:
            
            # expr: like (* Start Start)
            # NOTE no ite in Expr.
            if type(expr) == list and expr[0] == 'ite':
                continue
            prodRules[tName].append(parseRule(expr))
        
        depFunExpr[tName] = [[] for _ in range(100)]
    
    genDep = 1
    for term in prodRules.keys():
        genDepExpr(term, genDep)
        for fe in depFunExpr[term][genDep]:
            listAllFunExpr.append(fe)
            if fe.term == startSym:
                feidx = len(listAllFunExpr)-1
                for exid in range(AllExampleCnt):
                    exinput = [inputlist[i] for inputlist in AllExamplesInput]
                    if checkCons(fe, exinput):
                        example2Expr[exid].add(feidx)
    
    treeRoot = treeNode(None, None, None, 0, [])
    finalExpr = getTreeExpr(treeRoot)
    cexample = genCounterExample(outpExpr(finalExpr))
    while cexample != None:
        addExample(cexample)    # find an expr for cexample, update ret
        
        lsCons = [(i, len(ls)) for i, ls in enumerate(example2Expr)]
        lsCons = sorted(lsCons, key=lambda x: x[1])
        treeRoot = treeNode(None, None, None, None, [])
        for i, _ in lsCons:
            inp = [inputlist[i] for inputlist in AllExamplesInput]  # pick the i th input
            node = walkTree(treeRoot, inp)
            if node.evalFunc is None:
                for w in sorted(list(example2Expr[i])):
                    node.evalFunc = w
                    break
            if node.evalFunc in example2Expr[i]:
                node.todoExamples.append(i)
                continue
            arrInp = [inputlist[node.todoExamples] for inputlist in AllExamplesInput]
            evalI = None
            for w in sorted(list(example2Expr[i])):
                evalI = w
                break
            # print('evalI:',evalI)

            fg = False
            for idFE, fe in enumerate(listAllFunExpr):
                if fe.term == startSym:
                    # TODO tricky
                    continue
                arr1 = fe.func(*arrInp)
                i1 = fe.func(*inp) == True
                if np.all(arr1) and not i1:
                    lsNode = treeNode(None, None, None, node.evalFunc, node.todoExamples)
                    rsNode = treeNode(None, None, None, evalI, [i])
                    node.reinit(lsNode, rsNode, idFE, None, [])
                    fg = True
                    break
                elif not np.any(arr1) and i1:
                    lsNode = treeNode(None, None, None, evalI, [i])
                    rsNode = treeNode(None, None, None, node.evalFunc, node.todoExamples)
                    node.reinit(lsNode, rsNode, idFE, None, [])
                    fg = True
                    break

            while not fg:
                genDep += 1
                startId = len(listAllFunExpr)
                for term in prodRules.keys():
                    genDepExpr(term, genDep)
                    for fe in depFunExpr[term][genDep]:
                        listAllFunExpr.append(fe)
                        if fe.term == startSym:
                            feidx = len(listAllFunExpr)-1
                            for exid in range(AllExampleCnt):
                                exinput = [inputlist[i] for inputlist in AllExamplesInput]
                                if checkCons(fe, exinput):
                                    example2Expr[exid].add(feidx)
                for tid, fe in enumerate(listAllFunExpr[startId:]):
                    idFE = tid + startId
                    if fe.term == startSym:
                        # TODO tricky
                        continue
                    arr1 = fe.func(*arrInp)
                    i1 = fe.func(*inp) == True
                    if np.all(arr1) and not i1:
                        lsNode = treeNode(None, None, None, node.evalFunc, node.todoExamples)
                        rsNode = treeNode(None, None, None, evalI, [i])
                        node.reinit(lsNode, rsNode, idFE, None, [])
                        fg = True
                        break
                    elif not np.any(arr1) and i1:
                        lsNode = treeNode(None, None, None, evalI, [i])
                        rsNode = treeNode(None, None, None, node.evalFunc, node.todoExamples)
                        node.reinit(lsNode, rsNode, idFE, None, [])
                        fg = True
                        break
        finalExpr = getTreeExpr(treeRoot)
        cexample = genCounterExample(outpExpr(finalExpr))
    print(outpExpr(finalExpr))

    



