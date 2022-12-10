


import sys
import sexp
import translator
import numpy as np
import z3
import random

synFunName = ""
synFunExpr = []

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

dec2Param = {}

class FunExpr:
    def __init__(self, term, expr, length, func):
        super().__init__()
        self.term = term    # Start or StartBool
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
    print(strExpr)
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
evalexpr2Examples = {}
boolexpr2Examples = {}

# ---- check if funcexpr is a valid output for example ----

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

# ---- check if funcexpr is a valid output for example ----


# ---- gen counter example and tackle it ----
def genCounterExample(Str, checker):
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

def addExample(exampleInput):

    # add a counterexample and find corresponding expr for it.

    global AllExampleCnt
    global genDep
    findValidExpr = False
    AllExamplesInput.append(exampleInput)
    for i, funcexpr in enumerate(listAllFunExpr):
        if funcexpr.term != startSym:
            if funcexpr.func(*example2Param(exampleInput)):
                boolexpr2Examples[i].add(AllExampleCnt)
            continue
        # NOTE check constraints with target = funcexpr and input = exampleInput
        if checkCons(funcexpr, exampleInput):
            evalexpr2Examples[i].add(AllExampleCnt)
            findValidExpr = True
    AllExampleCnt += 1
    while not findValidExpr:
        genDep += 1
        for term in prodRules.keys():
            genDepExpr(term, genDep)
            for fe in depFunExpr[term][genDep]:
                listAllFunExpr.append(fe)
                if fe.term == startSym:
                    feidx = len(listAllFunExpr)-1
                    evalexpr2Examples[feidx] = set()
                    for i, exinput in enumerate(AllExamplesInput):
                        if checkCons(fe, exinput):
                            evalexpr2Examples[feidx].add(i)
                            if i == AllExampleCnt-1:
                                findValidExpr = True
                else:
                    feidx = len(listAllFunExpr)-1
                    boolexpr2Examples[feidx] = set()
                    for i, exinput in enumerate(AllExamplesInput):
                        if fe.func(*example2Param(exinput)):
                            boolexpr2Examples[feidx].add(i)
# ---- gen counter example and tackle it ----


def splitExample(exampleSet, listCanExpr):
    Cnt = 0; retList = []
    doneExamples = set()
    while len(doneExamples) < len(exampleSet):
        maxscore = 0.0
        maxid = -1
        for feidx in listCanExpr:
            id = feidx
            exset = evalexpr2Examples[id] & exampleSet
            score = len(exset-doneExamples)/listAllFunExpr[id].length
            # print(listAllFunExpr[feidx].expr, score)
            if maxscore < score:
                maxid = id
                maxscore = score
        assert maxid >= 0
        retList.append(maxid)
        Cnt += 1
        doneExamples = doneExamples | (evalexpr2Examples[maxid] & exampleSet)
    return Cnt, retList

def buildTree(node:treeNode, listCanExpr:list):
    global genDep
    # print("Node:", node.todoExamples, listCandidateExpr)
    curClassCnt = len(listCanExpr)
    assert curClassCnt >= 1
    if curClassCnt == 1:
        node.evalFunc = listCanExpr[0]
    else:
        assert len(node.todoExamples) > 1
        lsNode = None
        rsNode = None
        lsClassList = []
        rsClassList = []
        foundClassFunc = False
        for feidx, fe in enumerate(listAllFunExpr):
            if fe.term == startSym:
                continue
            # NOTE term==StartBool if not startSym
            lsSet = node.todoExamples & boolexpr2Examples[feidx]
            rsSet = node.todoExamples - boolexpr2Examples[feidx]
            if not (lsSet and rsSet):
                continue
            lsClassCnt, lsClassList = splitExample(lsSet, listCanExpr)
            rsClassCnt, rsClassList = splitExample(rsSet, listCanExpr)
            assert rsClassCnt>0 and lsClassCnt>0
            if (lsClassCnt<curClassCnt and rsClassCnt<curClassCnt):
                lsNode = treeNode(None, None, None, None, lsSet)
                rsNode = treeNode(None, None, None, None, rsSet)
                node.reinit(lsNode, rsNode, feidx, None, node.todoExamples)
                foundClassFunc = True
                break
        while not foundClassFunc:
            startId = len(listAllFunExpr)
            genDep += 1
            for term in prodRules.keys():
                genDepExpr(term, genDep)
                for fe in depFunExpr[term][genDep]:
                    listAllFunExpr.append(fe)
                    if fe.term == startSym:
                        feidx = len(listAllFunExpr)-1
                        evalexpr2Examples[feidx] = set()
                        for i, exinput in enumerate(AllExamplesInput):
                            if checkCons(fe, exinput):
                                evalexpr2Examples[feidx].add(i)
                    else:
                        feidx = len(listAllFunExpr)-1
                        boolexpr2Examples[feidx] = set()
                        for i, exinput in enumerate(AllExamplesInput):
                            if fe.func(*example2Param(exinput)):
                                boolexpr2Examples[feidx].add(i)
            for idx, fe in enumerate(listAllFunExpr[startId:]):
                feidx = idx + startId
                if fe.term == startSym:
                    continue
                # NOTE term==StartBool if not startSym
                lsSet = node.todoExamples & boolexpr2Examples[feidx]
                rsSet = node.todoExamples - boolexpr2Examples[feidx]
                if not (lsSet and rsSet):
                    continue
                lsClassCnt, lsClassList = splitExample(lsSet, listCanExpr)
                rsClassCnt, rsClassList = splitExample(rsSet, listCanExpr)
                if fe.expr[0] == 'and' and fe.expr[1] == ['>=', 'y', 'x']:
                    print(fe.expr, lsSet, rsSet, lsClassList, rsClassList)
                assert rsClassCnt>0 and lsClassCnt>0
                if (lsClassCnt<curClassCnt and rsClassCnt<curClassCnt):
                    lsNode = treeNode(None, None, None, None, lsSet)
                    rsNode = treeNode(None, None, None, None, rsSet)
                    node.reinit(lsNode, rsNode, feidx, None, node.todoExamples)
                    foundClassFunc = True
                    break
        assert lsNode!=None
        assert rsNode!=None
        buildTree(lsNode, lsClassList)
        buildTree(rsNode, rsClassList)
    
paramList = None
def searchParam(expr):
    global paramList
    if type(expr) == list:
        if expr[0] == synFunName:
            if paramList == None:
                paramList = expr[1:]
            elif paramList != expr[1:]:
                raise ValueError("Inconsistent params")
        else:
            for e in expr:
                searchParam(e)
            

def getParamGen(expr):
    if type(expr) == list:
        ret = [getParamGen(e) for e in expr[1:]]
        oprF = AllFunctions[expr[0]]
        return lambda *a: oprF(*[f(*a) for f in ret])
    elif type(expr) == tuple:
        return lambda *a: np.int64(expr[1])
    else:
        return lambda *a, i=decName2Num[expr]: a[i]


genParam = []

def example2Param(exinput):
    global genParam
    return [func(*exinput) for func in genParam]

def genAnswer(bmExpr):

    global synFunName
    global synFunExpr
    global startSym
    global genParam


    checker = translator.ReadQuery(bmExpr)

    for expr in bmExpr:
        if expr[0] == 'synth-fun':
            synFunExpr = expr
            synFunName = expr[1]
            for i, e in enumerate(expr[2]): # Params
                synFunName2Num[e[0]] = i
            genParam = [0]*len(expr[2])
        elif expr[0] == 'define-fun':
            # no define-fun in open_tests
            # TODO

            pass
        elif expr[0] == 'declare-var':
            decName2Num[expr[1]]=len(declaredNames)
            declaredNames.append(expr[1])
        elif expr[0] == 'constraint':
            listConstraint.append(expr[1])
            searchParam(expr[1])
    
    if paramList != None:
        for id, p in enumerate(paramList):
            genParam[id] = getParamGen(p)
    
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
                evalexpr2Examples[feidx] = set()
                for i, exinput in enumerate(AllExamplesInput):
                    if checkCons(fe, exinput):
                        evalexpr2Examples[feidx].add(i)
            else:
                feidx = len(listAllFunExpr)-1
                boolexpr2Examples[feidx] = set()
                for i, exinput in enumerate(AllExamplesInput):
                    if fe.func(*example2Param(exinput)):
                        boolexpr2Examples[feidx].add(i)

    needRandomExample = True

    treeRoot = treeNode(None, None, None, 0, [])
    finalExpr = getTreeExpr(treeRoot)
    cexample = genCounterExample(outpExpr(finalExpr), checker)
    while cexample != None:
        addExample(cexample)    # find an expr for cexample
        
        if needRandomExample:
            for _ in range(50):
                exinput = [random.randrange(-2,15) for _ in range(len(cexample))]
                addExample(exinput)
            needRandomExample = False

        candidateCnt, listCandidateExpr = splitExample(set(range(AllExampleCnt)), list(evalexpr2Examples.keys()))
        # print("----iter----")
        # for i, exinput in enumerate(AllExamplesInput):
        #     print(i, exinput)
        # for feidx in listCandidateExpr:
        #     print(feidx, listAllFunExpr[feidx].expr, evalexpr2Examples[feidx])
        # print("----iter----")
        
        
        treeRoot = treeNode(None, None, None, None, set(range(AllExampleCnt)))
        buildTree(treeRoot, listCandidateExpr)

        finalExpr = getTreeExpr(treeRoot)
        # print(outpExpr(finalExpr))
        cexample = genCounterExample(outpExpr(finalExpr), checker)
        
    assert checker.check(outpExpr(finalExpr)) is None

if __name__ == "__main__":
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]

    genAnswer(bmExpr)
    



