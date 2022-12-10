import sys
import sexp
import pprint
import translator
import bv, fallback, lib


def stripComments(bmFile):
    noComments = "(\n"
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + "\n)"


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[
        0
    ]  # Parse string to python list

    typ = None
    for expr in bmExpr:
        if type(expr) is list:
            if expr[0] == 'set-logic':
                typ = expr[1]
                break

    if typ == 'BV' or typ == 'LIA':
        try:
            if typ == 'BV':
                bv.solve(bmExpr)
            else:
                lib.genAnswer(bmExpr)
        except Exception:
            fallback.solve(bmExpr)
        finally:
            exit(0)
    else:
        fallback.solve(bmExpr)
