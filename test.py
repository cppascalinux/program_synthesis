import datetime
import os
import os.path
import platform
import subprocess
import sys
import time
import signal
import sexp
import translator
import re
import random

mainprogram = "./main.py"
testroot = "./"
open_bv_tests = testroot + "open_bv_tests/"
open_tests = testroot + "open_tests/"
tmp_test = testroot + "tmp.sl"


class TimeoutError(Exception):
    pass


def stripComments(bmFile):
    noComments = "("
    for line in bmFile:
        line = line.split(";", 1)[0]
        noComments += line
    return noComments + ")"


def run_command(cmd, timeout=60):
    is_linux = platform.system() == "Linux"

    p = subprocess.Popen(
        cmd,
        #stderr=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        #start_new_session=True,
        shell=True,
        preexec_fn=os.setsid if is_linux else None,
    )
    #os.system("taskset -cp 0" + " " + str(p.pid))
    t_beginning = datetime.datetime.now()
    seconds_passed = 0
    try:
        out, err = p.communicate(timeout=timeout)
        timepassed = datetime.datetime.now() - t_beginning
        rtimepassed = timepassed.seconds + timepassed.microseconds / 1000000.0
    except subprocess.TimeoutExpired:
        #p.kill()
        os.killpg(p.pid, signal.SIGKILL)
        raise TimeoutError()
    return out.decode("UTF-8"), rtimepassed
def tokenize_for_bleu_eval(code):
    code = re.sub(r'([^A-Za-z0-9_])', r' \1 ', code)
        #code = re.sub(r'([a-z])([A-Z])', r'\1 \2', code)
    code = re.sub(r'\s+', ' ', code)
    code = code.replace('"', '`')
    code = code.replace('\'', '`')
    tokens = [t for t in code.split(' ') if t]
    return tokens

def is_constraint(line):
    key_list = ["(constraint", "(=", "#x"]
    for key in key_list:
        if key not in line: return False
    return True

def my_test(cmd, outputfile, testname, timeout=300):
    outputfile.write("\t%s:" % (testname))
    res = 0
    benchmarkFile = open(testname, encoding="utf-8")
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[
        0
    ]
    if "(set-logic BV)" in bm:
        with open(tmp_test, "w") as oup:
            for line in bm.split('\n')[1:-1]:
                if is_constraint(line) and random.randint(0, 10) == 0:
                    continue
                oup.write(line + "\n")
        cmd += tmp_test
    else:
        cmd += testname
    # Parse string to python
    #print(cmd)
    print(testname)
    try:
        result, rtime = run_command(cmd, timeout)
        print(result)
    except TimeoutError:
        outputfile.write("timeout after %i \n" % (timeout))
        print("timeout after %i \n" % (timeout))
        return 0
    else:
        resultlst = tokenize_for_bleu_eval(result)
        checker = translator.ReadQuery(bmExpr)
        try:
            checkresult = checker.check(result)
        except:
            print("Invalid format", result)
            # outputfile.write('Wrong Answer: Invalid check result %s(%f)\n' %(result,rtime))
            outputfile.write("Invalid format\t%f\n" % (rtime))
        else:
            if checkresult == None:
                outputfile.write("Passed\t%f\n" % (rtime))
                res = 1
            else:
                print("Wrong ", checkresult)
                # outputfile.write('Wrong Answer: get %s(%f)\n' %(result,rtime))
                outputfile.write("Wrong Answer\t%f\n" % (rtime))
        for x in resultlst:
            if x == "define" or x == "func" or x == "_":
                continue
            if bm.find(x) == -1:
                print(x)
                res = 0.5
                break
        print(res)
        return res


if __name__ == "__main__":
    timeout = 10
    testresultfile = "result.txt"
    outfile = open(testresultfile, "w")
    toexe = mainprogram+" "
    outfile.write( "start testing: \n")
    cmd = "python3 "

    for j, testgroup in enumerate([open_bv_tests, open_tests]):
        for test in os.listdir(testgroup):
            arg = testgroup + test
            s = my_test(cmd + toexe, outfile, arg, timeout)

