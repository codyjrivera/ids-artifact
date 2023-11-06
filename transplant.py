# Supporting Artifact for
# "Predictive Verification using Intrinsic Definitions of Data Structures"
# by Adithya Murali, Cody Rivera, and P. Madhusudan.
# 
# Artifact by Cody Rivera, 2023. 
#
# Script to insert quantifier-free pointwise definitions for ordinarily
# quantified statements in an SMT2 script.
#
# Usage: python3 ./transplant.py INPUT-FILE CHANGE-FILE
#
# Syntax of CHANGE-FILE:
# (replace IDENTIFIER S-EXPRESSION+)    ; Replaces a definition/declaration with one
#                                       ; or more S-expressions.
# (delete IDENTIFIER)                   ; Removes a definition/declaration.
# (remove-get-info)                     ; Removes get-info annotations. This allows for easier checking
#                                       ; that everything goes through, in exchange for making it more
#                                       ; difficult to debug.
#
# Note: Allowing multiple S-expressions is a kluge to inject auxiliary functions
# where needed.

import sys
from sexpdata import parse, dumps, car, cdr, Symbol

def isatom(sexp):
    return not isinstance(sexp, list) or len(sexp) == 0

def isreplace(sexp):
    return isinstance(sexp, list)\
        and len(sexp) >= 2\
        and sexp[0] == Symbol("replace")\
        and isinstance(sexp[1], Symbol)

def isdelete(sexp):
    return isinstance(sexp, list)\
        and len(sexp) == 2\
        and sexp[0] == Symbol("delete")\
        and isinstance(sexp[1], Symbol)

def isremovegetinfo(sexp):
    return isinstance(sexp, list)\
        and len(sexp) == 1\
        and sexp[0] == Symbol("remove-get-info")

def isdefinition(sexp, symbol):
    return isinstance(sexp, list)\
        and len(sexp) >= 2\
        and sexp[0] in {Symbol("declare-fun"), 
                        Symbol("define-fun"), 
                        Symbol("declare-const"),
                        Symbol("define-const"),
                        Symbol("declare-sort")}\
        and sexp[1] == symbol

def isgetinfo(sexp):
    return isinstance(sexp, list)\
        and len(sexp) >= 1\
        and sexp[0] == Symbol("get-info")

def operate(input, changes):
    while not isatom(changes):
        change = car(changes)
        if isreplace(change):
            symbol = change[1]
            i = 0
            while i < len(input):
                if isdefinition(input[i], symbol):
                    input[i:i+1] = change[2:]
                    i += len(change[2:])
                else:
                    i += 1
        elif isdelete(change):
            symbol = change[1]
            i = 0
            while i < len(input):
                if isdefinition(input[i], symbol):
                    input[i:i+1] = []
                else:
                    i += 1
        elif isremovegetinfo(change):
            i = 0
            while i < len(input):
                if isgetinfo(input[i]):
                    input[i:i+1] = []
                else:
                    i += 1
        else:
            print(f"Bad command in {sys.argv[2]}:", file=sys.stderr)
            print(dumps(change), file=sys.stderr)
            sys.exit(1)
        changes = cdr(changes)
    return input

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(f"Usage: python {sys.argv[0]} INPUT-FILE CHANGE-FILE", file=sys.stderr)
        sys.exit(1)
    input_file = open(sys.argv[1], "r")
    change_file = open(sys.argv[2], "r")
    input = parse(input_file.read())
    changes = parse(change_file.read())
    output = operate(input, changes)
    for sexp in output:
        print(dumps(sexp))
