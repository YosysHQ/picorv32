#!/usr/bin/python3

import sys, getopt
import subprocess

steps=15
debug_print = False
debug_file = None # open("debug.smt2", "w")

yices = subprocess.Popen(['yices-smt2', '--incremental'], stdin=subprocess.PIPE,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

def yices_write(stmt):
    stmt = stmt.strip()
    if debug_print:
        print("> %s" % stmt)
    if debug_file:
        print(stmt, file=debug_file)
        debug_file.flush()
    yices.stdin.write(bytes(stmt + "\n", "ascii"))
    yices.stdin.flush()

def yices_read():
    stmt = []
    count_brackets = 0

    while True:
        line = yices.stdout.readline().decode("ascii").strip()
        count_brackets += line.count("(")
        count_brackets -= line.count(")")
        stmt.append(line)
        if debug_print:
            print("< %s" % line)
        if count_brackets == 0:
            break
        if not yices.poll():
            print("Yices terminated unexpectedly: %s" % "".join(stmt))
            sys.exit(1)

    stmt = "".join(stmt)
    if stmt.startswith("(error"):
        print("Yices Error: %s" % stmt, file=sys.stderr)
        sys.exit(1)

    return stmt

def yices_parse(stmt):
    def worker(stmt):
        if stmt[0] == '(':
            expr = []
            cursor = 1
            while stmt[cursor] != ')':
                el, le = worker(stmt[cursor:])
                expr.append(el)
                cursor += le
            return expr, cursor+1

        if stmt[0] == '|':
            expr = "|"
            cursor = 1
            while stmt[cursor] != '|':
                expr += stmt[cursor]
                cursor += 1
            expr += "|"
            return expr, cursor+1

        if stmt[0] in [" ", "\t", "\r", "\n"]:
            el, le = worker(stmt[1:])
            return el, le+1

        expr = ""
        cursor = 0
        while stmt[cursor] not in ["(", ")", "|", " ", "\t", "\r", "\n"]:
            expr += stmt[cursor]
            cursor += 1
        return expr, cursor
    return worker(stmt)[0]

def yices_get(mod_name, net_name, state_name):
    yices_write("(get-value ((|%s_n %s| %s)))" % (mod_name, net_name, state_name))
    return yices_parse(yices_read())[0][1]

def yices_get_bool(mod_name, net_name, state_name):
    v = yices_get(mod_name, net_name, state_name)
    assert v in ["true", "false"]
    return 1 if v == "true" else 0

yices_write("(set-logic QF_AUFBV)")

with open("mem_equiv_a.smt2", "r") as f:
    for line in f: yices_write(line)

with open("mem_equiv_b.smt2", "r") as f:
    for line in f: yices_write(line)

# set-up states and transaction, reset for two cycles
for i in range(steps):
    yices_write("(declare-fun a%d () main_a_s)" % i)
    yices_write("(declare-fun b%d () main_b_s)" % i)
    if i > 0:
        yices_write("(assert (main_a_t a%d a%d))" % (i-1, i))
        yices_write("(assert (main_b_t b%d b%d))" % (i-1, i))
    if i > 1:
        yices_write("(assert (|main_a_n resetn| a%d))" % i)
        yices_write("(assert (|main_b_n resetn| b%d))" % i)
    else:
        yices_write("(assert (not (|main_a_n resetn| a%d)))" % i)
        yices_write("(assert (not (|main_b_n resetn| b%d)))" % i)

# start with synced memory and register file
yices_write("(assert (= (|main_a_m cpu.cpuregs| a0) (|main_b_m cpu.cpuregs| b0)))")
yices_write("(assert (= (|main_a_m memory| a0) (|main_b_m memory| b0)))")

# stop with a trap and no pending memory xfer
yices_write("(assert (not (|main_a_n mem_valid| a%d)))" % (steps-1))
yices_write("(assert (not (|main_b_n mem_valid| b%d)))" % (steps-1))
yices_write("(assert (|main_a_n trap| a%d))" % (steps-1))
yices_write("(assert (|main_b_n trap| b%d))" % (steps-1))

# look for differences in memory or register file
yices_write(("(assert (or (distinct (|main_a_m cpu.cpuregs| a%d) (|main_b_m cpu.cpuregs| b%d)) " +
        "(distinct (|main_a_m memory| a%d) (|main_b_m memory| b%d))))") % (steps-1, steps-1, steps-1, steps-1))

print("checking...")
yices_write("(check-sat)")

def print_status(mod, step):
    resetn = yices_get_bool("main_" + mod, "resetn", "%s%d" % (mod, step))
    memvld = yices_get_bool("main_" + mod, "mem_valid", "%s%d" % (mod, step))
    domem  = yices_get_bool("main_" + mod, "domem", "%s%d" % (mod, step))
    memrdy = yices_get_bool("main_" + mod, "mem_ready", "%s%d" % (mod, step))
    trap   = yices_get_bool("main_" + mod, "trap", "%s%d" % (mod, step))
    print("%s[%d]: resetn=%s, memvld=%s, domem=%s, memrdy=%s, trap=%s" % (mod, step, resetn, memvld, domem, memrdy, trap))

def print_mem_xfer(mod, step):
    yices_write("(get-value ((and (|main_%s_n mem_valid| %s%d) (|main_%s_n mem_ready| %s%d))))" % (mod, mod, step, mod, mod, step))
    if yices_parse(yices_read())[0][1] == 'true':
        mem_addr = yices_get("main_" + mod, "mem_addr", "%s%d" % (mod, step))
        mem_wdata = yices_get("main_" + mod, "mem_wdata", "%s%d" % (mod, step))
        mem_wstrb = yices_get("main_" + mod, "mem_wstrb", "%s%d" % (mod, step))
        mem_rdata = yices_get("main_" + mod, "mem_rdata", "%s%d" % (mod, step))
        print("%s[%d]: addr=%s, wdata=%s, wstrb=%s, rdata=%s" % (mod, step, mem_addr, mem_wdata, mem_wstrb, mem_rdata))

if yices_read() == "sat":
    print("yices returned sat -> model check failed!")

    print()
    for i in range(steps):
        print_status("a", i)

    print()
    for i in range(steps):
        print_status("b", i)

    print()
    for i in range(1, steps):
        print_mem_xfer("a", i)

    print()
    for i in range(1, steps):
        print_mem_xfer("b", i)

else:
    print("yices returned unsat -> model check passed.")

