#!/usr/bin/python3

import os, sys, getopt
from time import time
import subprocess

steps = 15
words = 0
solver = "yices"
allmem = False
fastmem = False
initzero = False
debug_print = False
debug_file = open("debug.smt2", "w")


# Yices Bindings
#####################################

if solver == "yices":
    yices = subprocess.Popen(['yices-smt2', '--incremental'], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

elif solver == "z3":
    yices = subprocess.Popen(['z3', '-smt2', '-in'], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

else:
    assert False

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

def yices_bv2hex(v):
    if v == "true": return "1"
    if v == "false": return "0"
    h = ""
    while len(v) > 2:
        d = 0
        if len(v) > 0 and v[-1] == "1": d += 1
        if len(v) > 1 and v[-2] == "1": d += 2
        if len(v) > 2 and v[-3] == "1": d += 4
        if len(v) > 3 and v[-4] == "1": d += 8
        h = hex(d)[2:] + h
        if len(v) < 4: break
        v = v[:-4]
    return h

def yices_bv2bin(v):
    if v == "true": return "1"
    if v == "false": return "0"
    return v[2:]

def yices_get(expr):
    yices_write("(get-value (%s))" % (expr))
    return yices_parse(yices_read())[0][1]

def yices_get_net(mod_name, net_name, state_name):
    return yices_get("(|%s_n %s| %s)" % (mod_name, net_name, state_name))

def yices_get_net_bool(mod_name, net_name, state_name):
    v = yices_get_net(mod_name, net_name, state_name)
    assert v in ["true", "false"]
    return 1 if v == "true" else 0

def yices_get_net_hex(mod_name, net_name, state_name):
    return yices_bv2hex(yices_get_net(mod_name, net_name, state_name))

def yices_get_net_bin(mod_name, net_name, state_name):
    return yices_bv2bin(yices_get_net(mod_name, net_name, state_name))


# Main Program
#####################################

start_time = time()

def timestamp():
    secs = int(time() - start_time)
    return "+ %6d [%3d:%02d:%02d] " % (secs, secs // (60*60), (secs // 60) % 60, secs % 60)

yices_write("(set-logic QF_AUFBV)")

regs_a = list()
regs_b = list()

with open("mem_equiv_a.smt2", "r") as f:
    for line in f:
        if line.startswith("; yosys-smt2-register "):
            line = line.split()
            regs_a.append((line[2], int(line[3])))
        else:
            yices_write(line)

with open("mem_equiv_b.smt2", "r") as f:
    for line in f:
        if line.startswith("; yosys-smt2-register "):
            line = line.split()
            regs_b.append((line[2], int(line[3])))
        else:
            yices_write(line)

for step in range(steps):
    yices_write("(declare-fun a%d () main_a_s)" % step)
    yices_write("(declare-fun b%d () main_b_s)" % step)

    if fastmem:
        yices_write("(assert (|main_a_n domem| a%d))" % step)
        yices_write("(assert (|main_b_n domem| b%d))" % step)

    if words > 0:
        if allmem:
            yices_write("(assert (bvult (|main_a_n mem_addr| a%d) #x%08x))" % (step, words))
            yices_write("(assert (bvult (|main_b_n mem_addr| b%d) #x%08x))" % (step, words))
        else:
            yices_write("(assert (or (not (|main_a_n mem_valid| a%d)) (bvult (|main_a_n mem_addr| a%d) #x%08x)))" % (step, step, words))
            yices_write("(assert (or (not (|main_b_n mem_valid| b%d)) (bvult (|main_b_n mem_addr| b%d) #x%08x)))" % (step, step, words))

    # reset in first cycle
    if step < 1:
        yices_write("(assert (not (|main_a_n resetn| a%d)))" % step)
        yices_write("(assert (not (|main_b_n resetn| b%d)))" % step)

    else:
        yices_write("(assert (|main_a_n resetn| a%d))" % step)
        yices_write("(assert (|main_b_n resetn| b%d))" % step)

    if step == 0:
        # start with synced memory and register file
        yices_write("(assert (= (|main_a_m cpu.cpuregs| a0) (|main_b_m cpu.cpuregs| b0)))")
        yices_write("(assert (= (|main_a_m memory| a0) (|main_b_m memory| b0)))")

    else:
        yices_write("(assert (main_a_t a%d a%d))" % (step-1, step))
        yices_write("(assert (main_b_t b%d b%d))" % (step-1, step))

        print("%s Checking sequence of length %d.." % (timestamp(), step))
        yices_write("(push 1)")

        # stop with a trap and no pending memory xfer
        yices_write("(assert (not (|main_a_n mem_valid| a%d)))" % step)
        yices_write("(assert (not (|main_b_n mem_valid| b%d)))" % step)
        yices_write("(assert (|main_a_n trap| a%d))" % step)
        yices_write("(assert (|main_b_n trap| b%d))" % step)

        # look for differences in memory or register file
        yices_write(("(assert (or (distinct (|main_a_m cpu.cpuregs| a%d) (|main_b_m cpu.cpuregs| b%d)) " +
                "(distinct (|main_a_m memory| a%d) (|main_b_m memory| b%d))))") % (step, step, step, step))

        yices_write("(check-sat)")

        if yices_read() == "sat":

            print("%s Creating model.." % timestamp())

            def make_cpu_regs(step):
                for i in range(1, 32):
                    yices_write("(define-fun a%d_r%d () (_ BitVec 32) (select (|main_a_m cpu.cpuregs| a%d) #b%s))" % (step, i, step, bin(32+i)[3:]))
                    yices_write("(define-fun b%d_r%d () (_ BitVec 32) (select (|main_b_m cpu.cpuregs| b%d) #b%s))" % (step, i, step, bin(32+i)[3:]))

            make_cpu_regs(0)
            make_cpu_regs(step)

            yices_write("(check-sat)")

            def print_status(mod, step):
                resetn = yices_get_net_bool("main_" + mod, "resetn", "%s%d" % (mod, step))
                memvld = yices_get_net_bool("main_" + mod, "mem_valid", "%s%d" % (mod, step))
                domem  = yices_get_net_bool("main_" + mod, "domem", "%s%d" % (mod, step))
                memrdy = yices_get_net_bool("main_" + mod, "mem_ready", "%s%d" % (mod, step))
                trap   = yices_get_net_bool("main_" + mod, "trap", "%s%d" % (mod, step))
                print("status %5s: resetn=%s, memvld=%s, domem=%s, memrdy=%s, trap=%s" % ("%s[%d]" % (mod, step), resetn, memvld, domem, memrdy, trap))

            def print_mem_xfer(mod, step):
                if allmem or yices_get("(and (|main_%s_n mem_valid| %s%d) (|main_%s_n mem_ready| %s%d))" % (mod, mod, step, mod, mod, step)) == 'true':
                    mem_addr = yices_get_net_hex("main_" + mod, "mem_addr", "%s%d" % (mod, step))
                    mem_wdata = yices_get_net_hex("main_" + mod, "mem_wdata", "%s%d" % (mod, step))
                    mem_wstrb = yices_get_net_bin("main_" + mod, "mem_wstrb", "%s%d" % (mod, step))
                    mem_rdata = yices_get_net_hex("main_" + mod, "mem_rdata", "%s%d" % (mod, step))
                    if allmem and yices_get("(and (|main_%s_n mem_valid| %s%d) (|main_%s_n mem_ready| %s%d))" % (mod, mod, step, mod, mod, step)) == 'true':
                        print("mem %5s: addr=%s, wdata=%s, wstrb=%s, rdata=%s <-" % ("%s[%d]" % (mod, step), mem_addr, mem_wdata, mem_wstrb, mem_rdata))
                    else:
                        print("mem %5s: addr=%s, wdata=%s, wstrb=%s, rdata=%s" % ("%s[%d]" % (mod, step), mem_addr, mem_wdata, mem_wstrb, mem_rdata))

            def print_cpu_regs(step):
                for i in range(1, 32):
                    ra = yices_bv2hex(yices_get("a%d_r%d" % (step, i)))
                    rb = yices_bv2hex(yices_get("b%d_r%d" % (step, i)))
                    print("%3s[%d]: A=%s B=%s%s" % ("x%d" % i, step, ra, rb, " !" if ra != rb else ""))

            assert yices_read() == "sat"

            if initzero:
                for rn, rs in regs_a:
                    force_to_zero = True
                    if yices_get_net_bin("main_a", rn, "a0").count("1") != 0:
                        print("Looking for a solution with |main_a_n %s| initialized to all zeros.." % rn)
                        yices_write("(push 1)")
                        if rs == 1:
                            yices_write("(assert (not (|main_a_n %s| a0)))" % rn)
                        else:
                            yices_write("(assert (= (|main_a_n %s| a0) #b%s))" % (rn, "0" * rs))
                        yices_write("(check-sat)")
                        if yices_read() != "sat":
                            force_to_zero = False
                        yices_write("(pop 1)")
                    if force_to_zero:
                        if rs == 1:
                            yices_write("(assert (not (|main_a_n %s| a0)))" % rn)
                        else:
                            yices_write("(assert (= (|main_a_n %s| a0) #b%s))" % (rn, "0" * rs))
                    yices_write("(check-sat)")
                    assert yices_read() == "sat"
                for rn, rs in regs_b:
                    force_to_zero = True
                    if yices_get_net_bin("main_b", rn, "b0").count("1") != 0:
                        print("Looking for a solution with |main_b_n %s| initialized to all zeros.." % rn)
                        yices_write("(push 1)")
                        if rs == 1:
                            yices_write("(assert (not (|main_b_n %s| b0)))" % rn)
                        else:
                            yices_write("(assert (= (|main_b_n %s| b0) #b%s))" % (rn, "0" * rs))
                        yices_write("(check-sat)")
                        if yices_read() != "sat":
                            force_to_zero = False
                        yices_write("(pop 1)")
                    if force_to_zero:
                        if rs == 1:
                            yices_write("(assert (not (|main_b_n %s| b0)))" % rn)
                        else:
                            yices_write("(assert (= (|main_b_n %s| b0) #b%s))" % (rn, "0" * rs))
                    yices_write("(check-sat)")
                    assert yices_read() == "sat"

            print()
            print_cpu_regs(0)

            print()
            print_cpu_regs(step)

            print()
            for i in range(step+1):
                print_status("a", i)

            print()
            for i in range(step+1):
                print_status("b", i)

            print()
            for i in range(1, step+1):
                print_mem_xfer("a", i)

            print()
            for i in range(1, step+1):
                print_mem_xfer("b", i)

            with open("mem_equiv_tb.v", "w") as f:
                print()
                print("writing verilog test bench...")

                memory_words = 1
                memory_datas = { "a": dict(), "b": dict() }
                for i in range(step, 0, -1):
                    for mod in ["a", "b"]:
                        if allmem or yices_get("(and (|main_%s_n mem_valid| %s%d) (|main_%s_n mem_ready| %s%d))" % (mod, mod, i, mod, mod, i)) == 'true':
                            mem_addr = yices_get_net_hex("main_" + mod, "mem_addr", "%s%d" % (mod, i))
                            mem_rdata = yices_get_net_hex("main_" + mod, "mem_rdata", "%s%d" % (mod, i))
                            memory_datas[mod][mem_addr] = mem_rdata
                            memory_words = max((int(mem_addr, 16) >> 2)+1, memory_words)
                memory_data = dict()
                for k, v in memory_datas["a"].items(): memory_data[k] = v
                for k, v in memory_datas["b"].items(): memory_data[k] = v

                print("`timescale 1 ns / 1 ps", file=f)
                print("", file=f)
                print("module testbench;", file=f)
                print("    reg clk = 1, resetn, domem_a, domem_b;", file=f)
                print("    always #5 clk = ~clk;", file=f)
                print("", file=f)
                print("    main #(", file=f)
                print("        .MEMORY_WORDS(%d)," % memory_words, file=f)
                print("        .ENABLE_REGS_DUALPORT(0),", file=f)
                print("        .TWO_STAGE_SHIFT(0),", file=f)
                print("        .TWO_CYCLE_COMPARE(0),", file=f)
                print("        .TWO_CYCLE_ALU(0)", file=f)
                print("    ) main_a (", file=f)
                print("        .clk(clk),", file=f)
                print("        .resetn(resetn),", file=f)
                print("        .domem(domem_a)", file=f)
                print("    );", file=f)
                print("", file=f)
                print("    main #(", file=f)
                print("        .MEMORY_WORDS(%d)," % memory_words, file=f)
                print("        .ENABLE_REGS_DUALPORT(1),", file=f)
                print("        .TWO_STAGE_SHIFT(1),", file=f)
                print("        .TWO_CYCLE_COMPARE(1),", file=f)
                print("        .TWO_CYCLE_ALU(1)", file=f)
                print("    ) main_b (", file=f)
                print("        .clk(clk),", file=f)
                print("        .resetn(resetn),", file=f)
                print("        .domem(domem_b)", file=f)
                print("    );", file=f)
                print("", file=f)
                print("    task check_reg;", file=f)
                print("        input [4:0] n;", file=f)
                print("        begin", file=f)
                print("            if (main_a.cpu.cpuregs[n] != main_b.cpu.cpuregs[n])", file=f)
                print("                $display(\"Divergent values for reg %1d: A=%08x B=%08x\", n, main_a.cpu.cpuregs[n], main_b.cpu.cpuregs[n]);", file=f)
                print("        end", file=f)
                print("    endtask", file=f)
                print("", file=f)
                print("    task check_mem;", file=f)
                print("        input [31:0] n;", file=f)
                print("        begin", file=f)
                print("            if (main_a.memory[n] != main_b.memory[n])", file=f)
                print("                $display(\"Divergent values for memory addr %08x: A=%08x B=%08x\", n, main_a.cpu.cpuregs[n], main_b.cpu.cpuregs[n]);", file=f)
                print("        end", file=f)
                print("    endtask", file=f)
                print("", file=f)
                print("    initial begin", file=f)
                print("        $dumpfile(\"mem_equiv_tb.vcd\");", file=f)
                print("        $dumpvars(0, testbench);", file=f)
                print("", file=f)

                for rn, rs in regs_a:
                    print("        main_a.%s = %d'b %s;" % (rn, rs, yices_get_net_bin("main_a", rn, "a0")), file=f)
                print("", file=f)

                for rn, rs in regs_b:
                    print("        main_b.%s = %d'b %s;" % (rn, rs, yices_get_net_bin("main_b", rn, "b0")), file=f)
                print("", file=f)

                for i in range(1, 32):
                    ra = yices_bv2hex(yices_get("a%d_r%d" % (0, i)))
                    rb = yices_bv2hex(yices_get("b%d_r%d" % (0, i)))
                    print("        main_a.cpu.cpuregs[%2d] = 'h %s;  main_b.cpu.cpuregs[%2d] = 'h %s;" % (i, ra, i, rb), file=f)
                print("", file=f)

                for addr, data in memory_data.items():
                    print("        main_a.memory['h %08x] = 'h %s;" % (int(addr, 16) >> 2, data), file=f)
                    print("        main_b.memory['h %08x] = 'h %s;" % (int(addr, 16) >> 2, data), file=f)
                print("", file=f)

                for i in range(step+1):
                    print("        resetn = %d;" % yices_get_net_bool("main_a", "resetn", "a%d" % i), file=f)
                    print("        domem_a = %d;" % yices_get_net_bool("main_a", "domem", "a%d" % i), file=f)
                    print("        domem_b = %d;" % yices_get_net_bool("main_b", "domem", "b%d" % i), file=f)
                    print("        @(posedge clk);", file=f)
                print("", file=f)

                for i in range(1, 32):
                    print("        check_reg(%d);" % i, file=f)
                for addr, data in memory_data.items():
                    print("        check_mem('h %s);" % addr, file=f)
                print("", file=f)

                print("        @(posedge clk);", file=f)
                print("        @(posedge clk);", file=f)
                print("        $finish;", file=f)
                print("    end", file=f)
                print("endmodule", file=f)

            if words > 0:
                print("running verilog test bench...")
                os.system("iverilog -o mem_equiv_tb -s testbench mem_equiv_tb.v mem_equiv.v ../../picorv32.v && ./mem_equiv_tb")

            break

        else: # unsat
            yices_write("(pop 1)")

print("%s Done." % timestamp())
yices_write("(exit)")
yices.wait()

