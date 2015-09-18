#!/usr/bin/env python3

import os, sys, getopt
from smtio import smtio, smtopts

steps = 20
words = 0
allmem = False
so = smtopts()

def usage():
    print("""
python3 sync.py [options]

    -t <steps>
        default: 20
""" + so.helpmsg())
    sys.exit(1)

try:
    opts, args = getopt.getopt(sys.argv[1:], so.optstr + "t:")
except:
    usage()

for o, a in opts:
    if o == "-t":
        steps = int(a)
    elif so.handle(o, a):
        pass
    else:
        usage()

if len(args) > 0:
    usage()

smt = smtio(opts=so)

print("Solver: %s" % so.solver)
smt.setup("QF_AUFBV", "PicoRV32 \"sync.py\" BMC script, powered by Yosys")

regs_a = list()
regs_b = list()

with open("sync_a.smt2", "r") as f:
    for line in f:
        if line.startswith("; yosys-smt2-register "):
            line = line.split()
            regs_a.append((line[2], int(line[3])))
        else:
            smt.write(line)

with open("sync_b.smt2", "r") as f:
    for line in f:
        if line.startswith("; yosys-smt2-register "):
            line = line.split()
            regs_b.append((line[2], int(line[3])))
        else:
            smt.write(line)

for step in range(steps):
    smt.write("(declare-fun a%d () main_a_s)" % step)
    smt.write("(declare-fun b%d () main_b_s)" % step)

    smt.write("(assert (= (|main_a_n domem| a%d) (|main_b_n domem| b%d)))" % (step, step))
    smt.write("(assert (not (|main_a_n trap| a%d)))" % step)

    if step == 0:
        # start with synced memory and register file
        smt.write("(assert (= (|main_a_m cpu.cpuregs| a0) (|main_b_m cpu.cpuregs| b0)))")
        smt.write("(assert (= (|main_a_m memory| a0) (|main_b_m memory| b0)))")

        # reset in first cycle
        smt.write("(assert (not (|main_a_n resetn| a%d)))" % step)
        smt.write("(assert (not (|main_b_n resetn| b%d)))" % step)

    else:
        smt.write("(assert (main_a_t a%d a%d))" % (step-1, step))
        smt.write("(assert (main_b_t b%d b%d))" % (step-1, step))

        smt.write("(assert (|main_a_n resetn| a%d))" % step)
        smt.write("(assert (|main_b_n resetn| b%d))" % step)

        print("%s Checking sequence of length %d.." % (smt.timestamp(), step))
        smt.write("(push 1)")

        smt.write(("(assert (or (distinct (|main_a_m cpu.cpuregs| a%d) (|main_b_m cpu.cpuregs| b%d)) " +
                               "(distinct (|main_a_m memory|      a%d) (|main_b_m memory|      b%d))" +
                               "(distinct (|main_a_n trap|        a%d) (|main_b_n trap|        b%d))))") % (step, step, step, step, step, step))

        if smt.check_sat() == "sat":

            print("%s Creating model.." % smt.timestamp())

            def make_cpu_regs(step):
                for i in range(1, 32):
                    smt.write("(define-fun a%d_r%d () (_ BitVec 32) (select (|main_a_m cpu.cpuregs| a%d) #b%s))" % (step, i, step, bin(32+i)[3:]))
                    smt.write("(define-fun b%d_r%d () (_ BitVec 32) (select (|main_b_m cpu.cpuregs| b%d) #b%s))" % (step, i, step, bin(32+i)[3:]))

            make_cpu_regs(0)
            make_cpu_regs(step)

            assert smt.sheck_sat() == "sat"

            def print_status(mod, step):
                resetn = smt.get_net_bool("main_" + mod, "resetn", "%s%d" % (mod, step))
                memvld = smt.get_net_bool("main_" + mod, "mem_valid", "%s%d" % (mod, step))
                domem  = smt.get_net_bool("main_" + mod, "domem", "%s%d" % (mod, step))
                memrdy = smt.get_net_bool("main_" + mod, "mem_ready", "%s%d" % (mod, step))
                trap   = smt.get_net_bool("main_" + mod, "trap", "%s%d" % (mod, step))
                print("status %5s: resetn=%s, memvld=%s, domem=%s, memrdy=%s, trap=%s" % ("%s[%d]" % (mod, step), resetn, memvld, domem, memrdy, trap))

            def print_mem_xfer(mod, step):
                if allmem or smt.get("(and (|main_%s_n mem_valid| %s%d) (|main_%s_n mem_ready| %s%d))" % (mod, mod, step, mod, mod, step)) == 'true':
                    mem_addr = smt.get_net_hex("main_" + mod, "mem_addr", "%s%d" % (mod, step))
                    mem_wdata = smt.get_net_hex("main_" + mod, "mem_wdata", "%s%d" % (mod, step))
                    mem_wstrb = smt.get_net_bin("main_" + mod, "mem_wstrb", "%s%d" % (mod, step))
                    mem_rdata = smt.get_net_hex("main_" + mod, "mem_rdata", "%s%d" % (mod, step))
                    if allmem and smt.get("(and (|main_%s_n mem_valid| %s%d) (|main_%s_n mem_ready| %s%d))" % (mod, mod, step, mod, mod, step)) == 'true':
                        print("mem %5s: addr=%s, wdata=%s, wstrb=%s, rdata=%s <-" % ("%s[%d]" % (mod, step), mem_addr, mem_wdata, mem_wstrb, mem_rdata))
                    else:
                        print("mem %5s: addr=%s, wdata=%s, wstrb=%s, rdata=%s" % ("%s[%d]" % (mod, step), mem_addr, mem_wdata, mem_wstrb, mem_rdata))

            def print_cpu_regs(step):
                for i in range(1, 32):
                    ra = smt.bv2hex(smt.get("a%d_r%d" % (step, i)))
                    rb = smt.bv2hex(smt.get("b%d_r%d" % (step, i)))
                    print("%3s[%d]: A=%s B=%s%s" % ("x%d" % i, step, ra, rb, " !" if ra != rb else ""))

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

            with open("sync_tb.v", "w") as f:
                print()
                print("writing verilog test bench...")

                memory_words = 1
                memory_datas = { "a": dict(), "b": dict() }
                for i in range(step, 0, -1):
                    for mod in ["a", "b"]:
                        if allmem or smt.get("(and (|main_%s_n mem_valid| %s%d) (|main_%s_n mem_ready| %s%d))" % (mod, mod, i, mod, mod, i)) == 'true':
                            mem_addr = smt.get_net_hex("main_" + mod, "mem_addr", "%s%d" % (mod, i))
                            mem_rdata = smt.get_net_hex("main_" + mod, "mem_rdata", "%s%d" % (mod, i))
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
                print("        /* FIXME */", file=f)
                print("    ) main_a (", file=f)
                print("        .clk(clk),", file=f)
                print("        .resetn(resetn),", file=f)
                print("        .domem(domem_a)", file=f)
                print("    );", file=f)
                print("", file=f)
                print("    main #(", file=f)
                print("        .MEMORY_WORDS(%d)," % memory_words, file=f)
                print("        /* FIXME */", file=f)
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
                print("        $dumpfile(\"sync_tb.vcd\");", file=f)
                print("        $dumpvars(0, testbench);", file=f)
                print("", file=f)

                for rn, rs in regs_a:
                    print("        main_a.%s = %d'b %s;" % (rn, rs, smt.get_net_bin("main_a", rn, "a0")), file=f)
                print("", file=f)

                for rn, rs in regs_b:
                    print("        main_b.%s = %d'b %s;" % (rn, rs, smt.get_net_bin("main_b", rn, "b0")), file=f)
                print("", file=f)

                for i in range(1, 32):
                    ra = smt.bv2hex(smt.get("a%d_r%d" % (0, i)))
                    rb = smt.bv2hex(smt.get("b%d_r%d" % (0, i)))
                    print("        main_a.cpu.cpuregs[%2d] = 'h %s;  main_b.cpu.cpuregs[%2d] = 'h %s;" % (i, ra, i, rb), file=f)
                print("", file=f)

                for addr, data in memory_data.items():
                    print("        main_a.memory['h %08x] = 'h %s;" % (int(addr, 16) >> 2, data), file=f)
                    print("        main_b.memory['h %08x] = 'h %s;" % (int(addr, 16) >> 2, data), file=f)
                print("", file=f)

                for i in range(step+1):
                    print("        resetn = %d;" % smt.get_net_bool("main_a", "resetn", "a%d" % i), file=f)
                    print("        domem_a = %d;" % smt.get_net_bool("main_a", "domem", "a%d" % i), file=f)
                    print("        domem_b = %d;" % smt.get_net_bool("main_b", "domem", "b%d" % i), file=f)
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
                os.system("iverilog -o sync_tb -s testbench sync_tb.v main.v ../../picorv32.v && ./sync_tb")

            break

        else: # unsat
            smt.write("(pop 1)")

            smt.write("(assert (= (|main_a_m cpu.cpuregs| a%d) (|main_b_m cpu.cpuregs| b%d)))" % (step, step))
            smt.write("(assert (= (|main_a_m memory|      a%d) (|main_b_m memory|      b%d)))" % (step, step))
            smt.write("(assert (= (|main_a_n trap|        a%d) (|main_b_n trap|        b%d)))" % (step, step))

print("%s Done." % smt.timestamp())
smt.write("(exit)")
smt.wait()

