#!/usr/bin/env python3

import sys
import subprocess

class smtio:
    def __init__(self, solver="yices", debug_print=False, debug_file=None):
        if solver == "yices":
            popen_vargs = ['yices-smt2', '--incremental']

        if solver == "z3":
            popen_vargs = ['z3', '-smt2', '-in']

        if solver == "cvc4":
            popen_vargs = ['cvc4', '--incremental', '--lang', 'smt2']

        if solver == "mathsat":
            popen_vargs = ['mathsat']

        self.debug_print = debug_print
        self.debug_file = debug_file
        self.p = subprocess.Popen(popen_vargs, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def setup(self, logic="ALL", info=None):
        self.write("(set-logic %s)" % logic)
        if info is not None:
            self.write("(set-info :source |%s|)" % info)
        self.write("(set-info :smt-lib-version 2.5)")
        self.write("(set-info :category \"industrial\")")

    def write(self, stmt):
        stmt = stmt.strip()
        if self.debug_print:
            print("> %s" % stmt)
        if self.debug_file:
            print(stmt, file=self.debug_file)
            self.debug_file.flush()
        self.p.stdin.write(bytes(stmt + "\n", "ascii"))
        self.p.stdin.flush()

    def read(self):
        stmt = []
        count_brackets = 0

        while True:
            line = self.p.stdout.readline().decode("ascii").strip()
            count_brackets += line.count("(")
            count_brackets -= line.count(")")
            stmt.append(line)
            if self.debug_print:
                print("< %s" % line)
            if count_brackets == 0:
                break
            if not self.p.poll():
                print("SMT Solver terminated unexpectedly: %s" % "".join(stmt))
                sys.exit(1)

        stmt = "".join(stmt)
        if stmt.startswith("(error"):
            print("SMT Solver Error: %s" % stmt, file=sys.stderr)
            sys.exit(1)

        return stmt

    def check_sat(self):
        if self.debug_print:
            print("> (check-sat)")
        if self.debug_file:
            print("; running check-sat..", file=self.debug_file)
            self.debug_file.flush()
        self.p.stdin.write(bytes("(check-sat)\n", "ascii"))
        self.p.stdin.flush()
        result = self.read()
        if self.debug_file:
            print("(set-info :status %s)" % result, file=self.debug_file)
            print("(check-sat)", file=self.debug_file)
            self.debug_file.flush()
        return result

    def parse(self, stmt):
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

    def bv2hex(self, v):
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

    def bv2bin(self, v):
        if v == "true": return "1"
        if v == "false": return "0"
        return v[2:]

    def get(self, expr):
        self.write("(get-value (%s))" % (expr))
        return self.parse(self.read())[0][1]

    def get_net(self, mod_name, net_name, state_name):
        return self.get("(|%s_n %s| %s)" % (mod_name, net_name, state_name))

    def get_net_bool(self, mod_name, net_name, state_name):
        v = self.get_net(mod_name, net_name, state_name)
        assert v in ["true", "false"]
        return 1 if v == "true" else 0

    def get_net_hex(self, mod_name, net_name, state_name):
        return self.bv2hex(self.get_net(mod_name, net_name, state_name))

    def get_net_bin(self, mod_name, net_name, state_name):
        return self.bv2bin(self.get_net(mod_name, net_name, state_name))

    def wait(self):
        self.p.wait()


class mkvcd:
    def __init__(self, f):
        self.f = f
        self.t = -1
        self.nets = dict()

    def add_net(self, name, width):
        assert self.t == -1
        key = "n%d" % len(self.nets)
        self.nets[name] = (key, width)

    def set_net(self, name, bits):
        assert name in self.nets
        assert self.t >= 0
        print("b%s %s" % (bits, self.nets[name][0]), file=self.f)

    def set_time(self, t):
        assert t >= self.t
        if t != self.t:
            if self.t == -1:
                for name in sorted(self.nets):
                    key, width = self.nets[name]
                    print("$var wire %d %s %s $end" % (width, key, name), file=self.f)
                print("$enddefinitions $end", file=self.f)
            self.t = t
            assert self.t >= 0
            print("#%d" % self.t, file=self.f)

