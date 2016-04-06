
run_signle_test: riscv-torture/build.ok riscv-isa-sim/build.ok
	bash run_single_test.sh

riscv-torture/build.ok: riscv-torture-rv32.diff
	rm -rf riscv-torture
	git clone https://github.com/ucb-bar/riscv-torture.git riscv-torture
	cd riscv-torture && git checkout 2bc0c42 && patch -p1 < ../riscv-torture-rv32.diff
	cd riscv-torture && ./sbt generator/run && touch build.ok

riscv-fesvr/build.ok:
	rm -rf riscv-fesvr
	git clone https://github.com/riscv/riscv-fesvr.git riscv-fesvr
	+cd riscv-fesvr && git checkout 1c02bd6 && ./configure && make && touch build.ok

riscv-isa-sim/build.ok: riscv-fesvr/build.ok
	rm -rf riscv-isa-sim
	git clone https://github.com/riscv/riscv-isa-sim.git riscv-isa-sim
	cd riscv-isa-sim && git checkout 10ae74e && patch -p1 < ../riscv-isa-sim-sbreak.diff
	cd riscv-isa-sim && LDFLAGS="-L../riscv-fesvr" ./configure --with-isa=RV32IMC
	+cd riscv-isa-sim && ln -s ../riscv-fesvr/fesvr . && make && touch build.ok

clean:
	rm -rf riscv-torture riscv-fesvr riscv-isa-sim
	rm -f test.S test.elf test.ref

.PHONY: run_signle_test clean

