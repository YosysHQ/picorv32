#include "Vtestbench.h"
#include "verilated.h"

int main(int argc, char **argv, char **env)
{
	Verilated::commandArgs(argc, argv);
	Vtestbench* top = new Vtestbench;

	top->clk = 0;
	while (!Verilated::gotFinish()) {
		top->clk = !top->clk;
		top->eval();
	}

	delete top;
	exit(0);
}

