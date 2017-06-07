function opcode_jump;
	input [31:0] opcode;
	begin
		opcode_jump = 0;
		if (opcode[6:0] == 7'b1101111) opcode_jump = 1; // JAL
		if (opcode[14:12] == 3'b000 && opcode[6:0] == 7'b1100111) opcode_jump = 1; // JALR
	end
endfunction

function opcode_branch;
	input [31:0] opcode;
	begin
		opcode_branch = 0;
		if (opcode[14:12] == 3'b000 && opcode[6:0] == 7'b1100011) opcode_branch = 1; // BEQ
		if (opcode[14:12] == 3'b001 && opcode[6:0] == 7'b1100011) opcode_branch = 1; // BNE
		if (opcode[14:12] == 3'b100 && opcode[6:0] == 7'b1100011) opcode_branch = 1; // BLT
		if (opcode[14:12] == 3'b101 && opcode[6:0] == 7'b1100011) opcode_branch = 1; // BGE
		if (opcode[14:12] == 3'b110 && opcode[6:0] == 7'b1100011) opcode_branch = 1; // BLTU
		if (opcode[14:12] == 3'b111 && opcode[6:0] == 7'b1100011) opcode_branch = 1; // BGEU
	end
endfunction

function opcode_load;
	input [31:0] opcode;
	begin
		opcode_load = 0;
		if (opcode[14:12] == 3'b000 && opcode[6:0] == 7'b0000011) opcode_load = 1; // LB
		if (opcode[14:12] == 3'b001 && opcode[6:0] == 7'b0000011) opcode_load = 1; // LH
		if (opcode[14:12] == 3'b010 && opcode[6:0] == 7'b0000011) opcode_load = 1; // LW
		if (opcode[14:12] == 3'b100 && opcode[6:0] == 7'b0000011) opcode_load = 1; // LBU
		if (opcode[14:12] == 3'b101 && opcode[6:0] == 7'b0000011) opcode_load = 1; // LHU
	end
endfunction

function opcode_store;
	input [31:0] opcode;
	begin
		opcode_store = 0;
		if (opcode[14:12] == 3'b000 && opcode[6:0] == 7'b0100011) opcode_store = 1; // SB
		if (opcode[14:12] == 3'b001 && opcode[6:0] == 7'b0100011) opcode_store = 1; // SH
		if (opcode[14:12] == 3'b010 && opcode[6:0] == 7'b0100011) opcode_store = 1; // SW
	end
endfunction

function opcode_alui;
	input [31:0] opcode;
	begin
		opcode_alui = 0;
		if (opcode[14:12] == 3'b000 && opcode[6:0] == 7'b0010011) opcode_alui = 1; // ADDI
		if (opcode[14:12] == 3'b010 && opcode[6:0] == 7'b0010011) opcode_alui = 1; // SLTI
		if (opcode[14:12] == 3'b011 && opcode[6:0] == 7'b0010011) opcode_alui = 1; // SLTIU
		if (opcode[14:12] == 3'b100 && opcode[6:0] == 7'b0010011) opcode_alui = 1; // XORI
		if (opcode[14:12] == 3'b110 && opcode[6:0] == 7'b0010011) opcode_alui = 1; // ORI
		if (opcode[14:12] == 3'b111 && opcode[6:0] == 7'b0010011) opcode_alui = 1; // ANDI
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b001 && opcode[6:0] == 7'b0010011) opcode_alui = 1; // SLLI
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b101 && opcode[6:0] == 7'b0010011) opcode_alui = 1; // SRLI
		if (opcode[31:25] == 7'b0100000 && opcode[14:12] == 3'b101 && opcode[6:0] == 7'b0010011) opcode_alui = 1; // SRAI
	end
endfunction

function opcode_alu;
	input [31:0] opcode;
	begin
		opcode_alu = 0;
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b000 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // ADD
		if (opcode[31:25] == 7'b0100000 && opcode[14:12] == 3'b000 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // SUB
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b001 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // SLL
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b010 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // SLT
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b011 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // SLTU
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b100 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // XOR
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b101 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // SRL
		if (opcode[31:25] == 7'b0100000 && opcode[14:12] == 3'b101 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // SRA
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b110 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // OR
		if (opcode[31:25] == 7'b0000000 && opcode[14:12] == 3'b111 && opcode[6:0] == 7'b0110011) opcode_alu = 1; // AND
	end
endfunction

function opcode_sys;
	input [31:0] opcode;
	begin
		opcode_sys = 0;
		if (opcode[31:20] == 12'hC00 && opcode[19:12] == 3'b010 && opcode[6:0] == 7'b1110011) opcode_sys = 1; // RDCYCLE
		if (opcode[31:20] == 12'hC01 && opcode[19:12] == 3'b010 && opcode[6:0] == 7'b1110011) opcode_sys = 1; // RDTIME
		if (opcode[31:20] == 12'hC02 && opcode[19:12] == 3'b010 && opcode[6:0] == 7'b1110011) opcode_sys = 1; // RDINSTRET
		if (opcode[31:20] == 12'hC80 && opcode[19:12] == 3'b010 && opcode[6:0] == 7'b1110011) opcode_sys = 1; // RDCYCLEH
		if (opcode[31:20] == 12'hC81 && opcode[19:12] == 3'b010 && opcode[6:0] == 7'b1110011) opcode_sys = 1; // RDTIMEH
		if (opcode[31:20] == 12'hC82 && opcode[19:12] == 3'b010 && opcode[6:0] == 7'b1110011) opcode_sys = 1; // RDINSTRETH
	end

endfunction

function opcode_valid;
	input [31:0] opcode;
	begin
		opcode_valid = 0;
		if (opcode_jump  (opcode)) opcode_valid = 1;
		if (opcode_branch(opcode)) opcode_valid = 1;
		if (opcode_load  (opcode)) opcode_valid = 1;
		if (opcode_store (opcode)) opcode_valid = 1;
		if (opcode_alui  (opcode)) opcode_valid = 1;
		if (opcode_alu   (opcode)) opcode_valid = 1;
		if (opcode_sys   (opcode)) opcode_valid = 1;
	end
endfunction
