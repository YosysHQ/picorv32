/*
 *  PicoRV32 -- A Small RISC-V (RV32I) Processor Core
 *
 *  Copyright (C) 2015  Clifford Wolf <clifford@clifford.at>
 *  
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *  
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

`timescale 1 ns / 1 ps
// `define DEBUG


/***************************************************************
 * picorv32
 ***************************************************************/

module picorv32 #(
	parameter ENABLE_COUNTERS = 1,
	parameter ENABLE_REGS_16_31 = 1
) (
	input clk, resetn,
	output reg trap,

	output reg        mem_valid,
	output reg        mem_instr,
	input             mem_ready,

	output reg [31:0] mem_addr,
	output reg [31:0] mem_wdata,
	output reg [ 3:0] mem_wstrb,
	input      [31:0] mem_rdata,

	// look-ahead interface
	output            mem_la_read,
	output            mem_la_write,
	output     [31:0] mem_la_addr,
	output reg [31:0] mem_la_wdata,
	output reg [ 3:0] mem_la_wstrb
);
	localparam integer regfile_size = ENABLE_REGS_16_31 ? 32 : 16;
	localparam integer regindex_bits = ENABLE_REGS_16_31 ? 5 : 4;

	reg [63:0] count_cycle, count_instr;
	reg [31:0] reg_pc, reg_next_pc, reg_op1, reg_op2, reg_out, reg_alu_out;
	reg [31:0] cpuregs [0:regfile_size-1];
	reg [4:0] reg_sh;

	wire [31:0] next_pc;

	// Memory Interface

	reg [1:0] mem_state;
	reg [1:0] mem_wordsize;
	reg [31:0] mem_buffer;
	reg mem_do_prefetch;
	reg mem_do_rinst;
	reg mem_do_rdata;
	reg mem_do_wdata;

	wire mem_busy = |{mem_do_prefetch, mem_do_rinst, mem_do_rdata, mem_do_wdata};

	wire mem_done = mem_ready && ((mem_state[0] && (mem_do_rinst || mem_do_rdata)) || mem_state == 2);

	assign mem_la_write = resetn && !mem_state && mem_do_wdata;
	assign mem_la_read = resetn && !mem_state && (mem_do_rinst || mem_do_prefetch || mem_do_rdata);
	assign mem_la_addr = (mem_do_prefetch || mem_do_rinst) ? next_pc : {reg_op1[31:2], 2'b00};

	always @* begin
		(* full_case *)
		case (mem_wordsize)
			0: begin
				mem_la_wdata = reg_op2;
				mem_la_wstrb = 4'b1111;
				mem_buffer = mem_rdata;
			end
			1: begin
				mem_la_wdata = {2{reg_op2[15:0]}};
				mem_la_wstrb = reg_op1[1] ? 4'b1100 : 4'b0011;
				case (reg_op1[1])
					1'b0: mem_buffer = mem_rdata[15: 0];
					1'b1: mem_buffer = mem_rdata[31:16];
				endcase
			end
			2: begin
				mem_la_wdata = {4{reg_op2[7:0]}};
				mem_la_wstrb = 4'b0001 << reg_op1[1:0];
				case (reg_op1[1:0])
					2'b00: mem_buffer = mem_rdata[ 7: 0];
					2'b01: mem_buffer = mem_rdata[15: 8];
					2'b10: mem_buffer = mem_rdata[23:16];
					2'b11: mem_buffer = mem_rdata[31:24];
				endcase
			end
		endcase
	end

	always @(posedge clk) begin
		if (!resetn) begin
			mem_state <= 0;
			mem_valid <= 0;
		end else case (mem_state)
			0: begin
				mem_addr <= mem_la_addr;
				mem_wdata <= mem_la_wdata;
				mem_wstrb <= mem_la_wstrb;
				if (mem_do_prefetch || mem_do_rinst || mem_do_rdata) begin
					mem_valid <= 1;
					mem_instr <= mem_do_prefetch || mem_do_rinst;
					mem_wstrb <= 0;
					mem_state <= 1;
				end
				if (mem_do_wdata) begin
					mem_valid <= 1;
					mem_instr <= 0;
					mem_state <= 2;
				end
			end
			1: begin
				if (mem_ready) begin
					mem_valid <= 0;
					mem_state <= mem_do_rinst || mem_do_rdata ? 0 : 3;
				end
			end
			2: begin
				if (mem_ready) begin
					mem_valid <= 0;
					mem_state <= 0;
				end
			end
			3: begin
				if (mem_do_rinst) begin
					mem_state <= 0;
				end
			end
		endcase
	end


	// Instruction Decoder

	reg instr_lui, instr_auipc, instr_jal, instr_jalr;
	reg instr_beq, instr_bne, instr_blt, instr_bge, instr_bltu, instr_bgeu;
	reg instr_lb, instr_lh, instr_lw, instr_lbu, instr_lhu, instr_sb, instr_sh, instr_sw;
	reg instr_addi, instr_slti, instr_sltiu, instr_xori, instr_ori, instr_andi, instr_slli, instr_srli, instr_srai;
	reg instr_add, instr_sub, instr_sll, instr_slt, instr_sltu, instr_xor, instr_srl, instr_sra, instr_or, instr_and;
	reg instr_rdcycle, instr_rdcycleh, instr_rdinstr, instr_rdinstrh;
	wire instr_trap;

	reg [regindex_bits-1:0] decoded_rd, decoded_rs1, decoded_rs2;
	reg [31:0] decoded_imm;
	reg decoder_trigger;
	reg decoder_pseudo_trigger;

	wire [31:0] decoded_imm_uj;
	assign { decoded_imm_uj[31:20], decoded_imm_uj[10:1], decoded_imm_uj[11], decoded_imm_uj[19:12], decoded_imm_uj[0] } = $signed({mem_rdata[31:12], 1'b0});

	reg is_lui_auipc_jal;
	reg is_lb_lh_lw_lbu_lhu;
	reg is_slli_srli_srai;
	reg is_jalr_addi_slti_sltiu_xori_ori_andi;
	reg is_sb_sh_sw;
	reg is_sll_srl_sra;
	reg is_lui_auipc_jal_jalr_addi_add;
	reg is_slti_blt_slt;
	reg is_sltiu_bltu_sltu;
	reg is_beq_bne_blt_bge_bltu_bgeu;
	reg is_lbu_lhu_lw;
	reg is_compare;

	always @(posedge clk) begin
		is_lui_auipc_jal <= |{instr_lui, instr_auipc, instr_jal};
		is_lb_lh_lw_lbu_lhu <= |{instr_lb, instr_lh, instr_lw, instr_lbu, instr_lhu};
		is_slli_srli_srai <= |{instr_slli, instr_srli, instr_srai};
		is_jalr_addi_slti_sltiu_xori_ori_andi <= |{instr_jalr, instr_addi, instr_slti, instr_sltiu, instr_xori, instr_ori, instr_andi};
		is_sb_sh_sw <= |{instr_sb, instr_sh, instr_sw};
		is_sll_srl_sra <= |{instr_sll, instr_srl, instr_sra};
		is_lui_auipc_jal_jalr_addi_add <= |{instr_lui, instr_auipc, instr_jal, instr_jalr, instr_addi, instr_add};
		is_slti_blt_slt <= |{instr_slti, instr_blt, instr_slt};
		is_sltiu_bltu_sltu <= |{instr_sltiu, instr_bltu, instr_sltu};
		is_beq_bne_blt_bge_bltu_bgeu <= |{instr_beq, instr_bne, instr_blt, instr_bge, instr_bltu, instr_bgeu};
		is_lbu_lhu_lw <= |{instr_lbu, instr_lhu, instr_lw};
		is_compare <= |{instr_beq, instr_bne, instr_bge, instr_bgeu, is_slti_blt_slt, is_sltiu_bltu_sltu};
	end

	assign instr_trap = !{instr_lui, instr_auipc, instr_jal, instr_jalr,
			instr_beq, instr_bne, instr_blt, instr_bge, instr_bltu, instr_bgeu,
			instr_lb, instr_lh, instr_lw, instr_lbu, instr_lhu, instr_sb, instr_sh, instr_sw,
			instr_addi, instr_slti, instr_sltiu, instr_xori, instr_ori, instr_andi, instr_slli, instr_srli, instr_srai,
			instr_add, instr_sub, instr_sll, instr_slt, instr_sltu, instr_xor, instr_srl, instr_sra, instr_or, instr_and,
			instr_rdcycle, instr_rdcycleh, instr_rdinstr, instr_rdinstrh};
	
	reg [63:0] instruction;

	always @* begin
		instruction = 'bx;
		if (instr_lui)      instruction = "lui";
		if (instr_auipc)    instruction = "auipc";
		if (instr_jal)      instruction = "jal";
		if (instr_jalr)     instruction = "jalr";

		if (instr_beq)      instruction = "beq";
		if (instr_bne)      instruction = "bne";
		if (instr_blt)      instruction = "blt";
		if (instr_bge)      instruction = "bge";
		if (instr_bltu)     instruction = "bltu";
		if (instr_bgeu)     instruction = "bgeu";

		if (instr_lb)       instruction = "lb";
		if (instr_lh)       instruction = "lh";
		if (instr_lw)       instruction = "lw";
		if (instr_lbu)      instruction = "lbu";
		if (instr_lhu)      instruction = "lhu";
		if (instr_sb)       instruction = "sb";
		if (instr_sh)       instruction = "sh";
		if (instr_sw)       instruction = "sw";

		if (instr_addi)     instruction = "addi";
		if (instr_slti)     instruction = "slti";
		if (instr_sltiu)    instruction = "sltiu";
		if (instr_xori)     instruction = "xori";
		if (instr_ori)      instruction = "ori";
		if (instr_andi)     instruction = "andi";
		if (instr_slli)     instruction = "slli";
		if (instr_srli)     instruction = "srli";
		if (instr_srai)     instruction = "srai";

		if (instr_add)      instruction = "add";
		if (instr_sub)      instruction = "sub";
		if (instr_sll)      instruction = "sll";
		if (instr_slt)      instruction = "slt";
		if (instr_sltu)     instruction = "sltu";
		if (instr_xor)      instruction = "xor";
		if (instr_srl)      instruction = "srl";
		if (instr_sra)      instruction = "sra";
		if (instr_or)       instruction = "or";
		if (instr_and)      instruction = "and";

		if (instr_rdcycle)  instruction = "rdcycle";
		if (instr_rdcycleh) instruction = "rdcycleh";
		if (instr_rdinstr)  instruction = "rdinstr";
		if (instr_rdinstrh) instruction = "rdinstrh";
	end

	always @(posedge clk) begin
		if (mem_do_rinst && mem_done) begin
			instr_lui   <= mem_rdata[6:0] == 7'b0110111;
			instr_auipc <= mem_rdata[6:0] == 7'b0010111;

			instr_jal   <= mem_rdata[6:0] == 7'b1101111;
			instr_jalr  <= mem_rdata[6:0] == 7'b1100111;

			instr_beq   <= mem_rdata[6:0] == 7'b1100011 && mem_rdata[14:12] == 3'b000;
			instr_bne   <= mem_rdata[6:0] == 7'b1100011 && mem_rdata[14:12] == 3'b001;
			instr_blt   <= mem_rdata[6:0] == 7'b1100011 && mem_rdata[14:12] == 3'b100;
			instr_bge   <= mem_rdata[6:0] == 7'b1100011 && mem_rdata[14:12] == 3'b101;
			instr_bltu  <= mem_rdata[6:0] == 7'b1100011 && mem_rdata[14:12] == 3'b110;
			instr_bgeu  <= mem_rdata[6:0] == 7'b1100011 && mem_rdata[14:12] == 3'b111;

			instr_lb    <= mem_rdata[6:0] == 7'b0000011 && mem_rdata[14:12] == 3'b000;
			instr_lh    <= mem_rdata[6:0] == 7'b0000011 && mem_rdata[14:12] == 3'b001;
			instr_lw    <= mem_rdata[6:0] == 7'b0000011 && mem_rdata[14:12] == 3'b010;
			instr_lbu   <= mem_rdata[6:0] == 7'b0000011 && mem_rdata[14:12] == 3'b100;
			instr_lhu   <= mem_rdata[6:0] == 7'b0000011 && mem_rdata[14:12] == 3'b101;

			instr_sb    <= mem_rdata[6:0] == 7'b0100011 && mem_rdata[14:12] == 3'b000;
			instr_sh    <= mem_rdata[6:0] == 7'b0100011 && mem_rdata[14:12] == 3'b001;
			instr_sw    <= mem_rdata[6:0] == 7'b0100011 && mem_rdata[14:12] == 3'b010;

			instr_addi  <= mem_rdata[6:0] == 7'b0010011 && mem_rdata[14:12] == 3'b000;
			instr_slti  <= mem_rdata[6:0] == 7'b0010011 && mem_rdata[14:12] == 3'b010;
			instr_sltiu <= mem_rdata[6:0] == 7'b0010011 && mem_rdata[14:12] == 3'b011;
			instr_xori  <= mem_rdata[6:0] == 7'b0010011 && mem_rdata[14:12] == 3'b100;
			instr_ori   <= mem_rdata[6:0] == 7'b0010011 && mem_rdata[14:12] == 3'b110;
			instr_andi  <= mem_rdata[6:0] == 7'b0010011 && mem_rdata[14:12] == 3'b111;

			instr_slli  <= mem_rdata[6:0] == 7'b0010011 && mem_rdata[14:12] == 3'b001 && mem_rdata[31:25] == 7'b0000000;
			instr_srli  <= mem_rdata[6:0] == 7'b0010011 && mem_rdata[14:12] == 3'b101 && mem_rdata[31:25] == 7'b0000000;
			instr_srai  <= mem_rdata[6:0] == 7'b0010011 && mem_rdata[14:12] == 3'b101 && mem_rdata[31:25] == 7'b0100000;

			instr_add   <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b000 && mem_rdata[31:25] == 7'b0000000;
			instr_sub   <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b000 && mem_rdata[31:25] == 7'b0100000;
			instr_sll   <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b001 && mem_rdata[31:25] == 7'b0000000;
			instr_slt   <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b010 && mem_rdata[31:25] == 7'b0000000;
			instr_sltu  <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b011 && mem_rdata[31:25] == 7'b0000000;
			instr_xor   <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b100 && mem_rdata[31:25] == 7'b0000000;
			instr_srl   <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b101 && mem_rdata[31:25] == 7'b0000000;
			instr_sra   <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b101 && mem_rdata[31:25] == 7'b0100000;
			instr_or    <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b110 && mem_rdata[31:25] == 7'b0000000;
			instr_and   <= mem_rdata[6:0] == 7'b0110011 && mem_rdata[14:12] == 3'b111 && mem_rdata[31:25] == 7'b0000000;

			instr_rdcycle  <= ((mem_rdata[6:0] == 7'b1110011 && mem_rdata[31:12] == 'b11000000000000000010) ||
			                   (mem_rdata[6:0] == 7'b1110011 && mem_rdata[31:12] == 'b11000000000100000010)) && ENABLE_COUNTERS;
			instr_rdcycleh <= ((mem_rdata[6:0] == 7'b1110011 && mem_rdata[31:12] == 'b11001000000000000010) ||
			                   (mem_rdata[6:0] == 7'b1110011 && mem_rdata[31:12] == 'b11001000000100000010)) && ENABLE_COUNTERS;
			instr_rdinstr  <= (mem_rdata[6:0] == 7'b1110011 && mem_rdata[31:12] == 'b11000000001000000010) && ENABLE_COUNTERS;
			instr_rdinstrh <= (mem_rdata[6:0] == 7'b1110011 && mem_rdata[31:12] == 'b11001000001000000010) && ENABLE_COUNTERS;

			decoded_rd <= mem_rdata[11:7];
			decoded_rs1 <= mem_rdata[19:15];
			decoded_rs2 <= mem_rdata[24:20];
		end

		if (decoder_trigger && !decoder_pseudo_trigger) begin
			(* parallel_case *)
			case (1'b1)
				|{instr_lui, instr_auipc}:
					decoded_imm <= mem_rdata[31:12] << 12;
				instr_jal:
					decoded_imm <= decoded_imm_uj;
				instr_jalr:
					decoded_imm <= $signed(mem_rdata[31:20]);
				|{instr_beq, instr_bne, instr_blt, instr_bge, instr_bltu, instr_bgeu}:
					decoded_imm <= $signed({mem_rdata[31], mem_rdata[7], mem_rdata[30:25], mem_rdata[11:8], 1'b0});
				|{instr_lb, instr_lh, instr_lw, instr_lbu, instr_lhu}:
					decoded_imm <= $signed(mem_rdata[31:20]);
				|{instr_sb, instr_sh, instr_sw}:
					decoded_imm <= $signed({mem_rdata[31:25], mem_rdata[11:7]});
				|{instr_addi, instr_slti, instr_sltiu, instr_xori, instr_ori, instr_andi}:
					decoded_imm <= $signed(mem_rdata[31:20]);
				default:
					decoded_imm <= 1'bx;
			endcase
		end
	end


	// Main State Machine

	localparam cpu_state_trap   = 0;
	localparam cpu_state_fetch  = 1;
	localparam cpu_state_ld_rs1 = 2;
	localparam cpu_state_ld_rs2 = 3;
	localparam cpu_state_exec   = 4;
	localparam cpu_state_shift  = 5;
	localparam cpu_state_stmem  = 6;
	localparam cpu_state_ldmem  = 7;
	reg [2:0] cpu_state;

	reg set_mem_do_rinst;
	reg set_mem_do_rdata;
	reg set_mem_do_wdata;

	reg latched_store;
	reg latched_stalu;
	reg latched_branch;
	reg latched_is_lu;
	reg latched_is_lh;
	reg latched_is_lb;
	reg [regindex_bits-1:0] latched_rd;

	reg [31:0] current_pc;
	assign next_pc = latched_store && latched_branch ? reg_out : reg_next_pc;

	reg [31:0] alu_out;
	reg alu_out_0;

	always @* begin
		alu_out_0 = 'bx;
		(* parallel_case, full_case *)
		case (1'b1)
			instr_beq:
				alu_out_0 = reg_op1 == reg_op2;
			instr_bne:
				alu_out_0 = reg_op1 != reg_op2;
			instr_bge:
				alu_out_0 = $signed(reg_op1) >= $signed(reg_op2);
			instr_bgeu:
				alu_out_0 = reg_op1 >= reg_op2;
			is_slti_blt_slt:
				alu_out_0 = $signed(reg_op1) < $signed(reg_op2);
			is_sltiu_bltu_sltu:
				alu_out_0 = reg_op1 < reg_op2;
		endcase

		alu_out = 'bx;
		(* parallel_case, full_case *)
		case (1'b1)
			is_lui_auipc_jal_jalr_addi_add:
				alu_out = reg_op1 + reg_op2;
			instr_sub:
				alu_out = reg_op1 - reg_op2;
			is_compare:
				alu_out = alu_out_0;
			instr_xori || instr_xor:
				alu_out = reg_op1 ^ reg_op2;
			instr_ori || instr_or:
				alu_out = reg_op1 | reg_op2;
			instr_andi || instr_and:
				alu_out = reg_op1 & reg_op2;
		endcase
	end

	always @(posedge clk) begin
		trap <= 0;
		reg_sh <= 'bx;
		reg_out <= 'bx;
		set_mem_do_rinst = 0;
		set_mem_do_rdata = 0;
		set_mem_do_wdata = 0;

		reg_alu_out <= alu_out;

		if (ENABLE_COUNTERS)
			count_cycle <= resetn ? count_cycle + 1 : 0;

		decoder_trigger <= mem_do_rinst && mem_done;
		decoder_pseudo_trigger <= 0;

		if (!resetn) begin
			reg_pc <= 0;
			reg_next_pc <= 0;
			reg_op1 <= 'bx;
			reg_op2 <= 'bx;
			if (ENABLE_COUNTERS)
				count_instr <= 0;
			latched_store <= 0;
			latched_stalu <= 0;
			latched_branch <= 0;
			latched_is_lu <= 0;
			latched_is_lh <= 0;
			latched_is_lb <= 0;
			cpu_state <= cpu_state_fetch;
		end else
		(* parallel_case, full_case *)
		case (cpu_state)
			cpu_state_trap: begin
				trap <= 1;
			end
			cpu_state_fetch: begin
				mem_do_rinst <= !decoder_trigger;
				mem_wordsize <= 0;

				current_pc = reg_next_pc;

				if (latched_branch) begin
					current_pc = latched_store ? (latched_stalu ? reg_alu_out : reg_out) : reg_next_pc;
`ifdef DEBUG
					$display("ST_RD:  %2d 0x%08x, BRANCH 0x%08x", latched_rd, reg_pc + 4, current_pc);
`endif
					cpuregs[latched_rd] <= reg_pc + 4;
				end else
				if (latched_store) begin
`ifdef DEBUG
					$display("ST_RD:  %2d 0x%08x", latched_rd, reg_out);
`endif
					cpuregs[latched_rd] <= latched_stalu ? reg_alu_out : reg_out;
				end

				reg_pc <= current_pc;
				reg_next_pc <= current_pc;

				latched_store <= 0;
				latched_stalu <= 0;
				latched_branch <= 0;
				latched_is_lu <= 0;
				latched_is_lh <= 0;
				latched_is_lb <= 0;
				latched_rd <= decoded_rd;

				if (decoder_trigger) begin
`ifdef DEBUG
					$display("DECODE: 0x%08x %-s", current_pc, instruction);
`endif
					reg_next_pc <= current_pc + 4;

					if (instr_trap) begin
`ifdef DEBUG
						$display("SBREAK OR UNSUPPORTED INSN AT 0x%08x", current_pc);
`endif
						cpu_state <= cpu_state_trap;
					end else if (instr_jal) begin
						mem_do_rinst <= 1;
						if (latched_is_lu || latched_is_lh || latched_is_lb)
							reg_next_pc <= current_pc + decoded_imm;
						else
							reg_next_pc <= current_pc + decoded_imm_uj;
						latched_branch <= 1;
					end else if (|{instr_rdcycle, instr_rdcycleh, instr_rdinstr, instr_rdinstrh}) begin
						(* parallel_case, full_case *)
						case (1'b1)
							instr_rdcycle:
								reg_out <= count_cycle[31:0];
							instr_rdcycleh:
								reg_out <= count_cycle[63:32];
							instr_rdinstr:
								reg_out <= count_instr[31:0];
							instr_rdinstrh:
								reg_out <= count_instr[63:32];
						endcase
						latched_store <= 1;
					end else begin
						mem_do_rinst <= 0;
						mem_do_prefetch <= !instr_jalr;
						cpu_state <= cpu_state_ld_rs1;
					end
					if (ENABLE_COUNTERS)
						count_instr <= count_instr + 1;
				end
			end
			cpu_state_ld_rs1: begin
				if (is_lui_auipc_jal) begin
					reg_op1 <= instr_lui ? 0 : reg_pc;
					reg_op2 <= decoded_imm;
					mem_do_rinst <= mem_do_prefetch;
					cpu_state <= cpu_state_exec;
				end else begin
`ifdef DEBUG
					$display("LD_RS1: %2d 0x%08x", decoded_rs1, decoded_rs1 ? cpuregs[decoded_rs1] : 0);
`endif
					reg_op1 <= decoded_rs1 ? cpuregs[decoded_rs1] : 0;
					if (is_lb_lh_lw_lbu_lhu) begin
						cpu_state <= cpu_state_ldmem;
						mem_do_rinst <= 1;
					end else if (is_slli_srli_srai) begin
						reg_sh <= decoded_rs2;
						cpu_state <= cpu_state_shift;
					end else if (is_jalr_addi_slti_sltiu_xori_ori_andi) begin
						reg_op2 <= decoded_imm;
						mem_do_rinst <= mem_do_prefetch;
						cpu_state <= cpu_state_exec;
					end else
						cpu_state <= cpu_state_ld_rs2;
				end
			end
			cpu_state_ld_rs2: begin
`ifdef DEBUG
				$display("LD_RS2: %2d 0x%08x", decoded_rs2, decoded_rs2 ? cpuregs[decoded_rs2] : 0);
`endif
				reg_op2 <= decoded_rs2 ? cpuregs[decoded_rs2] : 0;
				if (is_sb_sh_sw) begin
					cpu_state <= cpu_state_stmem;
					mem_do_rinst <= 1;
				end else if (is_sll_srl_sra) begin
					reg_sh <= decoded_rs2 ? cpuregs[decoded_rs2] : 0;
					cpu_state <= cpu_state_shift;
				end else begin
					mem_do_rinst <= mem_do_prefetch;
					cpu_state <= cpu_state_exec;
				end
			end
			cpu_state_exec: begin
				latched_store <= alu_out_0;
				latched_branch <= alu_out_0;
				reg_out <= reg_pc + decoded_imm;
				if (is_beq_bne_blt_bge_bltu_bgeu) begin
					latched_rd <= 0;
					if (mem_done)
						cpu_state <= cpu_state_fetch;
					if (alu_out_0) begin
						decoder_trigger <= 0;
						set_mem_do_rinst = 1;
					end
				end else begin
					latched_branch <= instr_jalr;
					latched_store <= 1;
					latched_stalu <= 1;
					cpu_state <= cpu_state_fetch;
				end
			end
			cpu_state_shift: begin
				latched_store <= 1;
				if (reg_sh == 0) begin
					reg_out <= reg_op1;
					mem_do_rinst <= mem_do_prefetch;
					cpu_state <= cpu_state_fetch;
				end else if (reg_sh >= 4) begin
					(* parallel_case, full_case *)
					case (1'b1)
						instr_slli || instr_sll: reg_op1 <= reg_op1 << 4;
						instr_srli || instr_srl: reg_op1 <= reg_op1 >> 4;
						instr_srai || instr_sra: reg_op1 <= $signed(reg_op1) >>> 4;
					endcase
					reg_sh <= reg_sh - 4;
				end else begin
					(* parallel_case, full_case *)
					case (1'b1)
						instr_slli || instr_sll: reg_op1 <= reg_op1 << 1;
						instr_srli || instr_srl: reg_op1 <= reg_op1 >> 1;
						instr_srai || instr_sra: reg_op1 <= $signed(reg_op1) >>> 1;
					endcase
					reg_sh <= reg_sh - 1;
				end
			end
			cpu_state_stmem: begin
				if (!mem_do_prefetch || mem_done) begin
					if (!mem_do_wdata) begin
						(* parallel_case, full_case *)
						case (1'b1)
							instr_sb: mem_wordsize <= 2;
							instr_sh: mem_wordsize <= 1;
							instr_sw: mem_wordsize <= 0;
						endcase
						reg_op1 <= reg_op1 + decoded_imm;
						set_mem_do_wdata = 1;
					end
					if (!mem_do_prefetch && mem_done) begin
						cpu_state <= cpu_state_fetch;
						decoder_trigger <= 1;
					end
				end
			end
			cpu_state_ldmem: begin
				latched_store <= 1;
				if (!mem_do_prefetch || mem_done) begin
					if (!mem_do_rdata) begin
						(* parallel_case, full_case *)
						case (1'b1)
							instr_lb || instr_lbu: mem_wordsize <= 2;
							instr_lh || instr_lhu: mem_wordsize <= 1;
							instr_lw: mem_wordsize <= 0;
						endcase
						latched_is_lu <= is_lbu_lhu_lw;
						latched_is_lh <= instr_lh;
						latched_is_lb <= instr_lb;
						reg_op1 <= reg_op1 + decoded_imm;
						set_mem_do_rdata = 1;
					end
					if (!mem_do_prefetch && mem_done) begin
						(* parallel_case, full_case *)
						case (1'b1)
							latched_is_lu: reg_out <= mem_buffer;
							latched_is_lh: reg_out <= $signed(mem_buffer[15:0]);
							latched_is_lb: reg_out <= $signed(mem_buffer[7:0]);
						endcase
						decoder_trigger <= 1;
						decoder_pseudo_trigger <= 1;
						cpu_state <= cpu_state_fetch;
					end
				end
			end
		endcase

		if (resetn && (mem_do_rdata || mem_do_wdata)) begin
			if (mem_wordsize == 0 && reg_op1[1:0] != 0) begin
`ifdef DEBUG
				$display("MISALIGNED WORD: 0x%08x", reg_op1);
`endif
				cpu_state <= cpu_state_trap;
			end
			if (mem_wordsize == 1 && reg_op1[0] != 0) begin
`ifdef DEBUG
				$display("MISALIGNED HALFWORD: 0x%08x", reg_op1);
`endif
				cpu_state <= cpu_state_trap;
			end
		end
		if (resetn && mem_do_rinst && reg_pc[1:0] != 0) begin
`ifdef DEBUG
			$display("MISALIGNED INSTRUCTION: 0x%08x", reg_pc);
`endif
			cpu_state <= cpu_state_trap;
		end

		if (!resetn || mem_done) begin
			mem_do_prefetch <= 0;
			mem_do_rinst <= 0;
			mem_do_rdata <= 0;
			mem_do_wdata <= 0;
		end

		if (set_mem_do_rinst)
			mem_do_rinst <= 1;
		if (set_mem_do_rdata)
			mem_do_rdata <= 1;
		if (set_mem_do_wdata)
			mem_do_wdata <= 1;

		reg_pc[1:0] <= 0;
		reg_next_pc[1:0] <= 0;
		current_pc = 'bx;
	end
endmodule


/***************************************************************
 * picorv32_axi
 ***************************************************************/

module picorv32_axi #(
	parameter ENABLE_COUNTERS = 1,
	parameter ENABLE_REGS_16_31 = 1
) (
	input clk, resetn,
	output trap,

	// AXI4-lite master memory interface

	output        mem_axi_awvalid,
	input         mem_axi_awready,
	output [31:0] mem_axi_awaddr,
	output [ 2:0] mem_axi_awprot,

	output        mem_axi_wvalid,
	input         mem_axi_wready,
	output [31:0] mem_axi_wdata,
	output [ 3:0] mem_axi_wstrb,

	input         mem_axi_bvalid,
	output        mem_axi_bready,

	output        mem_axi_arvalid,
	input         mem_axi_arready,
	output [31:0] mem_axi_araddr,
	output [ 2:0] mem_axi_arprot,

	input         mem_axi_rvalid,
	output        mem_axi_rready,
	input  [31:0] mem_axi_rdata
);
	wire        mem_valid;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [ 3:0] mem_wstrb;
	wire        mem_instr;
	wire        mem_ready;
	wire [31:0] mem_rdata;

	picorv32_axi_adapter axi_adapter (
		.clk            (clk            ),
		.resetn         (resetn         ),
		.mem_axi_awvalid(mem_axi_awvalid),
		.mem_axi_awready(mem_axi_awready),
		.mem_axi_awaddr (mem_axi_awaddr ),
		.mem_axi_awprot (mem_axi_awprot ),
		.mem_axi_wvalid (mem_axi_wvalid ),
		.mem_axi_wready (mem_axi_wready ),
		.mem_axi_wdata  (mem_axi_wdata  ),
		.mem_axi_wstrb  (mem_axi_wstrb  ),
		.mem_axi_bvalid (mem_axi_bvalid ),
		.mem_axi_bready (mem_axi_bready ),
		.mem_axi_arvalid(mem_axi_arvalid),
		.mem_axi_arready(mem_axi_arready),
		.mem_axi_araddr (mem_axi_araddr ),
		.mem_axi_arprot (mem_axi_arprot ),
		.mem_axi_rvalid (mem_axi_rvalid ),
		.mem_axi_rready (mem_axi_rready ),
		.mem_axi_rdata  (mem_axi_rdata  ),
		.mem_valid      (mem_valid      ),
		.mem_instr      (mem_instr      ),
		.mem_ready      (mem_ready      ),
		.mem_addr       (mem_addr       ),
		.mem_wdata      (mem_wdata      ),
		.mem_wstrb      (mem_wstrb      ),
		.mem_rdata      (mem_rdata      )
	);

	picorv32 #(
		.ENABLE_COUNTERS  (ENABLE_COUNTERS  ),
		.ENABLE_REGS_16_31(ENABLE_REGS_16_31)
	) picorv32_core (
		.clk      (clk      ),
		.resetn   (resetn   ),
		.trap     (trap     ),
		.mem_valid(mem_valid),
		.mem_addr (mem_addr ),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.mem_instr(mem_instr),
		.mem_ready(mem_ready),
		.mem_rdata(mem_rdata)
	);
endmodule


/***************************************************************
 * picorv32_axi_adapter
 ***************************************************************/

module picorv32_axi_adapter (
	input clk, resetn,

	// AXI4-lite master memory interface

	output        mem_axi_awvalid,
	input         mem_axi_awready,
	output [31:0] mem_axi_awaddr,
	output [ 2:0] mem_axi_awprot,

	output        mem_axi_wvalid,
	input         mem_axi_wready,
	output [31:0] mem_axi_wdata,
	output [ 3:0] mem_axi_wstrb,

	input         mem_axi_bvalid,
	output        mem_axi_bready,

	output        mem_axi_arvalid,
	input         mem_axi_arready,
	output [31:0] mem_axi_araddr,
	output [ 2:0] mem_axi_arprot,

	input         mem_axi_rvalid,
	output        mem_axi_rready,
	input  [31:0] mem_axi_rdata,

	// Native PicoRV32 memory interface

	input         mem_valid,
	input         mem_instr,
	output        mem_ready,
	input  [31:0] mem_addr,
	input  [31:0] mem_wdata,
	input  [ 3:0] mem_wstrb,
	output [31:0] mem_rdata
);
	reg ack_awvalid;
	reg ack_arvalid;
	reg ack_wvalid;

	assign mem_axi_awvalid = mem_valid && |mem_wstrb && !ack_awvalid;
	assign mem_axi_awaddr = mem_addr;
	assign mem_axi_awprot = 0;

	assign mem_axi_arvalid = mem_valid && !mem_wstrb && !ack_arvalid;
	assign mem_axi_araddr = mem_addr;
	assign mem_axi_arprot = mem_instr ? 3'b100 : 3'b000;

	assign mem_axi_wvalid = mem_valid && |mem_wstrb && !ack_wvalid;
	assign mem_axi_wdata = mem_wdata;
	assign mem_axi_wstrb = mem_wstrb;

	assign mem_ready = mem_axi_bvalid || mem_axi_rvalid;
	assign mem_axi_bready = mem_valid && |mem_wstrb;
	assign mem_axi_rready = mem_valid && !mem_wstrb;
	assign mem_rdata = mem_axi_rdata;

	always @(posedge clk) begin
		if (!resetn) begin
			ack_awvalid <= 0;
		end else begin
			if (mem_axi_awready && mem_axi_awvalid)
				ack_awvalid <= 1;
			if (mem_axi_arready && mem_axi_arvalid)
				ack_arvalid <= 1;
			if (mem_axi_wready && mem_axi_wvalid)
				ack_wvalid <= 1;
			if (!mem_valid) begin
				ack_awvalid <= 0;
				ack_arvalid <= 0;
				ack_wvalid <= 0;
			end
		end
	end
endmodule

