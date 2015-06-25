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
	parameter ENABLE_REGS_16_31 = 1,
	parameter ENABLE_REGS_DUALPORT = 1,
	parameter LATCHED_MEM_RDATA = 0,
	parameter ENABLE_EXTERNAL_IRQ = 0,
	parameter ENABLE_ILLINSTR_IRQ = 0,
	parameter ENABLE_TIMER_IRQ = 0,
	parameter PROGADDR_RESET = 0,
	parameter PROGADDR_IRQ = 16
) (
	input clk, resetn, irq,
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
	localparam ENABLE_IRQ = ENABLE_EXTERNAL_IRQ || ENABLE_ILLINSTR_IRQ || ENABLE_TIMER_IRQ;

	localparam integer irqregs_offset = ENABLE_REGS_16_31 ? 32 : 16;
	localparam integer regfile_size = (ENABLE_REGS_16_31 ? 32 : 16) + 4*ENABLE_IRQ;
	localparam integer regindex_bits = (ENABLE_REGS_16_31 ? 5 : 4) + ENABLE_IRQ;

	reg [63:0] count_cycle, count_instr;
	reg [31:0] reg_pc, reg_next_pc, reg_op1, reg_op2, reg_out, reg_alu_out;
	reg [31:0] cpuregs [0:regfile_size-1];
	reg [4:0] reg_sh;

	wire [31:0] next_pc;

	reg irq_active;
	reg [4:0] irq_mask;
	reg [4:0] irq_pending;
	reg [31:0] timer;

	// Memory Interface

	reg [1:0] mem_state;
	reg [1:0] mem_wordsize;
	reg [31:0] mem_rdata_word;
	reg [31:0] mem_rdata_q;
	reg mem_do_prefetch;
	reg mem_do_rinst;
	reg mem_do_rdata;
	reg mem_do_wdata;

	wire mem_busy = |{mem_do_prefetch, mem_do_rinst, mem_do_rdata, mem_do_wdata};

	wire mem_done = mem_ready && ((mem_state[0] && (mem_do_rinst || mem_do_rdata)) || mem_state == 2);

	assign mem_la_write = resetn && !mem_state && mem_do_wdata;
	assign mem_la_read = resetn && !mem_state && (mem_do_rinst || mem_do_prefetch || mem_do_rdata);
	assign mem_la_addr = (mem_do_prefetch || mem_do_rinst) ? next_pc : {reg_op1[31:2], 2'b00};

	wire [31:0] mem_rdata_latched;
	assign mem_rdata_latched = ((mem_valid && mem_ready) || LATCHED_MEM_RDATA) ? mem_rdata : mem_rdata_q;

	always @* begin
		(* full_case *)
		case (mem_wordsize)
			0: begin
				mem_la_wdata = reg_op2;
				mem_la_wstrb = 4'b1111;
				mem_rdata_word = mem_rdata;
			end
			1: begin
				mem_la_wdata = {2{reg_op2[15:0]}};
				mem_la_wstrb = reg_op1[1] ? 4'b1100 : 4'b0011;
				case (reg_op1[1])
					1'b0: mem_rdata_word = mem_rdata[15: 0];
					1'b1: mem_rdata_word = mem_rdata[31:16];
				endcase
			end
			2: begin
				mem_la_wdata = {4{reg_op2[7:0]}};
				mem_la_wstrb = 4'b0001 << reg_op1[1:0];
				case (reg_op1[1:0])
					2'b00: mem_rdata_word = mem_rdata[ 7: 0];
					2'b01: mem_rdata_word = mem_rdata[15: 8];
					2'b10: mem_rdata_word = mem_rdata[23:16];
					2'b11: mem_rdata_word = mem_rdata[31:24];
				endcase
			end
		endcase
	end

	always @(posedge clk) begin
		if (mem_valid && mem_ready)
			mem_rdata_q <= mem_rdata_latched;
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
	reg instr_getq, instr_setq, instr_retirq, instr_maskirq, instr_waitirq, instr_timer;
	wire instr_trap;

	reg [regindex_bits-1:0] decoded_rd, decoded_rs1, decoded_rs2;
	reg [31:0] decoded_imm, decoded_imm_uj;
	reg decoder_trigger;
	reg decoder_pseudo_trigger;

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
	reg is_alu_reg_imm;
	reg is_alu_reg_reg;
	reg is_compare;

	assign instr_trap = !{instr_lui, instr_auipc, instr_jal, instr_jalr,
			instr_beq, instr_bne, instr_blt, instr_bge, instr_bltu, instr_bgeu,
			instr_lb, instr_lh, instr_lw, instr_lbu, instr_lhu, instr_sb, instr_sh, instr_sw,
			instr_addi, instr_slti, instr_sltiu, instr_xori, instr_ori, instr_andi, instr_slli, instr_srli, instr_srai,
			instr_add, instr_sub, instr_sll, instr_slt, instr_sltu, instr_xor, instr_srl, instr_sra, instr_or, instr_and,
			instr_rdcycle, instr_rdcycleh, instr_rdinstr, instr_rdinstrh,
			instr_getq, instr_setq, instr_retirq, instr_maskirq, instr_waitirq, instr_timer};
	
	wire is_rdcycle_rdcycleh_rdinstr_rdinstrh;
	assign is_rdcycle_rdcycleh_rdinstr_rdinstrh = |{instr_rdcycle, instr_rdcycleh, instr_rdinstr, instr_rdinstrh};

	reg [63:0] new_instruction;
	reg [63:0] instruction;

	always @* begin
		new_instruction = "";
		if (instr_lui)      new_instruction = "lui";
		if (instr_auipc)    new_instruction = "auipc";
		if (instr_jal)      new_instruction = "jal";
		if (instr_jalr)     new_instruction = "jalr";

		if (instr_beq)      new_instruction = "beq";
		if (instr_bne)      new_instruction = "bne";
		if (instr_blt)      new_instruction = "blt";
		if (instr_bge)      new_instruction = "bge";
		if (instr_bltu)     new_instruction = "bltu";
		if (instr_bgeu)     new_instruction = "bgeu";

		if (instr_lb)       new_instruction = "lb";
		if (instr_lh)       new_instruction = "lh";
		if (instr_lw)       new_instruction = "lw";
		if (instr_lbu)      new_instruction = "lbu";
		if (instr_lhu)      new_instruction = "lhu";
		if (instr_sb)       new_instruction = "sb";
		if (instr_sh)       new_instruction = "sh";
		if (instr_sw)       new_instruction = "sw";

		if (instr_addi)     new_instruction = "addi";
		if (instr_slti)     new_instruction = "slti";
		if (instr_sltiu)    new_instruction = "sltiu";
		if (instr_xori)     new_instruction = "xori";
		if (instr_ori)      new_instruction = "ori";
		if (instr_andi)     new_instruction = "andi";
		if (instr_slli)     new_instruction = "slli";
		if (instr_srli)     new_instruction = "srli";
		if (instr_srai)     new_instruction = "srai";

		if (instr_add)      new_instruction = "add";
		if (instr_sub)      new_instruction = "sub";
		if (instr_sll)      new_instruction = "sll";
		if (instr_slt)      new_instruction = "slt";
		if (instr_sltu)     new_instruction = "sltu";
		if (instr_xor)      new_instruction = "xor";
		if (instr_srl)      new_instruction = "srl";
		if (instr_sra)      new_instruction = "sra";
		if (instr_or)       new_instruction = "or";
		if (instr_and)      new_instruction = "and";

		if (instr_rdcycle)  new_instruction = "rdcycle";
		if (instr_rdcycleh) new_instruction = "rdcycleh";
		if (instr_rdinstr)  new_instruction = "rdinstr";
		if (instr_rdinstrh) new_instruction = "rdinstrh";

		if (instr_getq)     new_instruction = "getq";
		if (instr_setq)     new_instruction = "setq";
		if (instr_retirq)   new_instruction = "retirq";
		if (instr_maskirq)  new_instruction = "maskirq";
		if (instr_waitirq)  new_instruction = "waitirq";
		if (instr_timer)    new_instruction = "timer";

		if (new_instruction)
			instruction = new_instruction;
	end

	always @(posedge clk) begin
		is_lui_auipc_jal <= |{instr_lui, instr_auipc, instr_jal};
		is_lui_auipc_jal_jalr_addi_add <= |{instr_lui, instr_auipc, instr_jal, instr_jalr, instr_addi, instr_add};
		is_slti_blt_slt <= |{instr_slti, instr_blt, instr_slt};
		is_sltiu_bltu_sltu <= |{instr_sltiu, instr_bltu, instr_sltu};
		is_lbu_lhu_lw <= |{instr_lbu, instr_lhu, instr_lw};
		is_compare <= |{is_beq_bne_blt_bge_bltu_bgeu, instr_slti, instr_slt, instr_sltiu, instr_sltu};

		if (mem_do_rinst && mem_done) begin
			instr_lui   <= mem_rdata_latched[6:0] == 7'b0110111;
			instr_auipc <= mem_rdata_latched[6:0] == 7'b0010111;

			instr_jal    <= mem_rdata_latched[6:0] == 7'b1101111;
			instr_jalr   <= mem_rdata_latched[6:0] == 7'b1100111;
			instr_retirq <= mem_rdata_latched[6:0] == 7'b0001011 && mem_rdata_latched[31:25] == 7'b0000010 && ENABLE_IRQ;

			is_beq_bne_blt_bge_bltu_bgeu <= mem_rdata_latched[6:0] == 7'b1100011;
			is_lb_lh_lw_lbu_lhu          <= mem_rdata_latched[6:0] == 7'b0000011;
			is_sb_sh_sw                  <= mem_rdata_latched[6:0] == 7'b0100011;
			is_alu_reg_imm               <= mem_rdata_latched[6:0] == 7'b0010011;
			is_alu_reg_reg               <= mem_rdata_latched[6:0] == 7'b0110011;

			{ decoded_imm_uj[31:20], decoded_imm_uj[10:1], decoded_imm_uj[11], decoded_imm_uj[19:12], decoded_imm_uj[0] } <= $signed({mem_rdata_latched[31:12], 1'b0});

			decoded_rd <= mem_rdata_latched[11:7];
			decoded_rs1 <= mem_rdata_latched[19:15];
			decoded_rs2 <= mem_rdata_latched[24:20];

			if (mem_rdata_latched[6:0] == 7'b0001011 && mem_rdata_latched[31:25] == 7'b0000000 && ENABLE_IRQ)
				decoded_rs1[regindex_bits-1] <= 1; // instr_getq

			if (mem_rdata_latched[6:0] == 7'b0001011 && mem_rdata_latched[31:25] == 7'b0000010 && ENABLE_IRQ)
				decoded_rs1 <= irqregs_offset; // instr_retirq
		end

		if (decoder_trigger && !decoder_pseudo_trigger) begin
			instr_beq   <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b000;
			instr_bne   <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b001;
			instr_blt   <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b100;
			instr_bge   <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b101;
			instr_bltu  <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b110;
			instr_bgeu  <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b111;

			instr_lb    <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b000;
			instr_lh    <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b001;
			instr_lw    <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b010;
			instr_lbu   <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b100;
			instr_lhu   <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b101;

			instr_sb    <= is_sb_sh_sw && mem_rdata_q[14:12] == 3'b000;
			instr_sh    <= is_sb_sh_sw && mem_rdata_q[14:12] == 3'b001;
			instr_sw    <= is_sb_sh_sw && mem_rdata_q[14:12] == 3'b010;

			instr_addi  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b000;
			instr_slti  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b010;
			instr_sltiu <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b011;
			instr_xori  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b100;
			instr_ori   <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b110;
			instr_andi  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b111;

			instr_slli  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b001 && mem_rdata_q[31:25] == 7'b0000000;
			instr_srli  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0000000;
			instr_srai  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0100000;

			instr_add   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b000 && mem_rdata_q[31:25] == 7'b0000000;
			instr_sub   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b000 && mem_rdata_q[31:25] == 7'b0100000;
			instr_sll   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b001 && mem_rdata_q[31:25] == 7'b0000000;
			instr_slt   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b010 && mem_rdata_q[31:25] == 7'b0000000;
			instr_sltu  <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b011 && mem_rdata_q[31:25] == 7'b0000000;
			instr_xor   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b100 && mem_rdata_q[31:25] == 7'b0000000;
			instr_srl   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0000000;
			instr_sra   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0100000;
			instr_or    <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b110 && mem_rdata_q[31:25] == 7'b0000000;
			instr_and   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b111 && mem_rdata_q[31:25] == 7'b0000000;

			instr_rdcycle  <= ((mem_rdata_q[6:0] == 7'b1110011 && mem_rdata_q[31:12] == 'b11000000000000000010) ||
			                   (mem_rdata_q[6:0] == 7'b1110011 && mem_rdata_q[31:12] == 'b11000000000100000010)) && ENABLE_COUNTERS;
			instr_rdcycleh <= ((mem_rdata_q[6:0] == 7'b1110011 && mem_rdata_q[31:12] == 'b11001000000000000010) ||
			                   (mem_rdata_q[6:0] == 7'b1110011 && mem_rdata_q[31:12] == 'b11001000000100000010)) && ENABLE_COUNTERS;
			instr_rdinstr  <=  (mem_rdata_q[6:0] == 7'b1110011 && mem_rdata_q[31:12] == 'b11000000001000000010) && ENABLE_COUNTERS;
			instr_rdinstrh <=  (mem_rdata_q[6:0] == 7'b1110011 && mem_rdata_q[31:12] == 'b11001000001000000010) && ENABLE_COUNTERS;

			instr_getq    <= mem_rdata_q[6:0] == 7'b0001011 && mem_rdata_q[31:25] == 7'b0000000 && ENABLE_IRQ;
			instr_setq    <= mem_rdata_q[6:0] == 7'b0001011 && mem_rdata_q[31:25] == 7'b0000001 && ENABLE_IRQ;
			instr_maskirq <= mem_rdata_q[6:0] == 7'b0001011 && mem_rdata_q[31:25] == 7'b0000011 && ENABLE_IRQ;
			instr_waitirq <= mem_rdata_q[6:0] == 7'b0001011 && mem_rdata_q[31:25] == 7'b0000100 && ENABLE_IRQ;
			instr_timer   <= mem_rdata_q[6:0] == 7'b0001011 && mem_rdata_q[31:25] == 7'b0000101 && ENABLE_TIMER_IRQ;

			is_slli_srli_srai <= is_alu_reg_imm && |{
				mem_rdata_q[14:12] == 3'b001 && mem_rdata_q[31:25] == 7'b0000000,
				mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0000000,
				mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0100000
			};

			is_jalr_addi_slti_sltiu_xori_ori_andi <= instr_jalr || is_alu_reg_imm && |{
				mem_rdata_q[14:12] == 3'b000,
				mem_rdata_q[14:12] == 3'b010,
				mem_rdata_q[14:12] == 3'b011,
				mem_rdata_q[14:12] == 3'b100,
				mem_rdata_q[14:12] == 3'b110,
				mem_rdata_q[14:12] == 3'b111
			};

			is_sll_srl_sra <= is_alu_reg_reg && |{
				mem_rdata_q[14:12] == 3'b001 && mem_rdata_q[31:25] == 7'b0000000,
				mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0000000,
				mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0100000
			};

			(* parallel_case *)
			case (1'b1)
				instr_jal:
					decoded_imm <= decoded_imm_uj;
				|{instr_lui, instr_auipc}:
					decoded_imm <= mem_rdata_q[31:12] << 12;
				|{instr_jalr, is_lb_lh_lw_lbu_lhu, is_alu_reg_imm}:
					decoded_imm <= $signed(mem_rdata_q[31:20]);
				is_beq_bne_blt_bge_bltu_bgeu:
					decoded_imm <= $signed({mem_rdata_q[31], mem_rdata_q[7], mem_rdata_q[30:25], mem_rdata_q[11:8], 1'b0});
				is_sb_sh_sw:
					decoded_imm <= $signed({mem_rdata_q[31:25], mem_rdata_q[11:7]});
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
	reg [1:0] irq_state;

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

		if (ENABLE_TIMER_IRQ && timer) begin
			if (timer - 1 == 0)
				irq_pending[1] <= 1;
			timer <= timer - 1;
		end

		if (ENABLE_EXTERNAL_IRQ && irq) begin
			irq_pending[0] <= 1;
		end

		decoder_trigger <= mem_do_rinst && mem_done;
		decoder_pseudo_trigger <= 0;

		if (!resetn) begin
			reg_pc <= PROGADDR_RESET;
			reg_next_pc <= PROGADDR_RESET;
			if (ENABLE_COUNTERS)
				count_instr <= 0;
			latched_store <= 0;
			latched_stalu <= 0;
			latched_branch <= 0;
			latched_is_lu <= 0;
			latched_is_lh <= 0;
			latched_is_lb <= 0;
			irq_active <= 0;
			irq_mask <= 0;
			irq_pending <= 0;
			irq_state <= 0;
			timer <= 0;
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
					$display("ST_RD:  %2d 0x%08x", latched_rd, latched_stalu ? reg_alu_out : reg_out);
`endif
					cpuregs[latched_rd] <= latched_stalu ? reg_alu_out : reg_out;
				end else
				if (ENABLE_IRQ && irq_state[0]) begin
					cpuregs[latched_rd] <= current_pc;
					current_pc = PROGADDR_IRQ;
					irq_active <= 1;
					mem_do_rinst <= 1;
				end else
				if (ENABLE_IRQ && irq_state[1]) begin
					cpuregs[latched_rd] <=
						irq_pending[0] && irq_mask[0] ? 0 :
						irq_pending[1] && irq_mask[1] ? 1 :
						irq_pending[2] && irq_mask[2] ? 2 :
						irq_pending[3] && irq_mask[3] ? 3 : 4;
					irq_pending <=
						irq_pending[0] && irq_mask[0] ? irq_pending & 5'b11110 :
						irq_pending[1] && irq_mask[1] ? irq_pending & 5'b11101 :
						irq_pending[2] && irq_mask[2] ? irq_pending & 5'b11011 :
						irq_pending[3] && irq_mask[3] ? irq_pending & 5'b10111 : irq_pending & 5'b01111;
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

				if (ENABLE_IRQ && ((decoder_trigger && !irq_active && |(irq_pending & irq_mask)) || irq_state)) begin
					irq_state <=
						irq_state == 2'b00 ? 2'b01 :
						irq_state == 2'b01 ? 2'b10 : 2'b00;
					latched_rd <= irqregs_offset | irq_state[0];
				end else
				if (decoder_trigger) begin
`ifdef DEBUG
					$display("-- %-0t", $time);
`endif
					reg_next_pc <= current_pc + 4;
					if (ENABLE_COUNTERS)
						count_instr <= count_instr + 1;
					if (instr_jal) begin
`ifdef DEBUG
						$display("DECODE: 0x%08x jal", current_pc);
`endif
						mem_do_rinst <= 1;
						reg_next_pc <= current_pc + decoded_imm_uj;
						latched_branch <= 1;
					end else begin
						mem_do_rinst <= 0;
						mem_do_prefetch <= !instr_jalr && !instr_retirq;
						cpu_state <= cpu_state_ld_rs1;
					end
				end
			end
			cpu_state_ld_rs1: begin
				reg_op1 <= 'bx;
				reg_op2 <= 'bx;
`ifdef DEBUG
				$display("DECODE: 0x%08x %-0s", reg_pc, instruction);
`endif
				if (instr_trap) begin
`ifdef DEBUG
					$display("SBREAK OR UNSUPPORTED INSN AT 0x%08x", reg_pc);
`endif
					if (ENABLE_ILLINSTR_IRQ && irq_mask[2] && !irq_active) begin
						irq_pending[2] <= 1;
						cpu_state <= cpu_state_fetch;
					end else
						cpu_state <= cpu_state_trap;
				end else
				if (is_rdcycle_rdcycleh_rdinstr_rdinstrh) begin
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
					cpu_state <= cpu_state_fetch;
				end else
				if (is_lui_auipc_jal) begin
					reg_op1 <= instr_lui ? 0 : reg_pc;
					reg_op2 <= decoded_imm;
					mem_do_rinst <= mem_do_prefetch;
					cpu_state <= cpu_state_exec;
				end else
				if (ENABLE_IRQ && instr_getq) begin
					reg_out <= cpuregs[decoded_rs1];
					latched_store <= 1;
					cpu_state <= cpu_state_fetch;
				end else
				if (ENABLE_IRQ && instr_setq) begin
					reg_out <= cpuregs[decoded_rs1];
					latched_rd <= latched_rd | irqregs_offset;
					latched_store <= 1;
					cpu_state <= cpu_state_fetch;
				end else
				if (ENABLE_IRQ && instr_retirq) begin
					irq_active <= 0;
					latched_branch <= 1;
					latched_store <= 1;
					reg_out <= cpuregs[decoded_rs1];
					cpu_state <= cpu_state_fetch;
				end else
				if (ENABLE_IRQ && instr_maskirq) begin
					irq_mask = decoded_rs2;
					cpu_state <= cpu_state_fetch;
				end else
				if (ENABLE_TIMER_IRQ && instr_timer) begin
					timer <= cpuregs[decoded_rs1];
					cpu_state <= cpu_state_fetch;
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
					end else if (ENABLE_REGS_DUALPORT) begin
`ifdef DEBUG
						$display("LD_RS2: %2d 0x%08x", decoded_rs2, decoded_rs2 ? cpuregs[decoded_rs2] : 0);
`endif
						reg_sh <= decoded_rs2 ? cpuregs[decoded_rs2] : 0;
						reg_op2 <= decoded_rs2 ? cpuregs[decoded_rs2] : 0;
						if (is_sb_sh_sw) begin
							cpu_state <= cpu_state_stmem;
							mem_do_rinst <= 1;
						end else if (is_sll_srl_sra) begin
							cpu_state <= cpu_state_shift;
						end else begin
							mem_do_rinst <= mem_do_prefetch;
							cpu_state <= cpu_state_exec;
						end
					end else
						cpu_state <= cpu_state_ld_rs2;
				end
			end
			cpu_state_ld_rs2: begin
`ifdef DEBUG
				$display("LD_RS2: %2d 0x%08x", decoded_rs2, decoded_rs2 ? cpuregs[decoded_rs2] : 0);
`endif
				reg_sh <= decoded_rs2 ? cpuregs[decoded_rs2] : 0;
				reg_op2 <= decoded_rs2 ? cpuregs[decoded_rs2] : 0;
				if (is_sb_sh_sw) begin
					cpu_state <= cpu_state_stmem;
					mem_do_rinst <= 1;
				end else if (is_sll_srl_sra) begin
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
						decoder_pseudo_trigger <= 1;
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
							latched_is_lu: reg_out <= mem_rdata_word;
							latched_is_lh: reg_out <= $signed(mem_rdata_word[15:0]);
							latched_is_lb: reg_out <= $signed(mem_rdata_word[7:0]);
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
	parameter ENABLE_REGS_16_31 = 1,
	parameter ENABLE_REGS_DUALPORT = 1,
	parameter ENABLE_EXTERNAL_IRQ = 0,
	parameter ENABLE_ILLINSTR_IRQ = 0,
	parameter ENABLE_TIMER_IRQ = 0
) (
	input clk, resetn, irq,
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
		.ENABLE_COUNTERS     (ENABLE_COUNTERS     ),
		.ENABLE_REGS_16_31   (ENABLE_REGS_16_31   ),
		.ENABLE_REGS_DUALPORT(ENABLE_REGS_DUALPORT),
		.ENABLE_EXTERNAL_IRQ (ENABLE_EXTERNAL_IRQ ),
		.ENABLE_ILLINSTR_IRQ (ENABLE_ILLINSTR_IRQ ),
		.ENABLE_TIMER_IRQ    (ENABLE_TIMER_IRQ    )
	) picorv32_core (
		.clk      (clk      ),
		.resetn   (resetn   ),
		.irq      (irq      ),
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

