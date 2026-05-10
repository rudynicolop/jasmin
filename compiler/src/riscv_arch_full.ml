open Arch_decl
open Riscv_decl

module type Riscv_input = sig
  val call_conv : (register, Arch_utils.empty, Arch_utils.empty, Arch_utils.empty, condt) calling_convention

end

module Riscv_core = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type rflag =  Arch_utils.empty
  type cond = condt
  type asm_op = Riscv_instr_decl.riscv_op
  type extra_op = Riscv_extra.riscv_extra_op
  type lowering_options = Riscv_lowering.lowering_options

  let atoI = X86_arch_full.atoI riscv_decl

  let asm_e =  Riscv_extra.riscv_extra atoI
  let aparams = Riscv_params.riscv_params atoI
  let known_implicits = []

  let alloc_stack_need_extra sz =
    not (Riscv_params_core.is_arith_small (Conv.cz_of_z sz))

  (* FIXME RISCV: check if everything is ct *)
  let is_ct_asm_op (o : asm_op) =
    match o with
    | _ -> true

  let is_ct_asm_extra (_o : extra_op) = true

  let is_doit_asm_op (_o : asm_op) = true

  (* All of the extra ops compile into DIT instructions only, but this needs to be checked manually. *)
  let is_doit_asm_extra (_o : extra_op) = true

  let pp_asm_op_for_rocq fmt (o : asm_op) =
    let open Riscv_instr_decl in
    match o with
    | ADD -> ToRocq.pp_bare fmt "ADD"
    | ADDI -> ToRocq.pp_bare fmt "ADDI"
    | SUB -> ToRocq.pp_bare fmt "SUB"
    | SLT -> ToRocq.pp_bare fmt "SLT"
    | SLTI -> ToRocq.pp_bare fmt "SLTI"
    | SLTU -> ToRocq.pp_bare fmt "SLTU"
    | SLTIU -> ToRocq.pp_bare fmt "SLTIU"
    | AND -> ToRocq.pp_bare fmt "AND"
    | ANDI -> ToRocq.pp_bare fmt "ANDI"
    | OR -> ToRocq.pp_bare fmt "OR"
    | ORI -> ToRocq.pp_bare fmt "ORI"
    | XOR -> ToRocq.pp_bare fmt "XOR"
    | XORI -> ToRocq.pp_bare fmt "XORI"
    | SLL -> ToRocq.pp_bare fmt "SLL"
    | SLLI -> ToRocq.pp_bare fmt "SLLI"
    | SRL -> ToRocq.pp_bare fmt "SRL"
    | SRLI -> ToRocq.pp_bare fmt "SRLI"
    | SRA -> ToRocq.pp_bare fmt "SRA"
    | SRAI -> ToRocq.pp_bare fmt "SRAI"
    | MV -> ToRocq.pp_bare fmt "MV"
    | LA -> ToRocq.pp_bare fmt "LA"
    | LI -> ToRocq.pp_bare fmt "LI"
    | NOT -> ToRocq.pp_bare fmt "NOT"
    | NEG -> ToRocq.pp_bare fmt "NEG"
    | LOAD (s, ws) -> ToRocq.pp_s_ws fmt "LOAD" (s, ws)
    | STORE ws -> ToRocq.pp_with_ws fmt "STORE" ws
    | MUL -> ToRocq.pp_bare fmt "MUL"
    | MULH -> ToRocq.pp_bare fmt "MULH"
    | MULHU -> ToRocq.pp_bare fmt "MULHU"
    | MULHSU -> ToRocq.pp_bare fmt "MULHSU"
    | DIV -> ToRocq.pp_bare fmt "DIV"
    | DIVU -> ToRocq.pp_bare fmt "DIVU"
    | REM -> ToRocq.pp_bare fmt "REM"
    | REMU -> ToRocq.pp_bare fmt "REMU"

  let pp_extra_op_for_rocq fmt (o : extra_op) =
    let open Riscv_extra in
    match o with
    | SWAP ws -> ToRocq.pp_with_ws fmt "SWAP" ws
    | Oriscv_add_large_imm -> ToRocq.pp_bare fmt "Oriscv_add_large_imm"

end

module Riscv (Lowering_params : Riscv_input) : Arch_full.Core_arch
  with type reg = register
   and type regx = Arch_utils.empty
   and type xreg = Arch_utils.empty
   and type rflag = Arch_utils.empty
   and type cond = condt
   and type asm_op = Riscv_instr_decl.riscv_op
   and type extra_op = Riscv_extra.riscv_extra_op = struct
  include Riscv_core
  include Lowering_params

  let lowering_opt = ()

  let not_saved_stack = (Riscv_params.riscv_liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_riscv.print_prog

  let callstyle = Arch_full.ByReg { call = Some RA; return = true }

  let internal_call_conv = Riscv_decl.riscv_internal_call_conv
end
