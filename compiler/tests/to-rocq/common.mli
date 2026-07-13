open Jasmin

module Make (C : Arch_full.Core_arch) : sig
  module Arch : Arch_full.Arch
    with type reg = C.reg
     and type regx = C.regx
     and type xreg = C.xreg
     and type rflag = C.rflag
     and type cond = C.cond
     and type asm_op = C.asm_op
     and type extra_op = C.extra_op

  val load_file :
    string ->
    ( unit,
      ( Arch.reg,
        Arch.regx,
        Arch.xreg,
        Arch.rflag,
        Arch.cond,
        Arch.asm_op,
        Arch.extra_op )
      Arch_extra.extended_op )
    Prog.prog
end
