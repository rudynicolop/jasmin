open Arch_decl
open X86_decl
open Wsize

module type X86_input = sig

 val call_conv : (register, register_ext, xmm_register, rflag, condt) calling_convention
 val lowering_opt : X86_lowering.lowering_options

end

let atoI decl =
  let open Prog in
  let mk_var k t s =
    V.mk s (Reg(k,Direct)) (Conv.ty_of_cty (Type.atype_of_ltype t)) L._dummy [] in

  match Arch_extra.MkAToIdent.mk decl mk_var with
  | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:true) e in
      raise (Utils.HiError e)
  | Utils0.Ok atoI -> atoI

module X86_core = struct
  type reg = register
  type regx = register_ext
  type xreg = xmm_register
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op
  type lowering_options = X86_lowering.lowering_options

  let atoI = atoI x86_decl
  let asm_e = X86_extra.x86_extra atoI
  let aparams = X86_params.x86_params atoI

  let not_saved_stack = (X86_params.x86_liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_x86.print_prog

  let callstyle = Arch_full.StackDirect

  let known_implicits = ["OF","_of_"; "CF", "_cf_"; "SF", "_sf_"; "ZF", "_zf_"]

  let alloc_stack_need_extra _ = false

  let is_ct_asm_op (o : asm_op) =
    match o with
    | DIV _ | IDIV _ -> false
    | _ -> true

  let is_doit_asm_op (o : asm_op) =
    match o with
    | ADC _ -> true
    | ADCX _ -> true
    | ADD _ -> true
    | ADOX _ -> true
    | AESDEC -> true
    | AESDECLAST -> true
    | AESENC -> true
    | AESENCLAST -> true
    | AESIMC -> true
    | AESKEYGENASSIST -> true
    | AND _ -> true
    | ANDN _ -> true
    | BLENDV (VE8, _) -> true
    | BLENDV _ -> false (* Not DOIT *)
    | BSR _ -> false (* Not DOIT *)
    | BSWAP _ -> false (* Not DOIT *)
    | BT _ -> true
    | BTR _ -> true
    | BTS _ -> true
    | CLC -> false (* Not DOIT *)
    | CLFLUSH -> false (* Not DOIT *)
    | CMOVcc _ -> true
    | CMP _ -> true
    | CQO _ -> false (* Not DOIT *)
    | DEC _ -> true
    | DIV _ -> false (* Not DOIT *)
    | IDIV _ -> false (* Not DOIT *)
    | IMUL _ -> true
    | IMULr _ -> true
    | IMULri _ -> true
    | INC _ -> true
    | LEA _ -> true
    | LFENCE -> false (* Not DOIT *)
    | LZCNT _ -> false (* Not DOIT *)
    | MFENCE -> false (* Not DOIT *)
    | MOV _ -> true
    | MOVD _ -> true
    | MOVEMASK (VE8, _) -> true
    | MOVEMASK _ -> false (* Not DOIT *)
    | MOVSX _ -> true
    | MOVV _ -> true
    | MOVX _ -> true
    | PADD _ -> true
    | POR -> true
    | MOVZX _ -> true
    | MUL _ -> true
    | MULX_lo_hi _ -> true
    | NEG _ -> true
    | NOT _ -> true
    | OR _ -> true
    | PCLMULQDQ -> true
    | PDEP _ -> false (* Not DOIT *)
    | PEXT _ -> false (* Not DOIT *)
    | POPCNT _ -> false (* Not DOIT *)
    | PREFETCHT0 -> false (* Not DOIT *)
    | PREFETCHT1 -> false (* Not DOIT *)
    | PREFETCHT2 -> false (* Not DOIT *)
    | PREFETCHNTA -> false (* Not DOIT *)
    | RCL _ -> false (* Not DOIT *)
    | RCR _ -> false (* Not DOIT *)
    | RDTSC _ -> false (* Not DOIT *)
    | RDTSCP _ -> false (* Not DOIT *)
    | ROL _ -> false (* Not DOIT *)
    | RORX _ -> false (* Not DOIT *)
    | ROR _ -> false (* Not DOIT *)
    | SAL _ -> false (* Not DOIT *)
    | SAR _ -> true
    | SARX _ -> false (* Not DOIT *)
    | SBB _ -> true
    | SETcc -> true
    | SFENCE -> false (* Not DOIT *)
    | SHA256MSG1 -> true
    | SHA256MSG2 -> true
    | SHA256RNDS2 -> true
    | SHL _ -> true
    | SHLD _ -> false (* Not DOIT *)
    | SHLX _ -> true
    | SHR _ -> true
    | SHRD _ -> false (* Not DOIT *)
    | SHRX _ -> true
    | STC -> false (* Not DOIT *)
    | SUB _ -> true
    | TEST _ -> true
    | TZCNT _ -> false (* Not DOIT *)
    | VAESDEC _ -> true
    | VAESDECLAST _ -> true
    | VAESENC _ -> true
    | VAESENCLAST _ -> true
    | VAESIMC -> true
    | VAESKEYGENASSIST -> true
    | VBROADCASTI128 -> true
    | VEXTRACTI128 -> true
    | VINSERTI128 -> true
    | VMOV _ -> true
    | VMOVDQA _ -> true
    | VMOVDQU _ -> true
    | VMOVHPD -> false (* Not DOIT *)
    | VMOVLPD -> false (* Not DOIT *)
    | VMOVSHDUP _ -> true
    | VMOVSLDUP _ -> true
    | VPABS _ -> true
    | VPACKSS _ -> true
    | VPACKUS _ -> true
    | VPADD _ -> true
    | VPALIGNR _ -> true
    | VPAND _ -> true
    | VPANDN _ -> true
    | VPAVG _ -> true
    | VPBLEND _ -> true
    | VPBROADCAST _ -> true
    | VPCLMULQDQ _ -> true
    | VPCMPEQ _ -> true
    | VPCMPGT _ -> true
    | VPERM2I128 -> true
    | VPERMD -> true
    | VPERMQ -> true
    | VPEXTR _ -> true
    | VPINSR _ -> true
    | VPMADDUBSW _ -> true
    | VPMADDWD _ -> true
    | VPMAXS (ve, _) -> ve = VE8 || ve = VE16
    | VPMAXU _ -> true
    | VPMINS (ve, _) -> ve = VE8 || ve = VE16
    | VPMINU _ -> true
    | VPMOVSX _ -> true
    | VPMOVZX _ -> true
    | VPMUL _ -> true
    | VPMULH _ -> true
    | VPMULHRS _ -> true
    | VPMULHU _ -> true
    | VPMULL _ -> true
    | VPMULU _ -> true
    | VPOR _ -> true
    | VPSHUFB _ -> true
    | VPSHUFD _ -> true
    | VPSHUFHW _ -> true
    | VPSHUFLW _ -> true
    | VPSIGN _ -> true
    | VPSLL _ -> true
    | VPSLLDQ _ -> true
    | VPSLLV _ -> true
    | VPSRA _ -> true
    | VPSRL _ -> true
    | VPSRLDQ _ -> true
    | VPSRLV _ -> true
    | VPSUB _ -> true
    | VPTEST _ -> true
    | VPUNPCKH _ -> true
    | VPUNPCKL _ -> true
    | VPXOR _ -> true
    | VSHUFPS _ -> false (* Not DOIT *)
    | XCHG _ -> false (* Not DOIT *)
    | XOR _ -> true

  (* -------------------------------------------------------------------- *)
  (* Rocq printing for x86 asm ops *)

  let pp_asm_op_for_rocq fmt (o : asm_op) =
    let open X86_instr_decl in
    match o with
    | MOV ws -> ToRocq.pp_with_ws fmt "MOV" ws
    | MOVSX (ws1, ws2) -> ToRocq.pp_with_ws2 fmt "MOVSX" (ws1, ws2)
    | MOVZX (ws1, ws2) -> ToRocq.pp_with_ws2 fmt "MOVZX" (ws1, ws2)
    | CMOVcc ws -> ToRocq.pp_with_ws fmt "CMOVcc" ws
    | XCHG ws -> ToRocq.pp_with_ws fmt "XCHG" ws
    | ADD ws -> ToRocq.pp_with_ws fmt "ADD" ws
    | SUB ws -> ToRocq.pp_with_ws fmt "SUB" ws
    | MUL ws -> ToRocq.pp_with_ws fmt "MUL" ws
    | IMUL ws -> ToRocq.pp_with_ws fmt "IMUL" ws
    | IMULr ws -> ToRocq.pp_with_ws fmt "IMULr" ws
    | IMULri ws -> ToRocq.pp_with_ws fmt "IMULri" ws
    | DIV ws -> ToRocq.pp_with_ws fmt "DIV" ws
    | IDIV ws -> ToRocq.pp_with_ws fmt "IDIV" ws
    | CQO ws -> ToRocq.pp_with_ws fmt "CQO" ws
    | ADC ws -> ToRocq.pp_with_ws fmt "ADC" ws
    | SBB ws -> ToRocq.pp_with_ws fmt "SBB" ws
    | NEG ws -> ToRocq.pp_with_ws fmt "NEG" ws
    | INC ws -> ToRocq.pp_with_ws fmt "INC" ws
    | DEC ws -> ToRocq.pp_with_ws fmt "DEC" ws
    | LZCNT ws -> ToRocq.pp_with_ws fmt "LZCNT" ws
    | TZCNT ws -> ToRocq.pp_with_ws fmt "TZCNT" ws
    | BSR ws -> ToRocq.pp_with_ws fmt "BSR" ws
    | SETcc -> ToRocq.pp_bare fmt "SETcc"
    | BT ws -> ToRocq.pp_with_ws fmt "BT" ws
    | CLC -> ToRocq.pp_bare fmt "CLC"
    | STC -> ToRocq.pp_bare fmt "STC"
    | LEA ws -> ToRocq.pp_with_ws fmt "LEA" ws
    | TEST ws -> ToRocq.pp_with_ws fmt "TEST" ws
    | CMP ws -> ToRocq.pp_with_ws fmt "CMP" ws
    | AND ws -> ToRocq.pp_with_ws fmt "AND" ws
    | ANDN ws -> ToRocq.pp_with_ws fmt "ANDN" ws
    | OR ws -> ToRocq.pp_with_ws fmt "OR" ws
    | XOR ws -> ToRocq.pp_with_ws fmt "XOR" ws
    | NOT ws -> ToRocq.pp_with_ws fmt "NOT" ws
    | ROR ws -> ToRocq.pp_with_ws fmt "ROR" ws
    | ROL ws -> ToRocq.pp_with_ws fmt "ROL" ws
    | RCR ws -> ToRocq.pp_with_ws fmt "RCR" ws
    | RCL ws -> ToRocq.pp_with_ws fmt "RCL" ws
    | SHL ws -> ToRocq.pp_with_ws fmt "SHL" ws
    | SHR ws -> ToRocq.pp_with_ws fmt "SHR" ws
    | SAL ws -> ToRocq.pp_with_ws fmt "SAL" ws
    | SAR ws -> ToRocq.pp_with_ws fmt "SAR" ws
    | SHLD ws -> ToRocq.pp_with_ws fmt "SHLD" ws
    | SHRD ws -> ToRocq.pp_with_ws fmt "SHRD" ws
    | RORX ws -> ToRocq.pp_with_ws fmt "RORX" ws
    | SARX ws -> ToRocq.pp_with_ws fmt "SARX" ws
    | SHRX ws -> ToRocq.pp_with_ws fmt "SHRX" ws
    | SHLX ws -> ToRocq.pp_with_ws fmt "SHLX" ws
    | MULX_lo_hi ws -> ToRocq.pp_with_ws fmt "MULX_lo_hi" ws
    | ADCX ws -> ToRocq.pp_with_ws fmt "ADCX" ws
    | ADOX ws -> ToRocq.pp_with_ws fmt "ADOX" ws
    | BSWAP ws -> ToRocq.pp_with_ws fmt "BSWAP" ws
    | POPCNT ws -> ToRocq.pp_with_ws fmt "POPCNT" ws
    | BTR ws -> ToRocq.pp_with_ws fmt "BTR" ws
    | BTS ws -> ToRocq.pp_with_ws fmt "BTS" ws
    | PEXT ws -> ToRocq.pp_with_ws fmt "PEXT" ws
    | PDEP ws -> ToRocq.pp_with_ws fmt "PDEP" ws
    | MOVX ws -> ToRocq.pp_with_ws fmt "MOVX" ws
    | POR -> ToRocq.pp_bare fmt "POR"
    | PADD (ve, ws) -> ToRocq.pp_ve_ws fmt "PADD" (ve, ws)
    | MOVD ws -> ToRocq.pp_with_ws fmt "MOVD" ws
    | MOVV ws -> ToRocq.pp_with_ws fmt "MOVV" ws
    | VMOV ws -> ToRocq.pp_with_ws fmt "VMOV" ws
    | VMOVDQA ws -> ToRocq.pp_with_ws fmt "VMOVDQA" ws
    | VMOVDQU ws -> ToRocq.pp_with_ws fmt "VMOVDQU" ws
    | VPMOVSX (v1, w1, v2, w2) -> ToRocq.pp_ve_ws_ve_ws fmt "VPMOVSX" (v1, w1, v2, w2)
    | VPMOVZX (v1, w1, v2, w2) -> ToRocq.pp_ve_ws_ve_ws fmt "VPMOVZX" (v1, w1, v2, w2)
    | VPAND ws -> ToRocq.pp_with_ws fmt "VPAND" ws
    | VPANDN ws -> ToRocq.pp_with_ws fmt "VPANDN" ws
    | VPOR ws -> ToRocq.pp_with_ws fmt "VPOR" ws
    | VPXOR ws -> ToRocq.pp_with_ws fmt "VPXOR" ws
    | VPADD (v, w) -> ToRocq.pp_ve_ws fmt "VPADD" (v, w)
    | VPSUB (v, w) -> ToRocq.pp_ve_ws fmt "VPSUB" (v, w)
    | VPAVG (v, w) -> ToRocq.pp_ve_ws fmt "VPAVG" (v, w)
    | VPMULL (v, w) -> ToRocq.pp_ve_ws fmt "VPMULL" (v, w)
    | VPMULH ws -> ToRocq.pp_with_ws fmt "VPMULH" ws
    | VPMULHU ws -> ToRocq.pp_with_ws fmt "VPMULHU" ws
    | VPMULHRS ws -> ToRocq.pp_with_ws fmt "VPMULHRS" ws
    | VPMUL ws -> ToRocq.pp_with_ws fmt "VPMUL" ws
    | VPMULU ws -> ToRocq.pp_with_ws fmt "VPMULU" ws
    | VPEXTR ws -> ToRocq.pp_with_ws fmt "VPEXTR" ws
    | VPINSR ve -> ToRocq.pp_ve fmt "VPINSR" ve
    | VPSLL (v, w) -> ToRocq.pp_ve_ws fmt "VPSLL" (v, w)
    | VPSRL (v, w) -> ToRocq.pp_ve_ws fmt "VPSRL" (v, w)
    | VPSRA (v, w) -> ToRocq.pp_ve_ws fmt "VPSRA" (v, w)
    | VPSLLV (v, w) -> ToRocq.pp_ve_ws fmt "VPSLLV" (v, w)
    | VPSRLV (v, w) -> ToRocq.pp_ve_ws fmt "VPSRLV" (v, w)
    | VPSLLDQ ws -> ToRocq.pp_with_ws fmt "VPSLLDQ" ws
    | VPSRLDQ ws -> ToRocq.pp_with_ws fmt "VPSRLDQ" ws
    | VPSHUFB ws -> ToRocq.pp_with_ws fmt "VPSHUFB" ws
    | VPSHUFD ws -> ToRocq.pp_with_ws fmt "VPSHUFD" ws
    | VPSHUFHW ws -> ToRocq.pp_with_ws fmt "VPSHUFHW" ws
    | VPSHUFLW ws -> ToRocq.pp_with_ws fmt "VPSHUFLW" ws
    | VPBLEND (v, w) -> ToRocq.pp_ve_ws fmt "VPBLEND" (v, w)
    | BLENDV (v, w) -> ToRocq.pp_ve_ws fmt "BLENDV" (v, w)
    | VPACKUS (v, w) -> ToRocq.pp_ve_ws fmt "VPACKUS" (v, w)
    | VPACKSS (v, w) -> ToRocq.pp_ve_ws fmt "VPACKSS" (v, w)
    | VSHUFPS ws -> ToRocq.pp_with_ws fmt "VSHUFPS" ws
    | VPBROADCAST (v, w) -> ToRocq.pp_ve_ws fmt "VPBROADCAST" (v, w)
    | VMOVSHDUP ws -> ToRocq.pp_with_ws fmt "VMOVSHDUP" ws
    | VMOVSLDUP ws -> ToRocq.pp_with_ws fmt "VMOVSLDUP" ws
    | VPALIGNR ws -> ToRocq.pp_with_ws fmt "VPALIGNR" ws
    | VBROADCASTI128 -> ToRocq.pp_bare fmt "VBROADCASTI128"
    | VPUNPCKH (v, w) -> ToRocq.pp_ve_ws fmt "VPUNPCKH" (v, w)
    | VPUNPCKL (v, w) -> ToRocq.pp_ve_ws fmt "VPUNPCKL" (v, w)
    | VEXTRACTI128 -> ToRocq.pp_bare fmt "VEXTRACTI128"
    | VINSERTI128 -> ToRocq.pp_bare fmt "VINSERTI128"
    | VPERM2I128 -> ToRocq.pp_bare fmt "VPERM2I128"
    | VPERMD -> ToRocq.pp_bare fmt "VPERMD"
    | VPERMQ -> ToRocq.pp_bare fmt "VPERMQ"
    | MOVEMASK (v, w) -> ToRocq.pp_ve_ws fmt "MOVEMASK" (v, w)
    | VPCMPEQ (v, w) -> ToRocq.pp_ve_ws fmt "VPCMPEQ" (v, w)
    | VPCMPGT (v, w) -> ToRocq.pp_ve_ws fmt "VPCMPGT" (v, w)
    | VPSIGN (v, w) -> ToRocq.pp_ve_ws fmt "VPSIGN" (v, w)
    | VPMADDUBSW ws -> ToRocq.pp_with_ws fmt "VPMADDUBSW" ws
    | VPMADDWD ws -> ToRocq.pp_with_ws fmt "VPMADDWD" ws
    | VMOVLPD -> ToRocq.pp_bare fmt "VMOVLPD"
    | VMOVHPD -> ToRocq.pp_bare fmt "VMOVHPD"
    | VPMINU (v, w) -> ToRocq.pp_ve_ws fmt "VPMINU" (v, w)
    | VPMINS (v, w) -> ToRocq.pp_ve_ws fmt "VPMINS" (v, w)
    | VPMAXU (v, w) -> ToRocq.pp_ve_ws fmt "VPMAXU" (v, w)
    | VPMAXS (v, w) -> ToRocq.pp_ve_ws fmt "VPMAXS" (v, w)
    | VPABS (v, w) -> ToRocq.pp_ve_ws fmt "VPABS" (v, w)
    | VPTEST ws -> ToRocq.pp_with_ws fmt "VPTEST" ws
    | CLFLUSH -> ToRocq.pp_bare fmt "CLFLUSH"
    | PREFETCHT0 -> ToRocq.pp_bare fmt "PREFETCHT0"
    | PREFETCHT1 -> ToRocq.pp_bare fmt "PREFETCHT1"
    | PREFETCHT2 -> ToRocq.pp_bare fmt "PREFETCHT2"
    | PREFETCHNTA -> ToRocq.pp_bare fmt "PREFETCHNTA"
    | LFENCE -> ToRocq.pp_bare fmt "LFENCE"
    | MFENCE -> ToRocq.pp_bare fmt "MFENCE"
    | SFENCE -> ToRocq.pp_bare fmt "SFENCE"
    | RDTSC ws -> ToRocq.pp_with_ws fmt "RDTSC" ws
    | RDTSCP ws -> ToRocq.pp_with_ws fmt "RDTSCP" ws
    | AESDEC -> ToRocq.pp_bare fmt "AESDEC"
    | VAESDEC ws -> ToRocq.pp_with_ws fmt "VAESDEC" ws
    | AESDECLAST -> ToRocq.pp_bare fmt "AESDECLAST"
    | VAESDECLAST ws -> ToRocq.pp_with_ws fmt "VAESDECLAST" ws
    | AESENC -> ToRocq.pp_bare fmt "AESENC"
    | VAESENC ws -> ToRocq.pp_with_ws fmt "VAESENC" ws
    | AESENCLAST -> ToRocq.pp_bare fmt "AESENCLAST"
    | VAESENCLAST ws -> ToRocq.pp_with_ws fmt "VAESENCLAST" ws
    | AESIMC -> ToRocq.pp_bare fmt "AESIMC"
    | VAESIMC -> ToRocq.pp_bare fmt "VAESIMC"
    | AESKEYGENASSIST -> ToRocq.pp_bare fmt "AESKEYGENASSIST"
    | VAESKEYGENASSIST -> ToRocq.pp_bare fmt "VAESKEYGENASSIST"
    | PCLMULQDQ -> ToRocq.pp_bare fmt "PCLMULQDQ"
    | VPCLMULQDQ ws -> ToRocq.pp_with_ws fmt "VPCLMULQDQ" ws
    | SHA256RNDS2 -> ToRocq.pp_bare fmt "SHA256RNDS2"
    | SHA256MSG1 -> ToRocq.pp_bare fmt "SHA256MSG1"
    | SHA256MSG2 -> ToRocq.pp_bare fmt "SHA256MSG2"

  let pp_extra_op_for_rocq fmt (o : extra_op) =
    let open X86_extra in
    match o with
    | Oset0 ws -> ToRocq.pp_with_ws fmt "Oset0" ws
    | Oconcat128 -> ToRocq.pp_bare fmt "Oconcat128"
    | Ox86MOVZX32 -> ToRocq.pp_bare fmt "Ox86MOVZX32"
    | Ox86MULX ws -> ToRocq.pp_with_ws fmt "Ox86MULX" ws
    | Ox86MULX_hi ws -> ToRocq.pp_with_ws fmt "Ox86MULX_hi" ws
    | Ox86SLHinit -> ToRocq.pp_bare fmt "Ox86SLHinit"
    | Ox86SLHupdate -> ToRocq.pp_bare fmt "Ox86SLHupdate"
    | Ox86SLHmove -> ToRocq.pp_bare fmt "Ox86SLHmove"
    | Ox86SLHprotect (rk, ws) -> ToRocq.pp_rk_ws fmt "Ox86SLHprotect" (rk, ws)

  (* All of the extra ops compile into CT instructions (no DIV). *)
  let is_ct_asm_extra (_o : extra_op) = true

  (* All of the extra ops compile into DOIT instructions only, but this needs to be checked manually. *)
  let is_doit_asm_extra (o : extra_op) =
    match o with
    | Oset0 _           -> true
    | Oconcat128        -> true
    | Ox86MOVZX32       -> true
    | Ox86MULX _ws      -> true
    | Ox86MULX_hi _     -> true
    | Ox86SLHinit       -> true
    | Ox86SLHupdate     -> true
    | Ox86SLHmove       -> true
    | Ox86SLHprotect _  -> true

end


module X86 (Lowering_params : X86_input) :
  Arch_full.Core_arch
    with type reg = register
     and type regx = register_ext
     and type xreg = xmm_register
     and type rflag = rflag
     and type cond = condt
     and type asm_op = X86_instr_decl.x86_op
     and type extra_op = X86_extra.x86_extra_op = struct

  include X86_core

  include Lowering_params

  let internal_call_conv = X86_decl.x86_internal_call_conv
end
