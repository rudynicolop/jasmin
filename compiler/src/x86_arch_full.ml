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
    | MOV ws -> ToRocq.pp_with_ws "MOV" fmt ws
    | MOVSX (ws1, ws2) -> ToRocq.pp_with_ws2 "MOVSX" fmt (ws1, ws2)
    | MOVZX (ws1, ws2) -> ToRocq.pp_with_ws2 "MOVZX" fmt (ws1, ws2)
    | CMOVcc ws -> ToRocq.pp_with_ws "CMOVcc" fmt ws
    | XCHG ws -> ToRocq.pp_with_ws "XCHG" fmt ws
    | ADD ws -> ToRocq.pp_with_ws "ADD" fmt ws
    | SUB ws -> ToRocq.pp_with_ws "SUB" fmt ws
    | MUL ws -> ToRocq.pp_with_ws "MUL" fmt ws
    | IMUL ws -> ToRocq.pp_with_ws "IMUL" fmt ws
    | IMULr ws -> ToRocq.pp_with_ws "IMULr" fmt ws
    | IMULri ws -> ToRocq.pp_with_ws "IMULri" fmt ws
    | DIV ws -> ToRocq.pp_with_ws "DIV" fmt ws
    | IDIV ws -> ToRocq.pp_with_ws "IDIV" fmt ws
    | CQO ws -> ToRocq.pp_with_ws "CQO" fmt ws
    | ADC ws -> ToRocq.pp_with_ws "ADC" fmt ws
    | SBB ws -> ToRocq.pp_with_ws "SBB" fmt ws
    | NEG ws -> ToRocq.pp_with_ws "NEG" fmt ws
    | INC ws -> ToRocq.pp_with_ws "INC" fmt ws
    | DEC ws -> ToRocq.pp_with_ws "DEC" fmt ws
    | LZCNT ws -> ToRocq.pp_with_ws "LZCNT" fmt ws
    | TZCNT ws -> ToRocq.pp_with_ws "TZCNT" fmt ws
    | BSR ws -> ToRocq.pp_with_ws "BSR" fmt ws
    | SETcc -> ToRocq.pp_bare "SETcc" fmt
    | BT ws -> ToRocq.pp_with_ws "BT" fmt ws
    | CLC -> ToRocq.pp_bare "CLC" fmt
    | STC -> ToRocq.pp_bare "STC" fmt
    | LEA ws -> ToRocq.pp_with_ws "LEA" fmt ws
    | TEST ws -> ToRocq.pp_with_ws "TEST" fmt ws
    | CMP ws -> ToRocq.pp_with_ws "CMP" fmt ws
    | AND ws -> ToRocq.pp_with_ws "AND" fmt ws
    | ANDN ws -> ToRocq.pp_with_ws "ANDN" fmt ws
    | OR ws -> ToRocq.pp_with_ws "OR" fmt ws
    | XOR ws -> ToRocq.pp_with_ws "XOR" fmt ws
    | NOT ws -> ToRocq.pp_with_ws "NOT" fmt ws
    | ROR ws -> ToRocq.pp_with_ws "ROR" fmt ws
    | ROL ws -> ToRocq.pp_with_ws "ROL" fmt ws
    | RCR ws -> ToRocq.pp_with_ws "RCR" fmt ws
    | RCL ws -> ToRocq.pp_with_ws "RCL" fmt ws
    | SHL ws -> ToRocq.pp_with_ws "SHL" fmt ws
    | SHR ws -> ToRocq.pp_with_ws "SHR" fmt ws
    | SAL ws -> ToRocq.pp_with_ws "SAL" fmt ws
    | SAR ws -> ToRocq.pp_with_ws "SAR" fmt ws
    | SHLD ws -> ToRocq.pp_with_ws "SHLD" fmt ws
    | SHRD ws -> ToRocq.pp_with_ws "SHRD" fmt ws
    | RORX ws -> ToRocq.pp_with_ws "RORX" fmt ws
    | SARX ws -> ToRocq.pp_with_ws "SARX" fmt ws
    | SHRX ws -> ToRocq.pp_with_ws "SHRX" fmt ws
    | SHLX ws -> ToRocq.pp_with_ws "SHLX" fmt ws
    | MULX_lo_hi ws -> ToRocq.pp_with_ws "MULX_lo_hi" fmt ws
    | ADCX ws -> ToRocq.pp_with_ws "ADCX" fmt ws
    | ADOX ws -> ToRocq.pp_with_ws "ADOX" fmt ws
    | BSWAP ws -> ToRocq.pp_with_ws "BSWAP" fmt ws
    | POPCNT ws -> ToRocq.pp_with_ws "POPCNT" fmt ws
    | BTR ws -> ToRocq.pp_with_ws "BTR" fmt ws
    | BTS ws -> ToRocq.pp_with_ws "BTS" fmt ws
    | PEXT ws -> ToRocq.pp_with_ws "PEXT" fmt ws
    | PDEP ws -> ToRocq.pp_with_ws "PDEP" fmt ws
    | MOVX ws -> ToRocq.pp_with_ws "MOVX" fmt ws
    | POR -> ToRocq.pp_bare "POR" fmt
    | PADD (ve, ws) -> ToRocq.pp_ve_ws "PADD" fmt (ve, ws)
    | MOVD ws -> ToRocq.pp_with_ws "MOVD" fmt ws
    | MOVV ws -> ToRocq.pp_with_ws "MOVV" fmt ws
    | VMOV ws -> ToRocq.pp_with_ws "VMOV" fmt ws
    | VMOVDQA ws -> ToRocq.pp_with_ws "VMOVDQA" fmt ws
    | VMOVDQU ws -> ToRocq.pp_with_ws "VMOVDQU" fmt ws
    | VPMOVSX (v1, w1, v2, w2) -> ToRocq.pp_ve_ws_ve_ws "VPMOVSX" fmt (v1, w1, v2, w2)
    | VPMOVZX (v1, w1, v2, w2) -> ToRocq.pp_ve_ws_ve_ws "VPMOVZX" fmt (v1, w1, v2, w2)
    | VPAND ws -> ToRocq.pp_with_ws "VPAND" fmt ws
    | VPANDN ws -> ToRocq.pp_with_ws "VPANDN" fmt ws
    | VPOR ws -> ToRocq.pp_with_ws "VPOR" fmt ws
    | VPXOR ws -> ToRocq.pp_with_ws "VPXOR" fmt ws
    | VPADD (v, w) -> ToRocq.pp_ve_ws "VPADD" fmt (v, w)
    | VPSUB (v, w) -> ToRocq.pp_ve_ws "VPSUB" fmt (v, w)
    | VPAVG (v, w) -> ToRocq.pp_ve_ws "VPAVG" fmt (v, w)
    | VPMULL (v, w) -> ToRocq.pp_ve_ws "VPMULL" fmt (v, w)
    | VPMULH ws -> ToRocq.pp_with_ws "VPMULH" fmt ws
    | VPMULHU ws -> ToRocq.pp_with_ws "VPMULHU" fmt ws
    | VPMULHRS ws -> ToRocq.pp_with_ws "VPMULHRS" fmt ws
    | VPMUL ws -> ToRocq.pp_with_ws "VPMUL" fmt ws
    | VPMULU ws -> ToRocq.pp_with_ws "VPMULU" fmt ws
    | VPEXTR ws -> ToRocq.pp_with_ws "VPEXTR" fmt ws
    | VPINSR ve -> ToRocq.pp_ve "VPINSR" fmt ve
    | VPSLL (v, w) -> ToRocq.pp_ve_ws "VPSLL" fmt (v, w)
    | VPSRL (v, w) -> ToRocq.pp_ve_ws "VPSRL" fmt (v, w)
    | VPSRA (v, w) -> ToRocq.pp_ve_ws "VPSRA" fmt (v, w)
    | VPSLLV (v, w) -> ToRocq.pp_ve_ws "VPSLLV" fmt (v, w)
    | VPSRLV (v, w) -> ToRocq.pp_ve_ws "VPSRLV" fmt (v, w)
    | VPSLLDQ ws -> ToRocq.pp_with_ws "VPSLLDQ" fmt ws
    | VPSRLDQ ws -> ToRocq.pp_with_ws "VPSRLDQ" fmt ws
    | VPSHUFB ws -> ToRocq.pp_with_ws "VPSHUFB" fmt ws
    | VPSHUFD ws -> ToRocq.pp_with_ws "VPSHUFD" fmt ws
    | VPSHUFHW ws -> ToRocq.pp_with_ws "VPSHUFHW" fmt ws
    | VPSHUFLW ws -> ToRocq.pp_with_ws "VPSHUFLW" fmt ws
    | VPBLEND (v, w) -> ToRocq.pp_ve_ws "VPBLEND" fmt (v, w)
    | BLENDV (v, w) -> ToRocq.pp_ve_ws "BLENDV" fmt (v, w)
    | VPACKUS (v, w) -> ToRocq.pp_ve_ws "VPACKUS" fmt (v, w)
    | VPACKSS (v, w) -> ToRocq.pp_ve_ws "VPACKSS" fmt (v, w)
    | VSHUFPS ws -> ToRocq.pp_with_ws "VSHUFPS" fmt ws
    | VPBROADCAST (v, w) -> ToRocq.pp_ve_ws "VPBROADCAST" fmt (v, w)
    | VMOVSHDUP ws -> ToRocq.pp_with_ws "VMOVSHDUP" fmt ws
    | VMOVSLDUP ws -> ToRocq.pp_with_ws "VMOVSLDUP" fmt ws
    | VPALIGNR ws -> ToRocq.pp_with_ws "VPALIGNR" fmt ws
    | VBROADCASTI128 -> ToRocq.pp_bare "VBROADCASTI128" fmt
    | VPUNPCKH (v, w) -> ToRocq.pp_ve_ws "VPUNPCKH" fmt (v, w)
    | VPUNPCKL (v, w) -> ToRocq.pp_ve_ws "VPUNPCKL" fmt (v, w)
    | VEXTRACTI128 -> ToRocq.pp_bare "VEXTRACTI128" fmt
    | VINSERTI128 -> ToRocq.pp_bare "VINSERTI128" fmt
    | VPERM2I128 -> ToRocq.pp_bare "VPERM2I128" fmt
    | VPERMD -> ToRocq.pp_bare "VPERMD" fmt
    | VPERMQ -> ToRocq.pp_bare "VPERMQ" fmt
    | MOVEMASK (v, w) -> ToRocq.pp_ve_ws "MOVEMASK" fmt (v, w)
    | VPCMPEQ (v, w) -> ToRocq.pp_ve_ws "VPCMPEQ" fmt (v, w)
    | VPCMPGT (v, w) -> ToRocq.pp_ve_ws "VPCMPGT" fmt (v, w)
    | VPSIGN (v, w) -> ToRocq.pp_ve_ws "VPSIGN" fmt (v, w)
    | VPMADDUBSW ws -> ToRocq.pp_with_ws "VPMADDUBSW" fmt ws
    | VPMADDWD ws -> ToRocq.pp_with_ws "VPMADDWD" fmt ws
    | VMOVLPD -> ToRocq.pp_bare "VMOVLPD" fmt
    | VMOVHPD -> ToRocq.pp_bare "VMOVHPD" fmt
    | VPMINU (v, w) -> ToRocq.pp_ve_ws "VPMINU" fmt (v, w)
    | VPMINS (v, w) -> ToRocq.pp_ve_ws "VPMINS" fmt (v, w)
    | VPMAXU (v, w) -> ToRocq.pp_ve_ws "VPMAXU" fmt (v, w)
    | VPMAXS (v, w) -> ToRocq.pp_ve_ws "VPMAXS" fmt (v, w)
    | VPABS (v, w) -> ToRocq.pp_ve_ws "VPABS" fmt (v, w)
    | VPTEST ws -> ToRocq.pp_with_ws "VPTEST" fmt ws
    | CLFLUSH -> ToRocq.pp_bare "CLFLUSH" fmt
    | PREFETCHT0 -> ToRocq.pp_bare "PREFETCHT0" fmt
    | PREFETCHT1 -> ToRocq.pp_bare "PREFETCHT1" fmt
    | PREFETCHT2 -> ToRocq.pp_bare "PREFETCHT2" fmt
    | PREFETCHNTA -> ToRocq.pp_bare "PREFETCHNTA" fmt
    | LFENCE -> ToRocq.pp_bare "LFENCE" fmt
    | MFENCE -> ToRocq.pp_bare "MFENCE" fmt
    | SFENCE -> ToRocq.pp_bare "SFENCE" fmt
    | RDTSC ws -> ToRocq.pp_with_ws "RDTSC" fmt ws
    | RDTSCP ws -> ToRocq.pp_with_ws "RDTSCP" fmt ws
    | AESDEC -> ToRocq.pp_bare "AESDEC" fmt
    | VAESDEC ws -> ToRocq.pp_with_ws "VAESDEC" fmt ws
    | AESDECLAST -> ToRocq.pp_bare "AESDECLAST" fmt
    | VAESDECLAST ws -> ToRocq.pp_with_ws "VAESDECLAST" fmt ws
    | AESENC -> ToRocq.pp_bare "AESENC" fmt
    | VAESENC ws -> ToRocq.pp_with_ws "VAESENC" fmt ws
    | AESENCLAST -> ToRocq.pp_bare "AESENCLAST" fmt
    | VAESENCLAST ws -> ToRocq.pp_with_ws "VAESENCLAST" fmt ws
    | AESIMC -> ToRocq.pp_bare "AESIMC" fmt
    | VAESIMC -> ToRocq.pp_bare "VAESIMC" fmt
    | AESKEYGENASSIST -> ToRocq.pp_bare "AESKEYGENASSIST" fmt
    | VAESKEYGENASSIST -> ToRocq.pp_bare "VAESKEYGENASSIST" fmt
    | PCLMULQDQ -> ToRocq.pp_bare "PCLMULQDQ" fmt
    | VPCLMULQDQ ws -> ToRocq.pp_with_ws "VPCLMULQDQ" fmt ws
    | SHA256RNDS2 -> ToRocq.pp_bare "SHA256RNDS2" fmt
    | SHA256MSG1 -> ToRocq.pp_bare "SHA256MSG1" fmt
    | SHA256MSG2 -> ToRocq.pp_bare "SHA256MSG2" fmt

  let pp_extra_op_for_rocq fmt (o : extra_op) =
    let open X86_extra in
    match o with
    | Oset0 ws -> ToRocq.pp_with_ws "Oset0" fmt ws
    | Oconcat128 -> ToRocq.pp_bare "Oconcat128" fmt
    | Ox86MOVZX32 -> ToRocq.pp_bare "Ox86MOVZX32" fmt
    | Ox86MULX ws -> ToRocq.pp_with_ws "Ox86MULX" fmt ws
    | Ox86MULX_hi ws -> ToRocq.pp_with_ws "Ox86MULX_hi" fmt ws
    | Ox86SLHinit -> ToRocq.pp_bare "Ox86SLHinit" fmt
    | Ox86SLHupdate -> ToRocq.pp_bare "Ox86SLHupdate" fmt
    | Ox86SLHmove -> ToRocq.pp_bare "Ox86SLHmove" fmt
    | Ox86SLHprotect (rk, ws) -> ToRocq.pp_rk_ws "Ox86SLHprotect" fmt (rk, ws)

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
