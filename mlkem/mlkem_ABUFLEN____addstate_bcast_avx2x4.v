From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* ABUFLEN____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_14484 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14484).
Definition AT_14485 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14485).
Definition buf_14486 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14486).
Definition offset_14487 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14487).
Definition _LEN_14488 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14488).
Definition _TRAILB_14489 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14489).
Definition DELTA_14490 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14490).
Definition AT8_14491 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14491).
Definition w_14492 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14492).
Definition j_at_14493 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14493).

(* Signature *)
Definition tyin_ABUFLEN____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 536; aword U64; aint; aint ].
Definition args_ABUFLEN____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_14484.(gv)
    ; AT_14485.(gv)
    ; buf_14486.(gv)
    ; offset_14487.(gv)
    ; _LEN_14488.(gv)
    ; _TRAILB_14489.(gv) ].
Definition tyout_ABUFLEN____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_ABUFLEN____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_14484.(gv); AT_14485.(gv); offset_14487.(gv) ].

(* Body *)
Definition body_ABUFLEN____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_14490.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_14491.(gv)) AT_none (aint) (Pvar AT_14485))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_14485.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14485) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_14491) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_14490.(gv)
                                                                ; Lvar _LEN_14488.(gv)
                                                                ; Lvar _TRAILB_14489.(gv)
                                                                ; Lvar AT8_14491.(gv)
                                                                ; Lvar w_14492.(gv) ] ABUFLEN____a_ilen_read_bcast_upto8_at [:: Pvar buf_14486
                                                                    ; Pvar offset_14487
                                                                    ; Pvar DELTA_14490
                                                                    ; Pvar _LEN_14488
                                                                    ; Pvar _TRAILB_14489
                                                                    ; Pvar AT_14485
                                                                    ; Pvar AT8_14491 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_14492.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_14492) (Pget Aligned AAscale U256 st_14484 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14485) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_14484.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14485) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_14492))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_14485.(gv)) AT_none (aint) (Pvar AT8_14491)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_14487.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14487) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14490))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_14493.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14485) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_14493) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14485) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14488) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_14492.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_14486 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14487)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_14487.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14487) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_14492.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_14492) (Pget Unaligned AAdirect U256 st_14484 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_14493)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_14484.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_14493))) AT_none (aword U256) (Pvar w_14492))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_14493.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14493) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_14485.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_14485) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14488) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14488.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14488) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14488)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_14489) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_14490.(gv)
                                                                ; Lvar _LEN_14488.(gv)
                                                                ; Lvar _TRAILB_14489.(gv)
                                                                ; Lvar AT_14485.(gv)
                                                                ; Lvar w_14492.(gv) ] ABUFLEN____a_ilen_read_bcast_upto8_at [:: Pvar buf_14486
                                                                    ; Pvar offset_14487
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14488
                                                                    ; Pvar _TRAILB_14489
                                                                    ; Pvar AT_14485
                                                                    ; Pvar AT_14485 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_14492.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_14492) (Pget Unaligned AAdirect U256 st_14484 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_14493)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_14484.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_14493))) AT_none (aword U256) (Pvar w_14492))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_14487.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14487) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14490)))) ]
                              [::]) ].

Definition fd_ABUFLEN____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____addstate_bcast_avx2x4;
    f_params := args_ABUFLEN____addstate_bcast_avx2x4;
    f_body := body_ABUFLEN____addstate_bcast_avx2x4;
    f_tyout := tyout_ABUFLEN____addstate_bcast_avx2x4;
    f_res := res_ABUFLEN____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
