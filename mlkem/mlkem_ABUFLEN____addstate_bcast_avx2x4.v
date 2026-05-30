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
Definition st_114 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14484).
Definition AT_111 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14485).
Definition buf_164 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14486).
Definition offset_174 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14487).
Definition _LEN_107 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14488).
Definition _TRAILB_63 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14489).
Definition DELTA_116 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14490).
Definition AT8_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14491).
Definition w_116 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14492).
Definition j_at_19 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14493).

(* Signature *)
Definition tyin_ABUFLEN____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 536; aword U64; aint; aint ].
Definition args_ABUFLEN____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_114.(gv)
    ; AT_111.(gv)
    ; buf_164.(gv)
    ; offset_174.(gv)
    ; _LEN_107.(gv)
    ; _TRAILB_63.(gv) ].
Definition tyout_ABUFLEN____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_ABUFLEN____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_114.(gv); AT_111.(gv); offset_174.(gv) ].

(* Body *)
Definition body_ABUFLEN____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_116.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_43.(gv)) AT_none (aint) (Pvar AT_111))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_111.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_111) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_43) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_116.(gv)
                                                                ; Lvar _LEN_107.(gv)
                                                                ; Lvar _TRAILB_63.(gv)
                                                                ; Lvar AT8_43.(gv)
                                                                ; Lvar w_116.(gv) ] ABUFLEN____a_ilen_read_bcast_upto8_at [:: Pvar buf_164
                                                                    ; Pvar offset_174
                                                                    ; Pvar DELTA_116
                                                                    ; Pvar _LEN_107
                                                                    ; Pvar _TRAILB_63
                                                                    ; Pvar AT_111
                                                                    ; Pvar AT8_43 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_116.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_116) (Pget Aligned AAscale U256 st_114 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_111) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_114.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_111) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_116))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_111.(gv)) AT_none (aint) (Pvar AT8_43)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_174.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_174) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_116))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_19.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_111) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_19) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_111) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_107) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_116.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_164 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_174)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_174.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_174) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_116.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_116) (Pget Unaligned AAdirect U256 st_114 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_19)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_114.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_19))) AT_none (aword U256) (Pvar w_116))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_19.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_19) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_111.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_111) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_107) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_107.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_107) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_107)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_63) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_116.(gv)
                                                                ; Lvar _LEN_107.(gv)
                                                                ; Lvar _TRAILB_63.(gv)
                                                                ; Lvar AT_111.(gv)
                                                                ; Lvar w_116.(gv) ] ABUFLEN____a_ilen_read_bcast_upto8_at [:: Pvar buf_164
                                                                    ; Pvar offset_174
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_107
                                                                    ; Pvar _TRAILB_63
                                                                    ; Pvar AT_111
                                                                    ; Pvar AT_111 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_116.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_116) (Pget Unaligned AAdirect U256 st_114 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_19)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_114.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_19))) AT_none (aword U256) (Pvar w_116))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_174.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_174) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_116)))) ]
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
