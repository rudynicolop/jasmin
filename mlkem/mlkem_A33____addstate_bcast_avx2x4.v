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

(* A33____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_50 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17023).
Definition AT_45 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17024).
Definition buf_68 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17025).
Definition offset_61 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17026).
Definition _LEN_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17027).
Definition _TRAILB_25 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17028).
Definition DELTA_41 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17029).
Definition AT8_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17030).
Definition w_47 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17031).
Definition j_at_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17032).

(* Signature *)
Definition tyin_A33____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 33; aword U64; aint; aint ].
Definition args_A33____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_50.(gv)
    ; AT_45.(gv)
    ; buf_68.(gv)
    ; offset_61.(gv)
    ; _LEN_43.(gv)
    ; _TRAILB_25.(gv) ].
Definition tyout_A33____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A33____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_50.(gv); AT_45.(gv); offset_61.(gv) ].

(* Body *)
Definition body_A33____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_41.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_17.(gv)) AT_none (aint) (Pvar AT_45))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_45.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_45) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_17) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_41.(gv)
                                                                ; Lvar _LEN_43.(gv)
                                                                ; Lvar _TRAILB_25.(gv)
                                                                ; Lvar AT8_17.(gv)
                                                                ; Lvar w_47.(gv) ] A33____a_ilen_read_bcast_upto8_at [:: Pvar buf_68
                                                                    ; Pvar offset_61
                                                                    ; Pvar DELTA_41
                                                                    ; Pvar _LEN_43
                                                                    ; Pvar _TRAILB_25
                                                                    ; Pvar AT_45
                                                                    ; Pvar AT8_17 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_47.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_47) (Pget Aligned AAscale U256 st_50 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_45) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_50.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_45) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_47))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_45.(gv)) AT_none (aint) (Pvar AT8_17)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_61.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_61) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_41))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_7.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_45) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_7) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_45) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_43) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_47.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_68 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_61)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_61.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_61) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_47.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_47) (Pget Unaligned AAdirect U256 st_50 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_7)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_50.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_7))) AT_none (aword U256) (Pvar w_47))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_7.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_7) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_45.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_45) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_43) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_43.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_43) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_43)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_25) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_41.(gv)
                                                                ; Lvar _LEN_43.(gv)
                                                                ; Lvar _TRAILB_25.(gv)
                                                                ; Lvar AT_45.(gv)
                                                                ; Lvar w_47.(gv) ] A33____a_ilen_read_bcast_upto8_at [:: Pvar buf_68
                                                                    ; Pvar offset_61
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_43
                                                                    ; Pvar _TRAILB_25
                                                                    ; Pvar AT_45
                                                                    ; Pvar AT_45 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_47.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_47) (Pget Unaligned AAdirect U256 st_50 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_7)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_50.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_7))) AT_none (aword U256) (Pvar w_47))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_61.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_61) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_41)))) ]
                              [::]) ].

Definition fd_A33____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____addstate_bcast_avx2x4;
    f_params := args_A33____addstate_bcast_avx2x4;
    f_body := body_A33____addstate_bcast_avx2x4;
    f_tyout := tyout_A33____addstate_bcast_avx2x4;
    f_res := res_A33____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
