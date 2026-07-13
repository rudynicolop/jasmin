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

(* A1____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_20 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18169).
Definition AT_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18170).
Definition buf_26 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18171).
Definition offset_10 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18172).
Definition _LEN_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18173).
Definition _TRAILB_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18174).
Definition DELTA_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18175).
Definition AT8_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18176).
Definition w_17 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18177).
Definition j_at_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18178).

(* Signature *)
Definition tyin_A1____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1; aword U64; aint; aint ].
Definition args_A1____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_20.(gv)
    ; AT_15.(gv)
    ; buf_26.(gv)
    ; offset_10.(gv)
    ; _LEN_13.(gv)
    ; _TRAILB_7.(gv) ].
Definition tyout_A1____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_20.(gv); AT_15.(gv); offset_10.(gv) ].

(* Body *)
Definition body_A1____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_8.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_5.(gv)) AT_none (aint) (Pvar AT_15))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_5) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_8.(gv)
                                                                ; Lvar _LEN_13.(gv)
                                                                ; Lvar _TRAILB_7.(gv)
                                                                ; Lvar AT8_5.(gv)
                                                                ; Lvar w_17.(gv) ] A1____a_ilen_read_bcast_upto8_at [:: Pvar buf_26
                                                                    ; Pvar offset_10
                                                                    ; Pvar DELTA_8
                                                                    ; Pvar _LEN_13
                                                                    ; Pvar _TRAILB_7
                                                                    ; Pvar AT_15
                                                                    ; Pvar AT8_5 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_17.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_17) (Pget Aligned AAscale U256 st_20 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_20.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_17))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15.(gv)) AT_none (aint) (Pvar AT8_5)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_10.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_8))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_1.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_13) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_17.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_26 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_10)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_10.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_17.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_17) (Pget Unaligned AAdirect U256 st_20 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_1)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_20.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_1))) AT_none (aword U256) (Pvar w_17))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_15) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_13) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_13.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_13) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_13)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_7) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_8.(gv)
                                                                ; Lvar _LEN_13.(gv)
                                                                ; Lvar _TRAILB_7.(gv)
                                                                ; Lvar AT_15.(gv)
                                                                ; Lvar w_17.(gv) ] A1____a_ilen_read_bcast_upto8_at [:: Pvar buf_26
                                                                    ; Pvar offset_10
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_13
                                                                    ; Pvar _TRAILB_7
                                                                    ; Pvar AT_15
                                                                    ; Pvar AT_15 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_17.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_17) (Pget Unaligned AAdirect U256 st_20 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_1)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_20.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_1))) AT_none (aword U256) (Pvar w_17))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_10.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_8)))) ]
                              [::]) ].

Definition fd_A1____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____addstate_bcast_avx2x4;
    f_params := args_A1____addstate_bcast_avx2x4;
    f_body := body_A1____addstate_bcast_avx2x4;
    f_tyout := tyout_A1____addstate_bcast_avx2x4;
    f_res := res_A1____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
