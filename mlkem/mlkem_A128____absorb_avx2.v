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

(* A128____absorb_avx2 *)
(* Local variables *)
Definition st_61 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16445).
Definition AT_60 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16446).
Definition buf_91 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16447).
Definition _TRAILB_32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16448).
Definition _RATE8_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16449).
Definition offset_86 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16450).
Definition _LEN_54 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16451).
Definition ITERS_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16452).
Definition i_37 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16453).

(* Signature *)
Definition tyin_A128____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 128; aint; aint ].
Definition args_A128____absorb_avx2 : seq var_i :=
  [:: st_61.(gv); AT_60.(gv); buf_91.(gv); _TRAILB_32.(gv); _RATE8_26.(gv) ].
Definition tyout_A128____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A128____absorb_avx2 : seq var_i :=
  [:: st_61.(gv); AT_60.(gv) ].

(* Body *)
Definition body_A128____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_86.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_54.(gv)) AT_none (aint) (Pconst (128)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_60) (Pvar _LEN_54)) (Pvar _RATE8_26))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_61.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_86.(gv) ] A128____addstate_avx2 [:: Pvar st_61
                                                                    ; Pvar AT_60
                                                                    ; Pvar buf_91
                                                                    ; Pvar offset_86
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_26) (Pvar AT_60)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_54.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_54) (Papp2 (Osub (Op_int)) (Pvar _RATE8_26) (Pvar AT_60))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_60.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_61.(gv) ] _keccakf1600_avx2 [:: Pvar st_61 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_26.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_54) (Pvar _RATE8_26)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_37.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_37) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_26)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_61.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_86.(gv) ] A128____addstate_avx2 [:: Pvar st_61
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_91
                                                                    ; Pvar offset_86
                                                                    ; Pvar _RATE8_26
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_61.(gv) ] _keccakf1600_avx2 [:: Pvar st_61 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_37.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_37) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_54.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_54) (Pvar _RATE8_26))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_61.(gv)
                                    ; Lvar AT_60.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A128____addstate_avx2 [:: Pvar st_61
                                                                    ; Pvar AT_60
                                                                    ; Pvar buf_91
                                                                    ; Pvar offset_86
                                                                    ; Pvar _LEN_54
                                                                    ; Pvar _TRAILB_32 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_32) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_61.(gv) ] __addratebit_avx2 [:: Pvar st_61
                                                                    ; Pvar _RATE8_26 ]) ]
                              [::]) ].

Definition fd_A128____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____absorb_avx2;
    f_params := args_A128____absorb_avx2;
    f_body := body_A128____absorb_avx2;
    f_tyout := tyout_A128____absorb_avx2;
    f_res := res_A128____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
