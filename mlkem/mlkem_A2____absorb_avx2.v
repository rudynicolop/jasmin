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

(* A2____absorb_avx2 *)
(* Local variables *)
Definition st_27 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17838).
Definition AT_24 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17839).
Definition buf_37 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17840).
Definition _TRAILB_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17841).
Definition _RATE8_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17842).
Definition offset_24 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17843).
Definition _LEN_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17844).
Definition ITERS_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17845).
Definition i_17 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17846).

(* Signature *)
Definition tyin_A2____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 2; aint; aint ].
Definition args_A2____absorb_avx2 : seq var_i :=
  [:: st_27.(gv); AT_24.(gv); buf_37.(gv); _TRAILB_12.(gv); _RATE8_9.(gv) ].
Definition tyout_A2____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A2____absorb_avx2 : seq var_i := [:: st_27.(gv); AT_24.(gv) ].

(* Body *)
Definition body_A2____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_24.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_20.(gv)) AT_none (aint) (Pconst (2)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_24) (Pvar _LEN_20)) (Pvar _RATE8_9))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_27.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_24.(gv) ] A2____addstate_avx2 [:: Pvar st_27
                                                                    ; Pvar AT_24
                                                                    ; Pvar buf_37
                                                                    ; Pvar offset_24
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_9) (Pvar AT_24)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_20.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_20) (Papp2 (Osub (Op_int)) (Pvar _RATE8_9) (Pvar AT_24))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_24.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_27.(gv) ] _keccakf1600_avx2 [:: Pvar st_27 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_9.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_20) (Pvar _RATE8_9)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_17.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_9)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_27.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_24.(gv) ] A2____addstate_avx2 [:: Pvar st_27
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_37
                                                                    ; Pvar offset_24
                                                                    ; Pvar _RATE8_9
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_27.(gv) ] _keccakf1600_avx2 [:: Pvar st_27 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_17.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_20.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_20) (Pvar _RATE8_9))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_27.(gv)
                                    ; Lvar AT_24.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A2____addstate_avx2 [:: Pvar st_27
                                                                    ; Pvar AT_24
                                                                    ; Pvar buf_37
                                                                    ; Pvar offset_24
                                                                    ; Pvar _LEN_20
                                                                    ; Pvar _TRAILB_12 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_12) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_27.(gv) ] __addratebit_avx2 [:: Pvar st_27
                                                                    ; Pvar _RATE8_9 ]) ]
                              [::]) ].

Definition fd_A2____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____absorb_avx2;
    f_params := args_A2____absorb_avx2;
    f_body := body_A2____absorb_avx2;
    f_tyout := tyout_A2____absorb_avx2;
    f_res := res_A2____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
