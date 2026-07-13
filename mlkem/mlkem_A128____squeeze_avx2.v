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

(* A128____squeeze_avx2 *)
(* Local variables *)
Definition st_63 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16413).
Definition buf_93 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16414).
Definition _RATE8_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16415).
Definition offset_88 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16416).
Definition _LEN_56 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16417).
Definition ITERS_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16418).
Definition LO_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16419).
Definition i_38 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16420).

(* Signature *)
Definition tyin_A128____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 128; aint ].
Definition args_A128____squeeze_avx2 : seq var_i :=
  [:: st_63.(gv); buf_93.(gv); _RATE8_27.(gv) ].
Definition tyout_A128____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 128 ].
Definition res_A128____squeeze_avx2 : seq var_i :=
  [:: st_63.(gv); buf_93.(gv) ].

(* Body *)
Definition body_A128____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_88.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_56.(gv)) AT_none (aint) (Pconst (128)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_27.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_56) (Pvar _RATE8_27)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_10.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_56) (Pvar _RATE8_27)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_38.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_38) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_27)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_63.(gv) ] _keccakf1600_avx2 [:: Pvar st_63 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_93.(gv)
                                                                ; Lvar offset_88.(gv) ] A128____dumpstate_avx2 [:: Pvar buf_93
                                                                    ; Pvar offset_88
                                                                    ; Pvar _RATE8_27
                                                                    ; Pvar st_63 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_38.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_38) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_10))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_63.(gv) ] _keccakf1600_avx2 [:: Pvar st_63 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_93.(gv)
                                                                ; Lvar offset_88.(gv) ] A128____dumpstate_avx2 [:: Pvar buf_93
                                                                    ; Pvar offset_88
                                                                    ; Pvar LO_10
                                                                    ; Pvar st_63 ]) ]
                              [::]) ].

Definition fd_A128____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____squeeze_avx2;
    f_params := args_A128____squeeze_avx2;
    f_body := body_A128____squeeze_avx2;
    f_tyout := tyout_A128____squeeze_avx2;
    f_res := res_A128____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
