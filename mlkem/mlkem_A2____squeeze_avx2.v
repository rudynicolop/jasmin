From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A2____squeeze_avx2 *)
(* Local variables *)
Definition st_17806 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17806).
Definition buf_17807 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17807).
Definition _RATE8_17808 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17808).
Definition offset_17809 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17809).
Definition _LEN_17810 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17810).
Definition ITERS_17811 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17811).
Definition LO_17812 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17812).
Definition i_17813 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17813).

(* Signature *)
Definition tyin_A2____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 2; aint ].
Definition args_A2____squeeze_avx2 : seq var_i :=
  [:: st_17806.(gv); buf_17807.(gv); _RATE8_17808.(gv) ].
Definition tyout_A2____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 2 ].
Definition res_A2____squeeze_avx2 : seq var_i :=
  [:: st_17806.(gv); buf_17807.(gv) ].

(* Body *)
Definition body_A2____squeeze_avx2 : cmd :=
  [:: cassgn (Lvar offset_17809.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_17810.(gv)) (aint) (Pconst (2)%Z)
    ; cassgn (Lvar ITERS_17811.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17810) (Pvar _RATE8_17808))
    ; cassgn (Lvar LO_17812.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17810) (Pvar _RATE8_17808))
    ; cassgn (Lvar i_17813.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17813) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17811)))
        [:: ccall [:: Lvar st_17806.(gv) ] _keccakf1600_avx2 [:: Pvar st_17806 ]
          ; ccall [:: Lvar buf_17807.(gv); Lvar offset_17809.(gv) ] A2____dumpstate_avx2 [:: Pvar buf_17807
                                                                    ; Pvar offset_17809
                                                                    ; Pvar _RATE8_17808
                                                                    ; Pvar st_17806 ]
          ; cassgn (Lvar i_17813.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17813) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_17812))
        [:: ccall [:: Lvar st_17806.(gv) ] _keccakf1600_avx2 [:: Pvar st_17806 ]
          ; ccall [:: Lvar buf_17807.(gv); Lvar offset_17809.(gv) ] A2____dumpstate_avx2 [:: Pvar buf_17807
                                                                    ; Pvar offset_17809
                                                                    ; Pvar LO_17812
                                                                    ; Pvar st_17806 ] ]
        [::] ].

Definition fd_A2____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____squeeze_avx2;
    f_params := args_A2____squeeze_avx2;
    f_body := body_A2____squeeze_avx2;
    f_tyout := tyout_A2____squeeze_avx2;
    f_res := res_A2____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
