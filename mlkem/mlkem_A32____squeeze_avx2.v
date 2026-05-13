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

(* A32____squeeze_avx2 *)
(* Local variables *)
Definition st_17424 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17424).
Definition buf_17425 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17425).
Definition _RATE8_17426 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17426).
Definition offset_17427 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17427).
Definition _LEN_17428 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17428).
Definition ITERS_17429 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17429).
Definition LO_17430 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17430).
Definition i_17431 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17431).

(* Signature *)
Definition tyin_A32____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 32; aint ].
Definition args_A32____squeeze_avx2 : seq var_i :=
  [:: st_17424.(gv); buf_17425.(gv); _RATE8_17426.(gv) ].
Definition tyout_A32____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 32 ].
Definition res_A32____squeeze_avx2 : seq var_i :=
  [:: st_17424.(gv); buf_17425.(gv) ].

(* Body *)
Definition body_A32____squeeze_avx2 : cmd :=
  [:: cassgn (Lvar offset_17427.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_17428.(gv)) (aint) (Pconst (32)%Z)
    ; cassgn (Lvar ITERS_17429.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17428) (Pvar _RATE8_17426))
    ; cassgn (Lvar LO_17430.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17428) (Pvar _RATE8_17426))
    ; cassgn (Lvar i_17431.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17431) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17429)))
        [:: ccall [:: Lvar st_17424.(gv) ] _keccakf1600_avx2 [:: Pvar st_17424 ]
          ; ccall [:: Lvar buf_17425.(gv); Lvar offset_17427.(gv) ] A32____dumpstate_avx2 [:: Pvar buf_17425
                                                                    ; Pvar offset_17427
                                                                    ; Pvar _RATE8_17426
                                                                    ; Pvar st_17424 ]
          ; cassgn (Lvar i_17431.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17431) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_17430))
        [:: ccall [:: Lvar st_17424.(gv) ] _keccakf1600_avx2 [:: Pvar st_17424 ]
          ; ccall [:: Lvar buf_17425.(gv); Lvar offset_17427.(gv) ] A32____dumpstate_avx2 [:: Pvar buf_17425
                                                                    ; Pvar offset_17427
                                                                    ; Pvar LO_17430
                                                                    ; Pvar st_17424 ] ]
        [::] ].

Definition fd_A32____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____squeeze_avx2;
    f_params := args_A32____squeeze_avx2;
    f_body := body_A32____squeeze_avx2;
    f_tyout := tyout_A32____squeeze_avx2;
    f_res := res_A32____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
