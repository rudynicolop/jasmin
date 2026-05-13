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

(* A64____absorb_avx2 *)
(* Local variables *)
Definition st_16692 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16692).
Definition AT_16693 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16693).
Definition buf_16694 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 16694).
Definition _TRAILB_16695 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16695).
Definition _RATE8_16696 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16696).
Definition offset_16697 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16697).
Definition _LEN_16698 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16698).
Definition ITERS_16699 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16699).
Definition i_16700 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16700).

(* Signature *)
Definition tyin_A64____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 64; aint; aint ].
Definition args_A64____absorb_avx2 : seq var_i :=
  [:: st_16692.(gv)
    ; AT_16693.(gv)
    ; buf_16694.(gv)
    ; _TRAILB_16695.(gv)
    ; _RATE8_16696.(gv) ].
Definition tyout_A64____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A64____absorb_avx2 : seq var_i :=
  [:: st_16692.(gv); AT_16693.(gv) ].

(* Body *)
Definition body_A64____absorb_avx2 : cmd :=
  [:: cassgn (Lvar offset_16697.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_16698.(gv)) (aint) (Pconst (64)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_16693) (Pvar _LEN_16698)) (Pvar _RATE8_16696))
        [:: ccall [:: Lvar st_16692.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_16697.(gv) ] A64____addstate_avx2 [:: Pvar st_16692
                                                                    ; Pvar AT_16693
                                                                    ; Pvar buf_16694
                                                                    ; Pvar offset_16697
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_16696) (Pvar AT_16693)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_16698.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16698) (Papp2 (Osub (Op_int)) (Pvar _RATE8_16696) (Pvar AT_16693)))
          ; cassgn (Lvar AT_16693.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_16692.(gv) ] _keccakf1600_avx2 [:: Pvar st_16692 ]
          ; cassgn (Lvar ITERS_16699.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16698) (Pvar _RATE8_16696))
          ; cassgn (Lvar i_16700.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16700) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16699)))
              [:: ccall [:: Lvar st_16692.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_16697.(gv) ] A64____addstate_avx2 [:: Pvar st_16692
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_16694
                                                                    ; Pvar offset_16697
                                                                    ; Pvar _RATE8_16696
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_16692.(gv) ] _keccakf1600_avx2 [:: Pvar st_16692 ]
                ; cassgn (Lvar i_16700.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16700) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_16698.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16698) (Pvar _RATE8_16696)) ]
        [::]
    ; ccall [:: Lvar st_16692.(gv)
              ; Lvar AT_16693.(gv)
              ; Lnone dummy_var_info (aword U64) ] A64____addstate_avx2 [:: Pvar st_16692
                                                                    ; Pvar AT_16693
                                                                    ; Pvar buf_16694
                                                                    ; Pvar offset_16697
                                                                    ; Pvar _LEN_16698
                                                                    ; Pvar _TRAILB_16695 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16695) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_16692.(gv) ] __addratebit_avx2 [:: Pvar st_16692
                                                               ; Pvar _RATE8_16696 ] ]
        [::] ].

Definition fd_A64____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____absorb_avx2;
    f_params := args_A64____absorb_avx2;
    f_body := body_A64____absorb_avx2;
    f_tyout := tyout_A64____absorb_avx2;
    f_res := res_A64____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
