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

(* A2____absorb_avx2 *)
(* Local variables *)
Definition st_17838 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17838).
Definition AT_17839 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17839).
Definition buf_17840 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17840).
Definition _TRAILB_17841 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17841).
Definition _RATE8_17842 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17842).
Definition offset_17843 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17843).
Definition _LEN_17844 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17844).
Definition ITERS_17845 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17845).
Definition i_17846 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17846).

(* Signature *)
Definition tyin_A2____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 2; aint; aint ].
Definition args_A2____absorb_avx2 : seq var_i :=
  [:: st_17838.(gv)
    ; AT_17839.(gv)
    ; buf_17840.(gv)
    ; _TRAILB_17841.(gv)
    ; _RATE8_17842.(gv) ].
Definition tyout_A2____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A2____absorb_avx2 : seq var_i :=
  [:: st_17838.(gv); AT_17839.(gv) ].

(* Body *)
Definition body_A2____absorb_avx2 : cmd :=
  [:: cassgn (Lvar offset_17843.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_17844.(gv)) (aint) (Pconst (2)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_17839) (Pvar _LEN_17844)) (Pvar _RATE8_17842))
        [:: ccall [:: Lvar st_17838.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_17843.(gv) ] A2____addstate_avx2 [:: Pvar st_17838
                                                                    ; Pvar AT_17839
                                                                    ; Pvar buf_17840
                                                                    ; Pvar offset_17843
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_17842) (Pvar AT_17839)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_17844.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_17844) (Papp2 (Osub (Op_int)) (Pvar _RATE8_17842) (Pvar AT_17839)))
          ; cassgn (Lvar AT_17839.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_17838.(gv) ] _keccakf1600_avx2 [:: Pvar st_17838 ]
          ; cassgn (Lvar ITERS_17845.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17844) (Pvar _RATE8_17842))
          ; cassgn (Lvar i_17846.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17846) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17845)))
              [:: ccall [:: Lvar st_17838.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_17843.(gv) ] A2____addstate_avx2 [:: Pvar st_17838
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_17840
                                                                    ; Pvar offset_17843
                                                                    ; Pvar _RATE8_17842
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_17838.(gv) ] _keccakf1600_avx2 [:: Pvar st_17838 ]
                ; cassgn (Lvar i_17846.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17846) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_17844.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17844) (Pvar _RATE8_17842)) ]
        [::]
    ; ccall [:: Lvar st_17838.(gv)
              ; Lvar AT_17839.(gv)
              ; Lnone dummy_var_info (aword U64) ] A2____addstate_avx2 [:: Pvar st_17838
                                                                    ; Pvar AT_17839
                                                                    ; Pvar buf_17840
                                                                    ; Pvar offset_17843
                                                                    ; Pvar _LEN_17844
                                                                    ; Pvar _TRAILB_17841 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17841) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_17838.(gv) ] __addratebit_avx2 [:: Pvar st_17838
                                                               ; Pvar _RATE8_17842 ] ]
        [::] ].

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
