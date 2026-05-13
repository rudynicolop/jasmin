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

(* A33____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_17007 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17007).
Definition AT_17008 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17008).
Definition buf_17009 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17009).
Definition _TRAILB_17010 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17010).
Definition _RATE8_17011 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17011).
Definition offset_17012 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17012).
Definition _LEN_17013 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17013).
Definition ITERS_17014 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17014).
Definition i_17015 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17015).

(* Signature *)
Definition tyin_A33____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 33; aint; aint ].
Definition args_A33____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_17007.(gv)
    ; AT_17008.(gv)
    ; buf_17009.(gv)
    ; _TRAILB_17010.(gv)
    ; _RATE8_17011.(gv) ].
Definition tyout_A33____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A33____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_17007.(gv); AT_17008.(gv) ].

(* Body *)
Definition body_A33____absorb_bcast_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_17012.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_17013.(gv)) (aint) (Pconst (33)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_17008) (Pvar _LEN_17013)) (Pvar _RATE8_17011))
        [:: ccall [:: Lvar st_17007.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_17012.(gv) ] A33____addstate_bcast_avx2x4 [:: Pvar st_17007
                                                                    ; Pvar AT_17008
                                                                    ; Pvar buf_17009
                                                                    ; Pvar offset_17012
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_17011) (Pvar AT_17008)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_17013.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_17013) (Papp2 (Osub (Op_int)) (Pvar _RATE8_17011) (Pvar AT_17008)))
          ; cassgn (Lvar AT_17008.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_17007.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17007 ]
          ; cassgn (Lvar ITERS_17014.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17013) (Pvar _RATE8_17011))
          ; cassgn (Lvar i_17015.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17015) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17014)))
              [:: ccall [:: Lvar st_17007.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_17012.(gv) ] A33____addstate_bcast_avx2x4 [:: Pvar st_17007
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_17009
                                                                    ; Pvar offset_17012
                                                                    ; Pvar _RATE8_17011
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_17007.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17007 ]
                ; cassgn (Lvar i_17015.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17015) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_17013.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17013) (Pvar _RATE8_17011)) ]
        [::]
    ; ccall [:: Lvar st_17007.(gv)
              ; Lvar AT_17008.(gv)
              ; Lnone dummy_var_info (aword U64) ] A33____addstate_bcast_avx2x4 [:: Pvar st_17007
                                                                    ; Pvar AT_17008
                                                                    ; Pvar buf_17009
                                                                    ; Pvar offset_17012
                                                                    ; Pvar _LEN_17013
                                                                    ; Pvar _TRAILB_17010 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17010) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_17007.(gv) ] __addratebit_avx2x4 [:: Pvar st_17007
                                                                 ; Pvar _RATE8_17011 ] ]
        [::] ].

Definition fd_A33____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____absorb_bcast_avx2x4;
    f_params := args_A33____absorb_bcast_avx2x4;
    f_body := body_A33____absorb_bcast_avx2x4;
    f_tyout := tyout_A33____absorb_bcast_avx2x4;
    f_res := res_A33____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
