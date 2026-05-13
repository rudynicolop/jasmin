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

(* A33____absorb_avx2 *)
(* Local variables *)
Definition st_17074 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17074).
Definition AT_17075 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17075).
Definition buf_17076 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17076).
Definition _TRAILB_17077 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17077).
Definition _RATE8_17078 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17078).
Definition offset_17079 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17079).
Definition _LEN_17080 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17080).
Definition ITERS_17081 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17081).
Definition i_17082 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17082).

(* Signature *)
Definition tyin_A33____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 33; aint; aint ].
Definition args_A33____absorb_avx2 : seq var_i :=
  [:: st_17074.(gv)
    ; AT_17075.(gv)
    ; buf_17076.(gv)
    ; _TRAILB_17077.(gv)
    ; _RATE8_17078.(gv) ].
Definition tyout_A33____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A33____absorb_avx2 : seq var_i :=
  [:: st_17074.(gv); AT_17075.(gv) ].

(* Body *)
Definition body_A33____absorb_avx2 : cmd :=
  [:: cassgn (Lvar offset_17079.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_17080.(gv)) (aint) (Pconst (33)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_17075) (Pvar _LEN_17080)) (Pvar _RATE8_17078))
        [:: ccall [:: Lvar st_17074.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_17079.(gv) ] A33____addstate_avx2 [:: Pvar st_17074
                                                                    ; Pvar AT_17075
                                                                    ; Pvar buf_17076
                                                                    ; Pvar offset_17079
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_17078) (Pvar AT_17075)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_17080.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_17080) (Papp2 (Osub (Op_int)) (Pvar _RATE8_17078) (Pvar AT_17075)))
          ; cassgn (Lvar AT_17075.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_17074.(gv) ] _keccakf1600_avx2 [:: Pvar st_17074 ]
          ; cassgn (Lvar ITERS_17081.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17080) (Pvar _RATE8_17078))
          ; cassgn (Lvar i_17082.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17082) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17081)))
              [:: ccall [:: Lvar st_17074.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_17079.(gv) ] A33____addstate_avx2 [:: Pvar st_17074
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_17076
                                                                    ; Pvar offset_17079
                                                                    ; Pvar _RATE8_17078
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_17074.(gv) ] _keccakf1600_avx2 [:: Pvar st_17074 ]
                ; cassgn (Lvar i_17082.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17082) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_17080.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17080) (Pvar _RATE8_17078)) ]
        [::]
    ; ccall [:: Lvar st_17074.(gv)
              ; Lvar AT_17075.(gv)
              ; Lnone dummy_var_info (aword U64) ] A33____addstate_avx2 [:: Pvar st_17074
                                                                    ; Pvar AT_17075
                                                                    ; Pvar buf_17076
                                                                    ; Pvar offset_17079
                                                                    ; Pvar _LEN_17080
                                                                    ; Pvar _TRAILB_17077 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17077) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_17074.(gv) ] __addratebit_avx2 [:: Pvar st_17074
                                                               ; Pvar _RATE8_17078 ] ]
        [::] ].

Definition fd_A33____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____absorb_avx2;
    f_params := args_A33____absorb_avx2;
    f_body := body_A33____absorb_avx2;
    f_tyout := tyout_A33____absorb_avx2;
    f_res := res_A33____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
