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

(* A1____absorb_avx2 *)
(* Local variables *)
Definition st_18220 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18220).
Definition AT_18221 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18221).
Definition buf_18222 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18222).
Definition _TRAILB_18223 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18223).
Definition _RATE8_18224 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18224).
Definition offset_18225 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18225).
Definition _LEN_18226 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18226).
Definition ITERS_18227 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18227).
Definition i_18228 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18228).

(* Signature *)
Definition tyin_A1____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1; aint; aint ].
Definition args_A1____absorb_avx2 : seq var_i :=
  [:: st_18220.(gv)
    ; AT_18221.(gv)
    ; buf_18222.(gv)
    ; _TRAILB_18223.(gv)
    ; _RATE8_18224.(gv) ].
Definition tyout_A1____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1____absorb_avx2 : seq var_i :=
  [:: st_18220.(gv); AT_18221.(gv) ].

(* Body *)
Definition body_A1____absorb_avx2 : cmd :=
  [:: cassgn (Lvar offset_18225.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_18226.(gv)) (aint) (Pconst (1)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_18221) (Pvar _LEN_18226)) (Pvar _RATE8_18224))
        [:: ccall [:: Lvar st_18220.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_18225.(gv) ] A1____addstate_avx2 [:: Pvar st_18220
                                                                    ; Pvar AT_18221
                                                                    ; Pvar buf_18222
                                                                    ; Pvar offset_18225
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_18224) (Pvar AT_18221)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_18226.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_18226) (Papp2 (Osub (Op_int)) (Pvar _RATE8_18224) (Pvar AT_18221)))
          ; cassgn (Lvar AT_18221.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_18220.(gv) ] _keccakf1600_avx2 [:: Pvar st_18220 ]
          ; cassgn (Lvar ITERS_18227.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18226) (Pvar _RATE8_18224))
          ; cassgn (Lvar i_18228.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18228) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_18227)))
              [:: ccall [:: Lvar st_18220.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_18225.(gv) ] A1____addstate_avx2 [:: Pvar st_18220
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_18222
                                                                    ; Pvar offset_18225
                                                                    ; Pvar _RATE8_18224
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_18220.(gv) ] _keccakf1600_avx2 [:: Pvar st_18220 ]
                ; cassgn (Lvar i_18228.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18228) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_18226.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18226) (Pvar _RATE8_18224)) ]
        [::]
    ; ccall [:: Lvar st_18220.(gv)
              ; Lvar AT_18221.(gv)
              ; Lnone dummy_var_info (aword U64) ] A1____addstate_avx2 [:: Pvar st_18220
                                                                    ; Pvar AT_18221
                                                                    ; Pvar buf_18222
                                                                    ; Pvar offset_18225
                                                                    ; Pvar _LEN_18226
                                                                    ; Pvar _TRAILB_18223 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18223) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_18220.(gv) ] __addratebit_avx2 [:: Pvar st_18220
                                                               ; Pvar _RATE8_18224 ] ]
        [::] ].

Definition fd_A1____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____absorb_avx2;
    f_params := args_A1____absorb_avx2;
    f_body := body_A1____absorb_avx2;
    f_tyout := tyout_A1____absorb_avx2;
    f_res := res_A1____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
