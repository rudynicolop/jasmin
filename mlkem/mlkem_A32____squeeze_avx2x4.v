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

(* A32____squeeze_avx2x4 *)
(* Local variables *)
Definition st_17289 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17289).
Definition buf0_17290 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17290).
Definition buf1_17291 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17291).
Definition buf2_17292 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17292).
Definition buf3_17293 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17293).
Definition _RATE8_17294 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17294).
Definition offset_17295 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17295).
Definition _LEN_17296 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17296).
Definition ITERS_17297 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17297).
Definition LO_17298 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17298).
Definition i_17299 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17299).

(* Signature *)
Definition tyin_A32____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 32; aarr U8 32; aarr U8 32; aarr U8 32; aint ].
Definition args_A32____squeeze_avx2x4 : seq var_i :=
  [:: st_17289.(gv)
    ; buf0_17290.(gv)
    ; buf1_17291.(gv)
    ; buf2_17292.(gv)
    ; buf3_17293.(gv)
    ; _RATE8_17294.(gv) ].
Definition tyout_A32____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 32; aarr U8 32; aarr U8 32; aarr U8 32 ].
Definition res_A32____squeeze_avx2x4 : seq var_i :=
  [:: st_17289.(gv)
    ; buf0_17290.(gv)
    ; buf1_17291.(gv)
    ; buf2_17292.(gv)
    ; buf3_17293.(gv) ].

(* Body *)
Definition body_A32____squeeze_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_17295.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_17296.(gv)) (aint) (Pconst (32)%Z)
    ; cassgn (Lvar ITERS_17297.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17296) (Pvar _RATE8_17294))
    ; cassgn (Lvar LO_17298.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17296) (Pvar _RATE8_17294))
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_17297))
        [:: cassgn (Lvar i_17299.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17299) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17297)))
              [:: ccall [:: Lvar st_17289.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17289 ]
                ; ccall [:: Lvar buf0_17290.(gv)
                          ; Lvar buf1_17291.(gv)
                          ; Lvar buf2_17292.(gv)
                          ; Lvar buf3_17293.(gv)
                          ; Lvar offset_17295.(gv) ] A32____dumpstate_avx2x4 [:: Pvar buf0_17290
                                                                    ; Pvar buf1_17291
                                                                    ; Pvar buf2_17292
                                                                    ; Pvar buf3_17293
                                                                    ; Pvar offset_17295
                                                                    ; Pvar _RATE8_17294
                                                                    ; Pvar st_17289 ]
                ; cassgn (Lvar i_17299.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17299) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ] ]
        [::]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_17298))
        [:: ccall [:: Lvar st_17289.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17289 ]
          ; ccall [:: Lvar buf0_17290.(gv)
                    ; Lvar buf1_17291.(gv)
                    ; Lvar buf2_17292.(gv)
                    ; Lvar buf3_17293.(gv)
                    ; Lvar offset_17295.(gv) ] A32____dumpstate_avx2x4 [:: Pvar buf0_17290
                                                                    ; Pvar buf1_17291
                                                                    ; Pvar buf2_17292
                                                                    ; Pvar buf3_17293
                                                                    ; Pvar offset_17295
                                                                    ; Pvar LO_17298
                                                                    ; Pvar st_17289 ] ]
        [::] ].

Definition fd_A32____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____squeeze_avx2x4;
    f_params := args_A32____squeeze_avx2x4;
    f_body := body_A32____squeeze_avx2x4;
    f_tyout := tyout_A32____squeeze_avx2x4;
    f_res := res_A32____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
