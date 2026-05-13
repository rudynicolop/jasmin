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

(* A2____absorb_avx2x4 *)
(* Local variables *)
Definition st_17721 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17721).
Definition AT_17722 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17722).
Definition buf0_17723 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17723).
Definition buf1_17724 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17724).
Definition buf2_17725 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17725).
Definition buf3_17726 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17726).
Definition _TRAILB_17727 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17727).
Definition _RATE8_17728 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17728).
Definition offset_17729 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17729).
Definition _LEN_17730 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17730).
Definition ITERS_17731 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17731).
Definition i_17732 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17732).

(* Signature *)
Definition tyin_A2____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 2
    ; aarr U8 2
    ; aarr U8 2
    ; aarr U8 2
    ; aint
    ; aint ].
Definition args_A2____absorb_avx2x4 : seq var_i :=
  [:: st_17721.(gv)
    ; AT_17722.(gv)
    ; buf0_17723.(gv)
    ; buf1_17724.(gv)
    ; buf2_17725.(gv)
    ; buf3_17726.(gv)
    ; _TRAILB_17727.(gv)
    ; _RATE8_17728.(gv) ].
Definition tyout_A2____absorb_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res_A2____absorb_avx2x4 : seq var_i :=
  [:: st_17721.(gv); AT_17722.(gv) ].

(* Body *)
Definition body_A2____absorb_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_17729.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_17730.(gv)) (aint) (Pconst (2)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_17722) (Pvar _LEN_17730)) (Pvar _RATE8_17728))
        [:: ccall [:: Lvar st_17721.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_17729.(gv) ] A2____addstate_avx2x4 [:: Pvar st_17721
                                                                    ; Pvar AT_17722
                                                                    ; Pvar buf0_17723
                                                                    ; Pvar buf1_17724
                                                                    ; Pvar buf2_17725
                                                                    ; Pvar buf3_17726
                                                                    ; Pvar offset_17729
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_17728) (Pvar AT_17722)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_17730.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_17730) (Papp2 (Osub (Op_int)) (Pvar _RATE8_17728) (Pvar AT_17722)))
          ; cassgn (Lvar AT_17722.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_17721.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17721 ]
          ; cassgn (Lvar ITERS_17731.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17730) (Pvar _RATE8_17728))
          ; cassgn (Lvar i_17732.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17732) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17731)))
              [:: ccall [:: Lvar st_17721.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_17729.(gv) ] A2____addstate_avx2x4 [:: Pvar st_17721
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_17723
                                                                    ; Pvar buf1_17724
                                                                    ; Pvar buf2_17725
                                                                    ; Pvar buf3_17726
                                                                    ; Pvar offset_17729
                                                                    ; Pvar _RATE8_17728
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_17721.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17721 ]
                ; cassgn (Lvar i_17732.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17732) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_17730.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17730) (Pvar _RATE8_17728)) ]
        [::]
    ; ccall [:: Lvar st_17721.(gv)
              ; Lvar AT_17722.(gv)
              ; Lnone dummy_var_info (aword U64) ] A2____addstate_avx2x4 [:: Pvar st_17721
                                                                    ; Pvar AT_17722
                                                                    ; Pvar buf0_17723
                                                                    ; Pvar buf1_17724
                                                                    ; Pvar buf2_17725
                                                                    ; Pvar buf3_17726
                                                                    ; Pvar offset_17729
                                                                    ; Pvar _LEN_17730
                                                                    ; Pvar _TRAILB_17727 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17727) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_17721.(gv) ] __addratebit_avx2x4 [:: Pvar st_17721
                                                                 ; Pvar _RATE8_17728 ] ]
        [::] ].

Definition fd_A2____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____absorb_avx2x4;
    f_params := args_A2____absorb_avx2x4;
    f_body := body_A2____absorb_avx2x4;
    f_tyout := tyout_A2____absorb_avx2x4;
    f_res := res_A2____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
