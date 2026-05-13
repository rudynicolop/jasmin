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

(* A33____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_17266 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17266).
Definition offset_17267 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17267).
Definition DELTA_17268 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17268).
Definition LEN_17269 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17269).
Definition TRAIL_17270 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17270).
Definition CUR_17271 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17271).
Definition AT_17272 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17272).
Definition w_17273 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17273).
Definition AT8_17274 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17274).
Definition t16_17275 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17275).
Definition t8_17276 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17276).

(* Signature *)
Definition tyin_A33____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aint; aint; aint ].
Definition args_A33____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_17266.(gv)
    ; offset_17267.(gv)
    ; DELTA_17268.(gv)
    ; LEN_17269.(gv)
    ; TRAIL_17270.(gv)
    ; CUR_17271.(gv)
    ; AT_17272.(gv) ].
Definition tyout_A33____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A33____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_17268.(gv)
    ; LEN_17269.(gv)
    ; TRAIL_17270.(gv)
    ; AT_17272.(gv)
    ; w_17273.(gv) ].

(* Body *)
Definition body_A33____a_ilen_read_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17272) (Pvar CUR_17271)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17271) (Pconst (8)%Z)) (Pvar AT_17272))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17269) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17270) (Pconst (0)%Z))))
        [:: cassgn (Lvar w_17273.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)) ]
        [:: cassgn (Lvar AT8_17274.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17272) (Pvar CUR_17271))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_17269))
              [:: cassgn (Lvar w_17273.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf_17266 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17267) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17268)))))
                ; ccall [:: Lvar w_17273.(gv) ] __SHLQ [:: Pvar w_17273
                                                         ; Pvar AT8_17274 ]
                ; cassgn (Lvar DELTA_17268.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17268) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17274)))
                ; cassgn (Lvar LEN_17269.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17269) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17274)))
                ; cassgn (Lvar AT8_17274.(gv)) (aint) (Pconst (8)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_17269))
                    [:: cassgn (Lvar w_17273.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_17266 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17267) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17268))))))
                      ; ccall [:: Lvar w_17273.(gv) ] __SHLQ [:: Pvar w_17273
                                                               ; Pvar AT8_17274 ]
                      ; cassgn (Lvar DELTA_17268.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17268) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_17274)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17274)) (Pconst (4)%Z)))
                      ; cassgn (Lvar LEN_17269.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17269) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_17274)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17274)) (Pconst (4)%Z)))
                      ; cassgn (Lvar AT8_17274.(gv)) (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_17274)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_17274))) ]
                    [:: cassgn (Lvar w_17273.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)) ]
                ; cif
                    (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_17274) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_17269)))
                    [:: cassgn (Lvar t16_17275.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_17266 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17267) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17268))))))
                      ; cassgn (Lvar DELTA_17268.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17268) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_17274)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17274)) (Pconst (2)%Z)))
                      ; cassgn (Lvar LEN_17269.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17269) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_17274)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17274)) (Pconst (2)%Z)))
                      ; ccall [:: Lvar t16_17275.(gv) ] __SHLQ [:: Pvar t16_17275
                                                                 ; Pvar AT8_17274 ]
                      ; cassgn (Lvar w_17273.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w_17273) (Pvar t16_17275))
                      ; cassgn (Lvar AT8_17274.(gv)) (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_17274)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_17274))) ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pvar AT8_17274) (Pconst (8)%Z))
                    [:: cif
                          (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_17269))
                          [:: cassgn (Lvar t8_17276.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_17266 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17267) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17268))))))
                            ; cassgn (Lvar t8_17276.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar t8_17276) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_17270) (Pconst (256)%Z)))))
                            ; cassgn (Lvar DELTA_17268.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17268) (Pconst (1)%Z))
                            ; cassgn (Lvar LEN_17269.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17269) (Pconst (1)%Z))
                            ; ccall [:: Lvar t8_17276.(gv) ] __SHLQ [:: Pvar t8_17276
                                                                    ; Pvar AT8_17274 ]
                            ; cassgn (Lvar w_17273.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w_17273) (Pvar t8_17276))
                            ; cassgn (Lvar AT8_17274.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_17274) (Pconst (1)%Z))
                            ; cif
                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_17274) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_17270) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                [:: cassgn (Lvar AT8_17274.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_17274) (Pconst (1)%Z))
                                  ; cassgn (Lvar TRAIL_17270.(gv)) (aint) (Pconst (0)%Z) ]
                                [::] ]
                          [:: cif
                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_17270) (Pconst (256)%Z)) (Pconst (0)%Z))
                                [:: cassgn (Lvar t8_17276.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_17270) (Pconst (256)%Z)))
                                  ; ccall [:: Lvar t8_17276.(gv) ] __SHLQ [:: Pvar t8_17276
                                                                    ; Pvar AT8_17274 ]
                                  ; cassgn (Lvar w_17273.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w_17273) (Pvar t8_17276))
                                  ; cassgn (Lvar TRAIL_17270.(gv)) (aint) (Pconst (0)%Z)
                                  ; cassgn (Lvar AT8_17274.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_17274) (Pconst (1)%Z)) ]
                                [::] ] ]
                    [::] ]
          ; cassgn (Lvar AT_17272.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17271) (Pvar AT8_17274)) ] ].

Definition fd_A33____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_read_upto8_at;
    f_params := args_A33____a_ilen_read_upto8_at;
    f_body := body_A33____a_ilen_read_upto8_at;
    f_tyout := tyout_A33____a_ilen_read_upto8_at;
    f_res := res_A33____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
