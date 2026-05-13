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

(* A64____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_16884 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 16884).
Definition offset_16885 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16885).
Definition DELTA_16886 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16886).
Definition LEN_16887 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16887).
Definition TRAIL_16888 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16888).
Definition CUR_16889 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16889).
Definition AT_16890 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16890).
Definition w_16891 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16891).
Definition AT8_16892 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16892).
Definition t16_16893 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16893).
Definition t8_16894 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16894).

(* Signature *)
Definition tyin_A64____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aint; aint; aint ].
Definition args_A64____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_16884.(gv)
    ; offset_16885.(gv)
    ; DELTA_16886.(gv)
    ; LEN_16887.(gv)
    ; TRAIL_16888.(gv)
    ; CUR_16889.(gv)
    ; AT_16890.(gv) ].
Definition tyout_A64____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A64____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_16886.(gv)
    ; LEN_16887.(gv)
    ; TRAIL_16888.(gv)
    ; AT_16890.(gv)
    ; w_16891.(gv) ].

(* Body *)
Definition body_A64____a_ilen_read_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_16890) (Pvar CUR_16889)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_16889) (Pconst (8)%Z)) (Pvar AT_16890))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16887) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_16888) (Pconst (0)%Z))))
        [:: cassgn (Lvar w_16891.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)) ]
        [:: cassgn (Lvar AT8_16892.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_16890) (Pvar CUR_16889))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_16887))
              [:: cassgn (Lvar w_16891.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf_16884 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16885) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16886)))))
                ; ccall [:: Lvar w_16891.(gv) ] __SHLQ [:: Pvar w_16891
                                                         ; Pvar AT8_16892 ]
                ; cassgn (Lvar DELTA_16886.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16886) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16892)))
                ; cassgn (Lvar LEN_16887.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16887) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16892)))
                ; cassgn (Lvar AT8_16892.(gv)) (aint) (Pconst (8)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_16887))
                    [:: cassgn (Lvar w_16891.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_16884 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16885) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16886))))))
                      ; ccall [:: Lvar w_16891.(gv) ] __SHLQ [:: Pvar w_16891
                                                               ; Pvar AT8_16892 ]
                      ; cassgn (Lvar DELTA_16886.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16886) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_16892)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16892)) (Pconst (4)%Z)))
                      ; cassgn (Lvar LEN_16887.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16887) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_16892)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16892)) (Pconst (4)%Z)))
                      ; cassgn (Lvar AT8_16892.(gv)) (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_16892)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_16892))) ]
                    [:: cassgn (Lvar w_16891.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)) ]
                ; cif
                    (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_16892) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_16887)))
                    [:: cassgn (Lvar t16_16893.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_16884 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16885) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16886))))))
                      ; cassgn (Lvar DELTA_16886.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16886) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_16892)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16892)) (Pconst (2)%Z)))
                      ; cassgn (Lvar LEN_16887.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16887) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_16892)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_16892)) (Pconst (2)%Z)))
                      ; ccall [:: Lvar t16_16893.(gv) ] __SHLQ [:: Pvar t16_16893
                                                                 ; Pvar AT8_16892 ]
                      ; cassgn (Lvar w_16891.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w_16891) (Pvar t16_16893))
                      ; cassgn (Lvar AT8_16892.(gv)) (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_16892)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_16892))) ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pvar AT8_16892) (Pconst (8)%Z))
                    [:: cif
                          (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_16887))
                          [:: cassgn (Lvar t8_16894.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_16884 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16885) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16886))))))
                            ; cassgn (Lvar t8_16894.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar t8_16894) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_16888) (Pconst (256)%Z)))))
                            ; cassgn (Lvar DELTA_16886.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16886) (Pconst (1)%Z))
                            ; cassgn (Lvar LEN_16887.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16887) (Pconst (1)%Z))
                            ; ccall [:: Lvar t8_16894.(gv) ] __SHLQ [:: Pvar t8_16894
                                                                    ; Pvar AT8_16892 ]
                            ; cassgn (Lvar w_16891.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w_16891) (Pvar t8_16894))
                            ; cassgn (Lvar AT8_16892.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_16892) (Pconst (1)%Z))
                            ; cif
                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_16892) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_16888) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                [:: cassgn (Lvar AT8_16892.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_16892) (Pconst (1)%Z))
                                  ; cassgn (Lvar TRAIL_16888.(gv)) (aint) (Pconst (0)%Z) ]
                                [::] ]
                          [:: cif
                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_16888) (Pconst (256)%Z)) (Pconst (0)%Z))
                                [:: cassgn (Lvar t8_16894.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_16888) (Pconst (256)%Z)))
                                  ; ccall [:: Lvar t8_16894.(gv) ] __SHLQ [:: Pvar t8_16894
                                                                    ; Pvar AT8_16892 ]
                                  ; cassgn (Lvar w_16891.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w_16891) (Pvar t8_16894))
                                  ; cassgn (Lvar TRAIL_16888.(gv)) (aint) (Pconst (0)%Z)
                                  ; cassgn (Lvar AT8_16892.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_16892) (Pconst (1)%Z)) ]
                                [::] ] ]
                    [::] ]
          ; cassgn (Lvar AT_16890.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_16889) (Pvar AT8_16892)) ] ].

Definition fd_A64____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_ilen_read_upto8_at;
    f_params := args_A64____a_ilen_read_upto8_at;
    f_body := body_A64____a_ilen_read_upto8_at;
    f_tyout := tyout_A64____a_ilen_read_upto8_at;
    f_res := res_A64____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
