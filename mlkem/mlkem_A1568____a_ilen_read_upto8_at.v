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

(* A1568____a_ilen_read_upto8_at *)
(* Local variables *)
Definition buf_15873 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15873).
Definition offset_15874 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15874).
Definition DELTA_15875 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15875).
Definition LEN_15876 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15876).
Definition TRAIL_15877 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15877).
Definition CUR_15878 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15878).
Definition AT_15879 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15879).
Definition w_15880 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15880).
Definition AT8_15881 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15881).
Definition t16_15882 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15882).
Definition t8_15883 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15883).

(* Signature *)
Definition tyin_A1568____a_ilen_read_upto8_at : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1568____a_ilen_read_upto8_at : seq var_i :=
  [:: buf_15873.(gv)
    ; offset_15874.(gv)
    ; DELTA_15875.(gv)
    ; LEN_15876.(gv)
    ; TRAIL_15877.(gv)
    ; CUR_15878.(gv)
    ; AT_15879.(gv) ].
Definition tyout_A1568____a_ilen_read_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U64 ].
Definition res_A1568____a_ilen_read_upto8_at : seq var_i :=
  [:: DELTA_15875.(gv)
    ; LEN_15876.(gv)
    ; TRAIL_15877.(gv)
    ; AT_15879.(gv)
    ; w_15880.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_read_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15879) (Pvar CUR_15878)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15878) (Pconst (8)%Z)) (Pvar AT_15879))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15876) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15877) (Pconst (0)%Z))))
        [:: cassgn (Lvar w_15880.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)) ]
        [:: cassgn (Lvar AT8_15881.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15879) (Pvar CUR_15878))
          ; cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_15876))
              [:: cassgn (Lvar w_15880.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf_15873 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15874) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15875)))))
                ; ccall [:: Lvar w_15880.(gv) ] __SHLQ [:: Pvar w_15880
                                                         ; Pvar AT8_15881 ]
                ; cassgn (Lvar DELTA_15875.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15875) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15881)))
                ; cassgn (Lvar LEN_15876.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15876) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15881)))
                ; cassgn (Lvar AT8_15881.(gv)) (aint) (Pconst (8)%Z) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (4)%Z) (Pvar LEN_15876))
                    [:: cassgn (Lvar w_15880.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 buf_15873 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15874) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15875))))))
                      ; ccall [:: Lvar w_15880.(gv) ] __SHLQ [:: Pvar w_15880
                                                               ; Pvar AT8_15881 ]
                      ; cassgn (Lvar DELTA_15875.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15875) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15881)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15881)) (Pconst (4)%Z)))
                      ; cassgn (Lvar LEN_15876.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15876) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15881)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15881)) (Pconst (4)%Z)))
                      ; cassgn (Lvar AT8_15881.(gv)) (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15881)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (4)%Z) (Pvar AT8_15881))) ]
                    [:: cassgn (Lvar w_15880.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z)) ]
                ; cif
                    (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_15881) (Pconst (8)%Z)) (Papp2 (Ole (Cmp_int)) (Pconst (2)%Z) (Pvar LEN_15876)))
                    [:: cassgn (Lvar t16_15882.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 buf_15873 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15874) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15875))))))
                      ; cassgn (Lvar DELTA_15875.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15875) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15881)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15881)) (Pconst (2)%Z)))
                      ; cassgn (Lvar LEN_15876.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15876) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15881)) (Pconst (8)%Z)) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15881)) (Pconst (2)%Z)))
                      ; ccall [:: Lvar t16_15882.(gv) ] __SHLQ [:: Pvar t16_15882
                                                                 ; Pvar AT8_15881 ]
                      ; cassgn (Lvar w_15880.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w_15880) (Pvar t16_15882))
                      ; cassgn (Lvar AT8_15881.(gv)) (aint) (Pif (aint) (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15881)) (Pconst (8)%Z)) (Pconst (8)%Z) (Papp2 (Oadd (Op_int)) (Pconst (2)%Z) (Pvar AT8_15881))) ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pvar AT8_15881) (Pconst (8)%Z))
                    [:: cif
                          (Papp2 (Ole (Cmp_int)) (Pconst (1)%Z) (Pvar LEN_15876))
                          [:: cassgn (Lvar t8_15883.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 buf_15873 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15874) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15875))))))
                            ; cassgn (Lvar t8_15883.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar t8_15883) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (256)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15877) (Pconst (256)%Z)))))
                            ; cassgn (Lvar DELTA_15875.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15875) (Pconst (1)%Z))
                            ; cassgn (Lvar LEN_15876.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15876) (Pconst (1)%Z))
                            ; ccall [:: Lvar t8_15883.(gv) ] __SHLQ [:: Pvar t8_15883
                                                                    ; Pvar AT8_15881 ]
                            ; cassgn (Lvar w_15880.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w_15880) (Pvar t8_15883))
                            ; cassgn (Lvar AT8_15881.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15881) (Pconst (1)%Z))
                            ; cif
                                (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT8_15881) (Pconst (8)%Z)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15877) (Pconst (256)%Z)) (Pconst (0)%Z)))
                                [:: cassgn (Lvar AT8_15881.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15881) (Pconst (1)%Z))
                                  ; cassgn (Lvar TRAIL_15877.(gv)) (aint) (Pconst (0)%Z) ]
                                [::] ]
                          [:: cif
                                (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15877) (Pconst (256)%Z)) (Pconst (0)%Z))
                                [:: cassgn (Lvar t8_15883.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omod Unsigned (Op_int)) (Pvar TRAIL_15877) (Pconst (256)%Z)))
                                  ; ccall [:: Lvar t8_15883.(gv) ] __SHLQ [:: Pvar t8_15883
                                                                    ; Pvar AT8_15881 ]
                                  ; cassgn (Lvar w_15880.(gv)) (aword U64) (Papp2 (Olor U64) (Pvar w_15880) (Pvar t8_15883))
                                  ; cassgn (Lvar TRAIL_15877.(gv)) (aint) (Pconst (0)%Z)
                                  ; cassgn (Lvar AT8_15881.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT8_15881) (Pconst (1)%Z)) ]
                                [::] ] ]
                    [::] ]
          ; cassgn (Lvar AT_15879.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15878) (Pvar AT8_15881)) ] ].

Definition fd_A1568____a_ilen_read_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_read_upto8_at;
    f_params := args_A1568____a_ilen_read_upto8_at;
    f_body := body_A1568____a_ilen_read_upto8_at;
    f_tyout := tyout_A1568____a_ilen_read_upto8_at;
    f_res := res_A1568____a_ilen_read_upto8_at;
    f_extra := tt;
  |}.

End IDO.
