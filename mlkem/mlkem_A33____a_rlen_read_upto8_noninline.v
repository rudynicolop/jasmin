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

(* A33____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_17130 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17130).
Definition off__17131 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17131).
Definition len__17132 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17132).
Definition w_17133 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17133).
Definition off_17134 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17134).
Definition len_17135 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17135).
Definition zf_17136 : gvar := mk_rocq_gvar Slocal (abool) (mkident 17136).
Definition sh_17137 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 17137).
Definition x_17138 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17138).

(* Signature *)
Definition tyin_A33____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 33; aword U64; aword U64 ].
Definition args_A33____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_17130.(gv); off__17131.(gv); len__17132.(gv) ].
Definition tyout_A33____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A33____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__17131.(gv); w_17133.(gv) ].

(* Body *)
Definition body_A33____a_rlen_read_upto8_noninline : cmd :=
  [:: cassgn (Lvar off_17134.(gv)) (aword U64) (Pvar off__17131)
    ; cassgn (Lvar len_17135.(gv)) (aword U64) (Pvar len__17132)
    ; cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_17135) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_17133.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_17130 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17134)))
          ; cassgn (Lvar off_17134.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17134) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_17136.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17135)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_17136))
              [:: cassgn (Lvar w_17133.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_17130 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17134))))
                ; cassgn (Lvar off_17134.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17134) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_17137.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_17133.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_17137.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_17136.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17135)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_17136))
              [:: cassgn (Lvar x_17138.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_17130 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17134))))
                ; cassgn (Lvar x_17138.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_17138) (Papp2 (Oland U8) (Pvar sh_17137) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_17133.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_17133) (Pvar x_17138))
                ; cassgn (Lvar off_17134.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17134) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_17137.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_17137) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_17136.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17135)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_17136))
              [:: cassgn (Lvar x_17138.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_17130 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17134))))
                ; cassgn (Lvar x_17138.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_17138) (Papp2 (Oland U8) (Pvar sh_17137) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_17133.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_17133) (Pvar x_17138))
                ; cassgn (Lvar off_17134.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17134) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ]
    ; cassgn (Lvar off__17131.(gv)) (aword U64) (Pvar off_17134) ].

Definition fd_A33____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_rlen_read_upto8_noninline;
    f_params := args_A33____a_rlen_read_upto8_noninline;
    f_body := body_A33____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A33____a_rlen_read_upto8_noninline;
    f_res := res_A33____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
