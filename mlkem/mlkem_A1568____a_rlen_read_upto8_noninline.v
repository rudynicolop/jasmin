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

(* A1568____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_15737 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15737).
Definition off__15738 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15738).
Definition len__15739 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15739).
Definition w_15740 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15740).
Definition off_15741 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15741).
Definition len_15742 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15742).
Definition zf_15743 : gvar := mk_rocq_gvar Slocal (abool) (mkident 15743).
Definition sh_15744 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 15744).
Definition x_15745 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15745).

(* Signature *)
Definition tyin_A1568____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 1568; aword U64; aword U64 ].
Definition args_A1568____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_15737.(gv); off__15738.(gv); len__15739.(gv) ].
Definition tyout_A1568____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1568____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__15738.(gv); w_15740.(gv) ].

(* Body *)
Definition body_A1568____a_rlen_read_upto8_noninline : cmd :=
  [:: cassgn (Lvar off_15741.(gv)) (aword U64) (Pvar off__15738)
    ; cassgn (Lvar len_15742.(gv)) (aword U64) (Pvar len__15739)
    ; cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_15742) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_15740.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_15737 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15741)))
          ; cassgn (Lvar off_15741.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15741) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_15743.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15742)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_15743))
              [:: cassgn (Lvar w_15740.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_15737 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15741))))
                ; cassgn (Lvar off_15741.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15741) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_15744.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_15740.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_15744.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_15743.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15742)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_15743))
              [:: cassgn (Lvar x_15745.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_15737 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15741))))
                ; cassgn (Lvar x_15745.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_15745) (Papp2 (Oland U8) (Pvar sh_15744) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_15740.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_15740) (Pvar x_15745))
                ; cassgn (Lvar off_15741.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15741) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_15744.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_15744) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_15743.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15742)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_15743))
              [:: cassgn (Lvar x_15745.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_15737 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15741))))
                ; cassgn (Lvar x_15745.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_15745) (Papp2 (Oland U8) (Pvar sh_15744) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_15740.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_15740) (Pvar x_15745))
                ; cassgn (Lvar off_15741.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15741) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ]
    ; cassgn (Lvar off__15738.(gv)) (aword U64) (Pvar off_15741) ].

Definition fd_A1568____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_rlen_read_upto8_noninline;
    f_params := args_A1568____a_rlen_read_upto8_noninline;
    f_body := body_A1568____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A1568____a_rlen_read_upto8_noninline;
    f_res := res_A1568____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
