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

(* A1____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_18276 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18276).
Definition off_ : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18277).
Definition len_ : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18278).
Definition w_18279 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18279).
Definition off_18280 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18280).
Definition len_18281 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18281).
Definition zf_18282 : gvar := mk_rocq_gvar Slocal (abool) (mkident 18282).
Definition sh_18283 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 18283).
Definition x_18284 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18284).

(* Signature *)
Definition tyin_A1____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 1; aword U64; aword U64 ].
Definition args_A1____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_18276.(gv); off_.(gv); len_.(gv) ].
Definition tyout_A1____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off_.(gv); w_18279.(gv) ].

(* Body *)
Definition body_A1____a_rlen_read_upto8_noninline : cmd :=
  [:: cassgn (Lvar off_18280.(gv)) (aword U64) (Pvar off_)
    ; cassgn (Lvar len_18281.(gv)) (aword U64) (Pvar len_)
    ; cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_18281) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_18279.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_18276 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_18280)))
          ; cassgn (Lvar off_18280.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_18280) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_18282.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_18281)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_18282))
              [:: cassgn (Lvar w_18279.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_18276 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_18280))))
                ; cassgn (Lvar off_18280.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_18280) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_18283.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_18279.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_18283.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_18282.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_18281)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_18282))
              [:: cassgn (Lvar x_18284.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_18276 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_18280))))
                ; cassgn (Lvar x_18284.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_18284) (Papp2 (Oland U8) (Pvar sh_18283) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_18279.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_18279) (Pvar x_18284))
                ; cassgn (Lvar off_18280.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_18280) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_18283.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_18283) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_18282.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_18281)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_18282))
              [:: cassgn (Lvar x_18284.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_18276 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_18280))))
                ; cassgn (Lvar x_18284.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_18284) (Papp2 (Oland U8) (Pvar sh_18283) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_18279.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_18279) (Pvar x_18284))
                ; cassgn (Lvar off_18280.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_18280) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ]
    ; cassgn (Lvar off_.(gv)) (aword U64) (Pvar off_18280) ].

Definition fd_A1____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_rlen_read_upto8_noninline;
    f_params := args_A1____a_rlen_read_upto8_noninline;
    f_body := body_A1____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A1____a_rlen_read_upto8_noninline;
    f_res := res_A1____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
