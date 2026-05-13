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

(* A1600____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_14973 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14973).
Definition off__14974 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14974).
Definition len__14975 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14975).
Definition w_14976 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14976).
Definition off_14977 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14977).
Definition len_14978 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14978).
Definition zf_14979 : gvar := mk_rocq_gvar Slocal (abool) (mkident 14979).
Definition sh_14980 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 14980).
Definition x_14981 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14981).

(* Signature *)
Definition tyin_A1600____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 1600; aword U64; aword U64 ].
Definition args_A1600____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_14973.(gv); off__14974.(gv); len__14975.(gv) ].
Definition tyout_A1600____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1600____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__14974.(gv); w_14976.(gv) ].

(* Body *)
Definition body_A1600____a_rlen_read_upto8_noninline : cmd :=
  [:: cassgn (Lvar off_14977.(gv)) (aword U64) (Pvar off__14974)
    ; cassgn (Lvar len_14978.(gv)) (aword U64) (Pvar len__14975)
    ; cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_14978) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_14976.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_14973 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14977)))
          ; cassgn (Lvar off_14977.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14977) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_14979.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14978)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_14979))
              [:: cassgn (Lvar w_14976.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_14973 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14977))))
                ; cassgn (Lvar off_14977.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14977) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_14980.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_14976.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_14980.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_14979.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14978)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_14979))
              [:: cassgn (Lvar x_14981.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_14973 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14977))))
                ; cassgn (Lvar x_14981.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_14981) (Papp2 (Oland U8) (Pvar sh_14980) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_14976.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_14976) (Pvar x_14981))
                ; cassgn (Lvar off_14977.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14977) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_14980.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_14980) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_14979.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14978)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_14979))
              [:: cassgn (Lvar x_14981.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_14973 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14977))))
                ; cassgn (Lvar x_14981.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_14981) (Papp2 (Oland U8) (Pvar sh_14980) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_14976.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_14976) (Pvar x_14981))
                ; cassgn (Lvar off_14977.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14977) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ]
    ; cassgn (Lvar off__14974.(gv)) (aword U64) (Pvar off_14977) ].

Definition fd_A1600____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_rlen_read_upto8_noninline;
    f_params := args_A1600____a_rlen_read_upto8_noninline;
    f_body := body_A1600____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A1600____a_rlen_read_upto8_noninline;
    f_res := res_A1600____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
