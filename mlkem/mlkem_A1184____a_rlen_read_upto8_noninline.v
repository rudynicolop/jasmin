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

(* A1184____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_16119 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16119).
Definition off__16120 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16120).
Definition len__16121 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16121).
Definition w_16122 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16122).
Definition off_16123 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16123).
Definition len_16124 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16124).
Definition zf_16125 : gvar := mk_rocq_gvar Slocal (abool) (mkident 16125).
Definition sh_16126 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 16126).
Definition x_16127 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16127).

(* Signature *)
Definition tyin_A1184____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 1184; aword U64; aword U64 ].
Definition args_A1184____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_16119.(gv); off__16120.(gv); len__16121.(gv) ].
Definition tyout_A1184____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1184____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__16120.(gv); w_16122.(gv) ].

(* Body *)
Definition body_A1184____a_rlen_read_upto8_noninline : cmd :=
  [:: cassgn (Lvar off_16123.(gv)) (aword U64) (Pvar off__16120)
    ; cassgn (Lvar len_16124.(gv)) (aword U64) (Pvar len__16121)
    ; cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_16124) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_16122.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_16119 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_16123)))
          ; cassgn (Lvar off_16123.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_16123) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_16125.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_16124)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_16125))
              [:: cassgn (Lvar w_16122.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_16119 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_16123))))
                ; cassgn (Lvar off_16123.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_16123) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_16126.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_16122.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_16126.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_16125.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_16124)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_16125))
              [:: cassgn (Lvar x_16127.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_16119 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_16123))))
                ; cassgn (Lvar x_16127.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_16127) (Papp2 (Oland U8) (Pvar sh_16126) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_16122.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_16122) (Pvar x_16127))
                ; cassgn (Lvar off_16123.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_16123) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_16126.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_16126) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_16125.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_16124)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_16125))
              [:: cassgn (Lvar x_16127.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_16119 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_16123))))
                ; cassgn (Lvar x_16127.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_16127) (Papp2 (Oland U8) (Pvar sh_16126) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_16122.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_16122) (Pvar x_16127))
                ; cassgn (Lvar off_16123.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_16123) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ]
    ; cassgn (Lvar off__16120.(gv)) (aword U64) (Pvar off_16123) ].

Definition fd_A1184____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_rlen_read_upto8_noninline;
    f_params := args_A1184____a_rlen_read_upto8_noninline;
    f_body := body_A1184____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A1184____a_rlen_read_upto8_noninline;
    f_res := res_A1184____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
