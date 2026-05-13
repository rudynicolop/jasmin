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

(* A33____a_rlen_read_upto8 *)
(* Local variables *)
Definition a_17144 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17144).
Definition off_17145 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17145).
Definition len_17146 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17146).
Definition w_17147 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17147).
Definition zf_17148 : gvar := mk_rocq_gvar Slocal (abool) (mkident 17148).
Definition sh_17149 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 17149).
Definition x_17150 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17150).

(* Signature *)
Definition tyin_A33____a_rlen_read_upto8 : seq atype :=
  [:: aarr U8 33; aword U64; aword U64 ].
Definition args_A33____a_rlen_read_upto8 : seq var_i :=
  [:: a_17144.(gv); off_17145.(gv); len_17146.(gv) ].
Definition tyout_A33____a_rlen_read_upto8 : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A33____a_rlen_read_upto8 : seq var_i :=
  [:: off_17145.(gv); w_17147.(gv) ].

(* Body *)
Definition body_A33____a_rlen_read_upto8 : cmd :=
  [:: cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_17146) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_17147.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_17144 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17145)))
          ; cassgn (Lvar off_17145.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17145) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_17148.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17146)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_17148))
              [:: cassgn (Lvar w_17147.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_17144 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17145))))
                ; cassgn (Lvar off_17145.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17145) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_17149.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_17147.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_17149.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_17148.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17146)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_17148))
              [:: cassgn (Lvar x_17150.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_17144 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17145))))
                ; cassgn (Lvar x_17150.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_17150) (Papp2 (Oland U8) (Pvar sh_17149) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_17147.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_17147) (Pvar x_17150))
                ; cassgn (Lvar off_17145.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17145) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_17149.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_17149) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_17148.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17146)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_17148))
              [:: cassgn (Lvar x_17150.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_17144 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17145))))
                ; cassgn (Lvar x_17150.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_17150) (Papp2 (Oland U8) (Pvar sh_17149) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_17147.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_17147) (Pvar x_17150))
                ; cassgn (Lvar off_17145.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17145) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ] ].

Definition fd_A33____a_rlen_read_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_rlen_read_upto8;
    f_params := args_A33____a_rlen_read_upto8;
    f_body := body_A33____a_rlen_read_upto8;
    f_tyout := tyout_A33____a_rlen_read_upto8;
    f_res := res_A33____a_rlen_read_upto8;
    f_extra := tt;
  |}.

End IDO.
