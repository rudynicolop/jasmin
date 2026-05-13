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

(* A64____a_rlen_read_upto8 *)
(* Local variables *)
Definition a_16762 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16762).
Definition off_16763 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16763).
Definition len_16764 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16764).
Definition w_16765 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16765).
Definition zf_16766 : gvar := mk_rocq_gvar Slocal (abool) (mkident 16766).
Definition sh_16767 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 16767).
Definition x_16768 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16768).

(* Signature *)
Definition tyin_A64____a_rlen_read_upto8 : seq atype :=
  [:: aarr U8 64; aword U64; aword U64 ].
Definition args_A64____a_rlen_read_upto8 : seq var_i :=
  [:: a_16762.(gv); off_16763.(gv); len_16764.(gv) ].
Definition tyout_A64____a_rlen_read_upto8 : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A64____a_rlen_read_upto8 : seq var_i :=
  [:: off_16763.(gv); w_16765.(gv) ].

(* Body *)
Definition body_A64____a_rlen_read_upto8 : cmd :=
  [:: cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_16764) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_16765.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_16762 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_16763)))
          ; cassgn (Lvar off_16763.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_16763) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_16766.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_16764)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_16766))
              [:: cassgn (Lvar w_16765.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_16762 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_16763))))
                ; cassgn (Lvar off_16763.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_16763) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_16767.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_16765.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_16767.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_16766.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_16764)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_16766))
              [:: cassgn (Lvar x_16768.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_16762 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_16763))))
                ; cassgn (Lvar x_16768.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_16768) (Papp2 (Oland U8) (Pvar sh_16767) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_16765.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_16765) (Pvar x_16768))
                ; cassgn (Lvar off_16763.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_16763) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_16767.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_16767) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_16766.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_16764)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_16766))
              [:: cassgn (Lvar x_16768.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_16762 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_16763))))
                ; cassgn (Lvar x_16768.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_16768) (Papp2 (Oland U8) (Pvar sh_16767) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_16765.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_16765) (Pvar x_16768))
                ; cassgn (Lvar off_16763.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_16763) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ] ].

Definition fd_A64____a_rlen_read_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_rlen_read_upto8;
    f_params := args_A64____a_rlen_read_upto8;
    f_body := body_A64____a_rlen_read_upto8;
    f_tyout := tyout_A64____a_rlen_read_upto8;
    f_res := res_A64____a_rlen_read_upto8;
    f_extra := tt;
  |}.

End IDO.
