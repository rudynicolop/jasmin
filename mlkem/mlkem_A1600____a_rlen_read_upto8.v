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

(* A1600____a_rlen_read_upto8 *)
(* Local variables *)
Definition a_14987 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14987).
Definition off_14988 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14988).
Definition len_14989 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14989).
Definition w_14990 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14990).
Definition zf_14991 : gvar := mk_rocq_gvar Slocal (abool) (mkident 14991).
Definition sh_14992 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 14992).
Definition x_14993 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14993).

(* Signature *)
Definition tyin_A1600____a_rlen_read_upto8 : seq atype :=
  [:: aarr U8 1600; aword U64; aword U64 ].
Definition args_A1600____a_rlen_read_upto8 : seq var_i :=
  [:: a_14987.(gv); off_14988.(gv); len_14989.(gv) ].
Definition tyout_A1600____a_rlen_read_upto8 : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1600____a_rlen_read_upto8 : seq var_i :=
  [:: off_14988.(gv); w_14990.(gv) ].

(* Body *)
Definition body_A1600____a_rlen_read_upto8 : cmd :=
  [:: cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_14989) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_14990.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_14987 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14988)))
          ; cassgn (Lvar off_14988.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14988) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_14991.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14989)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_14991))
              [:: cassgn (Lvar w_14990.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_14987 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14988))))
                ; cassgn (Lvar off_14988.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14988) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_14992.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_14990.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_14992.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_14991.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14989)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_14991))
              [:: cassgn (Lvar x_14993.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_14987 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14988))))
                ; cassgn (Lvar x_14993.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_14993) (Papp2 (Oland U8) (Pvar sh_14992) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_14990.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_14990) (Pvar x_14993))
                ; cassgn (Lvar off_14988.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14988) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_14992.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_14992) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_14991.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14989)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_14991))
              [:: cassgn (Lvar x_14993.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_14987 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14988))))
                ; cassgn (Lvar x_14993.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_14993) (Papp2 (Oland U8) (Pvar sh_14992) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_14990.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_14990) (Pvar x_14993))
                ; cassgn (Lvar off_14988.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14988) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ] ].

Definition fd_A1600____a_rlen_read_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_rlen_read_upto8;
    f_params := args_A1600____a_rlen_read_upto8;
    f_body := body_A1600____a_rlen_read_upto8;
    f_tyout := tyout_A1600____a_rlen_read_upto8;
    f_res := res_A1600____a_rlen_read_upto8;
    f_extra := tt;
  |}.

End IDO.
