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

(* A1120____a_rlen_read_upto8 *)
(* Local variables *)
Definition a_15369 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15369).
Definition off_15370 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15370).
Definition len_15371 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15371).
Definition w_15372 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15372).
Definition zf_15373 : gvar := mk_rocq_gvar Slocal (abool) (mkident 15373).
Definition sh_15374 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 15374).
Definition x_15375 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15375).

(* Signature *)
Definition tyin_A1120____a_rlen_read_upto8 : seq atype :=
  [:: aarr U8 1120; aword U64; aword U64 ].
Definition args_A1120____a_rlen_read_upto8 : seq var_i :=
  [:: a_15369.(gv); off_15370.(gv); len_15371.(gv) ].
Definition tyout_A1120____a_rlen_read_upto8 : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A1120____a_rlen_read_upto8 : seq var_i :=
  [:: off_15370.(gv); w_15372.(gv) ].

(* Body *)
Definition body_A1120____a_rlen_read_upto8 : cmd :=
  [:: cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_15371) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_15372.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_15369 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15370)))
          ; cassgn (Lvar off_15370.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15370) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_15373.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15371)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_15373))
              [:: cassgn (Lvar w_15372.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_15369 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15370))))
                ; cassgn (Lvar off_15370.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15370) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_15374.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_15372.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_15374.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_15373.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15371)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_15373))
              [:: cassgn (Lvar x_15375.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_15369 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15370))))
                ; cassgn (Lvar x_15375.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_15375) (Papp2 (Oland U8) (Pvar sh_15374) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_15372.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_15372) (Pvar x_15375))
                ; cassgn (Lvar off_15370.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15370) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_15374.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_15374) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_15373.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15371)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_15373))
              [:: cassgn (Lvar x_15375.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_15369 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15370))))
                ; cassgn (Lvar x_15375.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_15375) (Papp2 (Oland U8) (Pvar sh_15374) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_15372.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_15372) (Pvar x_15375))
                ; cassgn (Lvar off_15370.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15370) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ] ].

Definition fd_A1120____a_rlen_read_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____a_rlen_read_upto8;
    f_params := args_A1120____a_rlen_read_upto8;
    f_body := body_A1120____a_rlen_read_upto8;
    f_tyout := tyout_A1120____a_rlen_read_upto8;
    f_res := res_A1120____a_rlen_read_upto8;
    f_extra := tt;
  |}.

End IDO.
