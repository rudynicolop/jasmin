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

(* A1568____a_rlen_write_upto8 *)
(* Local variables *)
Definition buf_15726 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15726).
Definition off_15727 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15727).
Definition data_15728 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15728).
Definition len_15729 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15729).
Definition zf_15730 : gvar := mk_rocq_gvar Slocal (abool) (mkident 15730).

(* Signature *)
Definition tyin_A1568____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 1568; aword U64; aword U64; aword U64 ].
Definition args_A1568____a_rlen_write_upto8 : seq var_i :=
  [:: buf_15726.(gv); off_15727.(gv); data_15728.(gv); len_15729.(gv) ].
Definition tyout_A1568____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 1568; aword U64 ].
Definition res_A1568____a_rlen_write_upto8 : seq var_i :=
  [:: buf_15726.(gv); off_15727.(gv) ].

(* Body *)
Definition body_A1568____a_rlen_write_upto8 : cmd :=
  [:: cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_15729) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Laset Unaligned AAdirect U64 buf_15726.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15727))) (aword U64) (Pvar data_15728)
          ; cassgn (Lvar off_15727.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15727) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_15730.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15729)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_15730))
              [:: cassgn (Laset Unaligned AAdirect U32 buf_15726.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15727))) (aword U32) (Pvar data_15728)
                ; cassgn (Lvar off_15727.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15727) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar data_15728.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar data_15728) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_15730.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15729)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_15730))
              [:: cassgn (Laset Unaligned AAdirect U16 buf_15726.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15727))) (aword U16) (Pvar data_15728)
                ; cassgn (Lvar off_15727.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15727) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar data_15728.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar data_15728) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_15730.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_15729)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_15730))
              [:: cassgn (Laset Unaligned AAdirect U8 buf_15726.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_15727))) (aword U8) (Pvar data_15728)
                ; cassgn (Lvar off_15727.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_15727) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ] ].

Definition fd_A1568____a_rlen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_rlen_write_upto8;
    f_params := args_A1568____a_rlen_write_upto8;
    f_body := body_A1568____a_rlen_write_upto8;
    f_tyout := tyout_A1568____a_rlen_write_upto8;
    f_res := res_A1568____a_rlen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
