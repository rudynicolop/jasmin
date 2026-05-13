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

(* ABUFLEN____a_rlen_write_upto8 *)
(* Local variables *)
Definition buf_14580 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14580).
Definition off_14581 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14581).
Definition data_14582 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14582).
Definition len_14583 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14583).
Definition zf_14584 : gvar := mk_rocq_gvar Slocal (abool) (mkident 14584).

(* Signature *)
Definition tyin_ABUFLEN____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 536; aword U64; aword U64; aword U64 ].
Definition args_ABUFLEN____a_rlen_write_upto8 : seq var_i :=
  [:: buf_14580.(gv); off_14581.(gv); data_14582.(gv); len_14583.(gv) ].
Definition tyout_ABUFLEN____a_rlen_write_upto8 : seq atype :=
  [:: aarr U8 536; aword U64 ].
Definition res_ABUFLEN____a_rlen_write_upto8 : seq var_i :=
  [:: buf_14580.(gv); off_14581.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_rlen_write_upto8 : cmd :=
  [:: cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_14583) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Laset Unaligned AAdirect U64 buf_14580.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14581))) (aword U64) (Pvar data_14582)
          ; cassgn (Lvar off_14581.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14581) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_14584.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14583)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_14584))
              [:: cassgn (Laset Unaligned AAdirect U32 buf_14580.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14581))) (aword U32) (Pvar data_14582)
                ; cassgn (Lvar off_14581.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14581) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar data_14582.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar data_14582) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_14584.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14583)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_14584))
              [:: cassgn (Laset Unaligned AAdirect U16 buf_14580.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14581))) (aword U16) (Pvar data_14582)
                ; cassgn (Lvar off_14581.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14581) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar data_14582.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar data_14582) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_14584.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_14583)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_14584))
              [:: cassgn (Laset Unaligned AAdirect U8 buf_14580.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_14581))) (aword U8) (Pvar data_14582)
                ; cassgn (Lvar off_14581.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_14581) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ] ].

Definition fd_ABUFLEN____a_rlen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_rlen_write_upto8;
    f_params := args_ABUFLEN____a_rlen_write_upto8;
    f_body := body_ABUFLEN____a_rlen_write_upto8;
    f_tyout := tyout_ABUFLEN____a_rlen_write_upto8;
    f_res := res_ABUFLEN____a_rlen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
