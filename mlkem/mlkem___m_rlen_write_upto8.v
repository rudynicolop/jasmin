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

(* __m_rlen_write_upto8 *)
(* Local variables *)
Definition buf_18867 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18867).
Definition data : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18868).
Definition len_18869 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18869).
Definition zf_18870 : gvar := mk_rocq_gvar Slocal (abool) (mkident 18870).

(* Signature *)
Definition tyin___m_rlen_write_upto8 : seq atype :=
  [:: aword U64; aword U64; aword U64 ].
Definition args___m_rlen_write_upto8 : seq var_i :=
  [:: buf_18867.(gv); data.(gv); len_18869.(gv) ].
Definition tyout___m_rlen_write_upto8 : seq atype := [:: aword U64 ].
Definition res___m_rlen_write_upto8 : seq var_i := [:: buf_18867.(gv) ].

(* Body *)
Definition body___m_rlen_write_upto8 : cmd :=
  [:: cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_18869) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18867))) (aword U64) (Pvar data)
          ; cassgn (Lvar buf_18867.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18867) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_18870.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_18869)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_18870))
              [:: cassgn (Lmem Unaligned U32 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18867))) (aword U32) (Pvar data)
                ; cassgn (Lvar buf_18867.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18867) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar data.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar data) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_18870.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_18869)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_18870))
              [:: cassgn (Lmem Unaligned U16 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18867))) (aword U16) (Pvar data)
                ; cassgn (Lvar buf_18867.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18867) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar data.(gv)) (aword U64) (Papp2 (Olsr U64) (Pvar data) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_18870.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_18869)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_18870))
              [:: cassgn (Lmem Unaligned U8 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18867))) (aword U8) (Pvar data)
                ; cassgn (Lvar buf_18867.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18867) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ] ].

Definition fd___m_rlen_write_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_rlen_write_upto8;
    f_params := args___m_rlen_write_upto8;
    f_body := body___m_rlen_write_upto8;
    f_tyout := tyout___m_rlen_write_upto8;
    f_res := res___m_rlen_write_upto8;
    f_extra := tt;
  |}.

End IDO.
