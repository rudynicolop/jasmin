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

(* __m_rlen_read_upto8 *)
(* Local variables *)
Definition buf_18875 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18875).
Definition len : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18876).
Definition w_18877 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18877).
Definition zf : gvar := mk_rocq_gvar Slocal (abool) (mkident 18878).
Definition sh : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 18879).
Definition x_18880 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18880).

(* Signature *)
Definition tyin___m_rlen_read_upto8 : seq atype := [:: aword U64; aword U64 ].
Definition args___m_rlen_read_upto8 : seq var_i :=
  [:: buf_18875.(gv); len.(gv) ].
Definition tyout___m_rlen_read_upto8 : seq atype :=
  [:: aword U64; aword U64 ].
Definition res___m_rlen_read_upto8 : seq var_i :=
  [:: buf_18875.(gv); w_18877.(gv) ].

(* Body *)
Definition body___m_rlen_read_upto8 : cmd :=
  [:: cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_18877.(gv)) (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18875)))
          ; cassgn (Lvar buf_18875.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18875) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf))
              [:: cassgn (Lvar w_18877.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pload Unaligned U32 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18875))))
                ; cassgn (Lvar buf_18875.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18875) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_18877.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf))
              [:: cassgn (Lvar x_18880.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pload Unaligned U16 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18875))))
                ; cassgn (Lvar x_18880.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_18880) (Papp2 (Oland U8) (Pvar sh) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_18877.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_18877) (Pvar x_18880))
                ; cassgn (Lvar buf_18875.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18875) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf))
              [:: cassgn (Lvar x_18880.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pload Unaligned U8 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18875))))
                ; cassgn (Lvar x_18880.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_18880) (Papp2 (Oland U8) (Pvar sh) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_18877.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_18877) (Pvar x_18880))
                ; cassgn (Lvar buf_18875.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18875) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ] ].

Definition fd___m_rlen_read_upto8 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___m_rlen_read_upto8;
    f_params := args___m_rlen_read_upto8;
    f_body := body___m_rlen_read_upto8;
    f_tyout := tyout___m_rlen_read_upto8;
    f_res := res___m_rlen_read_upto8;
    f_extra := tt;
  |}.

End IDO.
