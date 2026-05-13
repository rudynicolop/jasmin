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

(* A32____a_rlen_read_upto8_noninline *)
(* Local variables *)
Definition a_17512 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17512).
Definition off__17513 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17513).
Definition len__17514 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17514).
Definition w_17515 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17515).
Definition off_17516 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17516).
Definition len_17517 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17517).
Definition zf_17518 : gvar := mk_rocq_gvar Slocal (abool) (mkident 17518).
Definition sh_17519 : gvar := mk_rocq_gvar Slocal (aword U8) (mkident 17519).
Definition x_17520 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17520).

(* Signature *)
Definition tyin_A32____a_rlen_read_upto8_noninline : seq atype :=
  [:: aarr U8 32; aword U64; aword U64 ].
Definition args_A32____a_rlen_read_upto8_noninline : seq var_i :=
  [:: a_17512.(gv); off__17513.(gv); len__17514.(gv) ].
Definition tyout_A32____a_rlen_read_upto8_noninline : seq atype :=
  [:: aword U64; aword U64 ].
Definition res_A32____a_rlen_read_upto8_noninline : seq var_i :=
  [:: off__17513.(gv); w_17515.(gv) ].

(* Body *)
Definition body_A32____a_rlen_read_upto8_noninline : cmd :=
  [:: cassgn (Lvar off_17516.(gv)) (aword U64) (Pvar off__17513)
    ; cassgn (Lvar len_17517.(gv)) (aword U64) (Pvar len__17514)
    ; cif
        (Papp2 (Owi2 Unsigned U64 WIge) (Pvar len_17517) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
        [:: cassgn (Lvar w_17515.(gv)) (aword U64) (Pget Unaligned AAdirect U64 a_17512 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17516)))
          ; cassgn (Lvar off_17516.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17516) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
        [:: copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_17518.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17517)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (4)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_17518))
              [:: cassgn (Lvar w_17515.(gv)) (aword U64) (Papp1 (Ozeroext U64 U32) (Pget Unaligned AAdirect U32 a_17512 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17516))))
                ; cassgn (Lvar off_17516.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17516) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))
                ; cassgn (Lvar sh_17519.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar w_17515.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Pconst (0)%Z))
                ; cassgn (Lvar sh_17519.(gv)) (aword U8) (Papp1 (Oword_of_int U8) (Pconst (0)%Z)) ]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_17518.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17517)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (2)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_17518))
              [:: cassgn (Lvar x_17520.(gv)) (aword U64) (Papp1 (Ozeroext U64 U16) (Pget Unaligned AAdirect U16 a_17512 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17516))))
                ; cassgn (Lvar x_17520.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_17520) (Papp2 (Oland U8) (Pvar sh_17519) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_17515.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_17515) (Pvar x_17520))
                ; cassgn (Lvar off_17516.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17516) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))
                ; cassgn (Lvar sh_17519.(gv)) (aword U8) (Papp2 (Oadd (Op_w U8)) (Pvar sh_17519) (Papp1 (Oword_of_int U8) (Pconst (16)%Z))) ]
              [::]
          ; copn [:: Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lnone dummy_var_info (abool)
                   ; Lvar zf_17518.(gv) ] (Oasm ((BaseOp ((None), (TEST U64))))) [:: Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar len_17517)
                                                                    ; Papp1 (Oword_of_int U64) (Pconst (1)%Z) ]
          ; cif
              (Papp1 (Onot) (Pvar zf_17518))
              [:: cassgn (Lvar x_17520.(gv)) (aword U64) (Papp1 (Ozeroext U64 U8) (Pget Unaligned AAdirect U8 a_17512 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar off_17516))))
                ; cassgn (Lvar x_17520.(gv)) (aword U64) (Papp2 (Olsl (Op_w U64)) (Pvar x_17520) (Papp2 (Oland U8) (Pvar sh_17519) (Papp1 (Oword_of_int U8) (Pconst (63)%Z))))
                ; cassgn (Lvar w_17515.(gv)) (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar w_17515) (Pvar x_17520))
                ; cassgn (Lvar off_17516.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar off_17516) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
              [::] ]
    ; cassgn (Lvar off__17513.(gv)) (aword U64) (Pvar off_17516) ].

Definition fd_A32____a_rlen_read_upto8_noninline : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_rlen_read_upto8_noninline;
    f_params := args_A32____a_rlen_read_upto8_noninline;
    f_body := body_A32____a_rlen_read_upto8_noninline;
    f_tyout := tyout_A32____a_rlen_read_upto8_noninline;
    f_res := res_A32____a_rlen_read_upto8_noninline;
    f_extra := tt;
  |}.

End IDO.
