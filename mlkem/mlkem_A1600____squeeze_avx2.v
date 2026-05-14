From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A1600____squeeze_avx2 *)
(* Local variables *)
Definition st_14885 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 14885).
Definition buf_14886 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14886).
Definition _RATE8_14887 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14887).
Definition offset_14888 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14888).
Definition _LEN_14889 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14889).
Definition ITERS_14890 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14890).
Definition LO_14891 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14891).
Definition i_14892 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14892).

(* Signature *)
Definition tyin_A1600____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1600; aint ].
Definition args_A1600____squeeze_avx2 : seq var_i :=
  [:: st_14885.(gv); buf_14886.(gv); _RATE8_14887.(gv) ].
Definition tyout_A1600____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1600 ].
Definition res_A1600____squeeze_avx2 : seq var_i :=
  [:: st_14885.(gv); buf_14886.(gv) ].

(* Body *)
Definition body_A1600____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_14888.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14889.(gv)) AT_none (aint) (Pconst (1600)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_14890.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14889) (Pvar _RATE8_14887)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_14891.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14889) (Pvar _RATE8_14887)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_14892.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14892) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14890)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14885.(gv) ] _keccakf1600_avx2 [:: Pvar st_14885 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_14886.(gv)
                                                                ; Lvar offset_14888.(gv) ] A1600____dumpstate_avx2 [:: Pvar buf_14886
                                                                    ; Pvar offset_14888
                                                                    ; Pvar _RATE8_14887
                                                                    ; Pvar st_14885 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_14892.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14892) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_14891))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14885.(gv) ] _keccakf1600_avx2 [:: Pvar st_14885 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_14886.(gv)
                                                                ; Lvar offset_14888.(gv) ] A1600____dumpstate_avx2 [:: Pvar buf_14886
                                                                    ; Pvar offset_14888
                                                                    ; Pvar LO_14891
                                                                    ; Pvar st_14885 ]) ]
                              [::]) ].

Definition fd_A1600____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____squeeze_avx2;
    f_params := args_A1600____squeeze_avx2;
    f_body := body_A1600____squeeze_avx2;
    f_tyout := tyout_A1600____squeeze_avx2;
    f_res := res_A1600____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
