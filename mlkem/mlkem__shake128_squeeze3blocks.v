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

(* _shake128_squeeze3blocks *)
(* Local variables *)
Definition buf_166 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14310).
Definition st_126 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14311).
Definition offset_180 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14312).

(* Signature *)
Definition tyin__shake128_squeeze3blocks : seq atype :=
  [:: aarr U8 536; aarr U256 7 ].
Definition args__shake128_squeeze3blocks : seq var_i :=
  [:: buf_166.(gv); st_126.(gv) ].
Definition tyout__shake128_squeeze3blocks : seq atype := [:: aarr U8 536 ].
Definition res__shake128_squeeze3blocks : seq var_i := [:: buf_166.(gv) ].

(* Body *)
Definition body__shake128_squeeze3blocks : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Lvar st_126.(gv) ] _keccakf1600_avx2 [:: Pvar st_126 ])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_180.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_166.(gv)
                                    ; Lvar offset_180.(gv) ] ABUFLEN____dumpstate_avx2 [:: Pvar buf_166
                                                                    ; Pvar offset_180
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar st_126 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_126.(gv) ] _keccakf1600_avx2 [:: Pvar st_126 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_166.(gv)
                                    ; Lvar offset_180.(gv) ] ABUFLEN____dumpstate_avx2 [:: Pvar buf_166
                                                                    ; Pvar offset_180
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar st_126 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_126.(gv) ] _keccakf1600_avx2 [:: Pvar st_126 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf_166.(gv)
                                    ; Lvar offset_180.(gv) ] ABUFLEN____dumpstate_avx2 [:: Pvar buf_166
                                                                    ; Pvar offset_180
                                                                    ; Pconst (200)%Z
                                                                    ; Pvar st_126 ]) ].

Definition fd__shake128_squeeze3blocks : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake128_squeeze3blocks;
    f_params := args__shake128_squeeze3blocks;
    f_body := body__shake128_squeeze3blocks;
    f_tyout := tyout__shake128_squeeze3blocks;
    f_res := res__shake128_squeeze3blocks;
    f_extra := tt;
  |}.

End IDO.
