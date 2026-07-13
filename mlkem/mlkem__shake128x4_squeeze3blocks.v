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

(* _shake128x4_squeeze3blocks *)
(* Local variables *)
Definition st_127 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14295).
Definition buf_168 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2144) (mkident 14296).
Definition buf0_43 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14297).
Definition buf1_43 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14298).
Definition buf2_43 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14299).
Definition buf3_43 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14300).
Definition offset_181 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14301).

(* Signature *)
Definition tyin__shake128x4_squeeze3blocks : seq atype :=
  [:: aarr U256 25; aarr U8 2144 ].
Definition args__shake128x4_squeeze3blocks : seq var_i :=
  [:: st_127.(gv); buf_168.(gv) ].
Definition tyout__shake128x4_squeeze3blocks : seq atype :=
  [:: aarr U256 25; aarr U8 2144 ].
Definition res__shake128x4_squeeze3blocks : seq var_i :=
  [:: st_127.(gv); buf_168.(gv) ].

(* Body *)
Definition body__shake128x4_squeeze3blocks : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar buf0_43.(gv)) AT_none (aarr U8 536) (Psub AAscale U8 536 buf_168 (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (536)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar buf1_43.(gv)) AT_none (aarr U8 536) (Psub AAscale U8 536 buf_168 (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (536)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar buf2_43.(gv)) AT_none (aarr U8 536) (Psub AAscale U8 536 buf_168 (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (536)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar buf3_43.(gv)) AT_none (aarr U8 536) (Psub AAscale U8 536 buf_168 (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (536)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar offset_181.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lvar st_127.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_127 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf0_43.(gv)
                                    ; Lvar buf1_43.(gv)
                                    ; Lvar buf2_43.(gv)
                                    ; Lvar buf3_43.(gv)
                                    ; Lvar offset_181.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_43
                                                                    ; Pvar buf1_43
                                                                    ; Pvar buf2_43
                                                                    ; Pvar buf3_43
                                                                    ; Pvar offset_181
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar st_127 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_127.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_127 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf0_43.(gv)
                                    ; Lvar buf1_43.(gv)
                                    ; Lvar buf2_43.(gv)
                                    ; Lvar buf3_43.(gv)
                                    ; Lvar offset_181.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_43
                                                                    ; Pvar buf1_43
                                                                    ; Pvar buf2_43
                                                                    ; Pvar buf3_43
                                                                    ; Pvar offset_181
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar st_127 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_127.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_127 ])
    ; MkI dummy_instr_info (Ccall [:: Lvar buf0_43.(gv)
                                    ; Lvar buf1_43.(gv)
                                    ; Lvar buf2_43.(gv)
                                    ; Lvar buf3_43.(gv)
                                    ; Lvar offset_181.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_43
                                                                    ; Pvar buf1_43
                                                                    ; Pvar buf2_43
                                                                    ; Pvar buf3_43
                                                                    ; Pvar offset_181
                                                                    ; Pconst (200)%Z
                                                                    ; Pvar st_127 ])
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U8 536 buf_168.(gv) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (536)%Z))) AT_none (aarr U8 536) (Pvar buf0_43))
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U8 536 buf_168.(gv) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (536)%Z))) AT_none (aarr U8 536) (Pvar buf1_43))
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U8 536 buf_168.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (536)%Z))) AT_none (aarr U8 536) (Pvar buf2_43))
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U8 536 buf_168.(gv) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (536)%Z))) AT_none (aarr U8 536) (Pvar buf3_43)) ].

Definition fd__shake128x4_squeeze3blocks : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake128x4_squeeze3blocks;
    f_params := args__shake128x4_squeeze3blocks;
    f_body := body__shake128x4_squeeze3blocks;
    f_tyout := tyout__shake128x4_squeeze3blocks;
    f_res := res__shake128x4_squeeze3blocks;
    f_extra := tt;
  |}.

End IDO.
