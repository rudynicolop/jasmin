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

(* A1184____squeeze_avx2 *)
(* Local variables *)
Definition st_73 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16031).
Definition buf_107 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16032).
Definition _RATE8_32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16033).
Definition offset_105 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16034).
Definition _LEN_66 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16035).
Definition ITERS_32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16036).
Definition LO_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16037).
Definition i_44 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16038).

(* Signature *)
Definition tyin_A1184____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1184; aint ].
Definition args_A1184____squeeze_avx2 : seq var_i :=
  [:: st_73.(gv); buf_107.(gv); _RATE8_32.(gv) ].
Definition tyout_A1184____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1184 ].
Definition res_A1184____squeeze_avx2 : seq var_i :=
  [:: st_73.(gv); buf_107.(gv) ].

(* Body *)
Definition body_A1184____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_105.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_66.(gv)) AT_none (aint) (Pconst (1184)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_32.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_66) (Pvar _RATE8_32)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_12.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_66) (Pvar _RATE8_32)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_44.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_44) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_32)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_73.(gv) ] _keccakf1600_avx2 [:: Pvar st_73 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_107.(gv)
                                                                ; Lvar offset_105.(gv) ] A1184____dumpstate_avx2 [:: Pvar buf_107
                                                                    ; Pvar offset_105
                                                                    ; Pvar _RATE8_32
                                                                    ; Pvar st_73 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_44.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_44) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_12))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_73.(gv) ] _keccakf1600_avx2 [:: Pvar st_73 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_107.(gv)
                                                                ; Lvar offset_105.(gv) ] A1184____dumpstate_avx2 [:: Pvar buf_107
                                                                    ; Pvar offset_105
                                                                    ; Pvar LO_12
                                                                    ; Pvar st_73 ]) ]
                              [::]) ].

Definition fd_A1184____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____squeeze_avx2;
    f_params := args_A1184____squeeze_avx2;
    f_body := body_A1184____squeeze_avx2;
    f_tyout := tyout_A1184____squeeze_avx2;
    f_res := res_A1184____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
