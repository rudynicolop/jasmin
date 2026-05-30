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

(* __keccakf1600_avx2x4 *)
(* Local variables *)
Definition a_5 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18650).
Definition RC : gvar := mk_rocq_gvar Slocal (aarr U64 24) (mkident 18651).
Definition s_e : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18652).
Definition e_0 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18653).
Definition r8_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18654).
Definition r56_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18655).
Definition c : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18656).
Definition rc_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18657).
Definition t_2 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18658).

(* Signature *)
Definition tyin___keccakf1600_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition args___keccakf1600_avx2x4 : seq var_i := [:: a_5.(gv) ].
Definition tyout___keccakf1600_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition res___keccakf1600_avx2x4 : seq var_i := [:: a_5.(gv) ].

(* Body *)
Definition body___keccakf1600_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar RC.(gv)) AT_none (aarr U64 24) (Pvar KECCAK1600_RC))
    ; MkI dummy_instr_info (Cassgn (Lvar e_0.(gv)) AT_none (aarr U256 25) (Pvar s_e))
    ; MkI dummy_instr_info (Cassgn (Lvar r8_0.(gv)) AT_none (aword U256) (Pvar ROL8))
    ; MkI dummy_instr_info (Cassgn (Lvar r56_0.(gv)) AT_none (aword U256) (Pvar ROL56))
    ; MkI dummy_instr_info (Cassgn (Lvar c.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar c) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (24)%Z)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar rc_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Aligned AAscale U64 RC (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar c)) ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar e_0.(gv) ] _keccakf1600_4x_pround [:: Pvar e_0
                                                                    ; Pvar a_5
                                                                    ; Pvar r8_0
                                                                    ; Pvar r56_0 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_2.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar rc_0) (Pget Aligned AAscale U256 e_0 (Pconst (0)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e_0.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar t_2))
                                ; MkI dummy_instr_info (Copn [:: Lvar a_5.(gv)
                                                               ; Lvar e_0.(gv) ] AT_none (Opseudo_op (Oswap (aarr U256 25%positive))) [:: Pvar e_0
                                                                    ; Pvar a_5 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar rc_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Aligned AAscale U64 RC (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar c) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar a_5.(gv) ] _keccakf1600_4x_pround [:: Pvar a_5
                                                                    ; Pvar e_0
                                                                    ; Pvar r8_0
                                                                    ; Pvar r56_0 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t_2.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar rc_0) (Pget Aligned AAscale U256 a_5 (Pconst (0)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 a_5.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar t_2))
                                ; MkI dummy_instr_info (Copn [:: Lvar a_5.(gv)
                                                               ; Lvar e_0.(gv) ] AT_none (Opseudo_op (Oswap (aarr U256 25%positive))) [:: Pvar e_0
                                                                    ; Pvar a_5 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar c.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar c) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z)))) ]) ].

Definition fd___keccakf1600_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___keccakf1600_avx2x4;
    f_params := args___keccakf1600_avx2x4;
    f_body := body___keccakf1600_avx2x4;
    f_tyout := tyout___keccakf1600_avx2x4;
    f_res := res___keccakf1600_avx2x4;
    f_extra := tt;
  |}.

End IDO.
