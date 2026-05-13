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

(* __keccakf1600_avx2x4 *)
(* Local variables *)
Definition a_18650 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18650).
Definition RC : gvar := mk_rocq_gvar Slocal (aarr U64 24) (mkident 18651).
Definition s_e : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18652).
Definition e_18653 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18653).
Definition r8_18654 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18654).
Definition r56_18655 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18655).
Definition c : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18656).
Definition rc_18657 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18657).
Definition t_18658 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18658).

(* Signature *)
Definition tyin___keccakf1600_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition args___keccakf1600_avx2x4 : seq var_i := [:: a_18650.(gv) ].
Definition tyout___keccakf1600_avx2x4 : seq atype := [:: aarr U256 25 ].
Definition res___keccakf1600_avx2x4 : seq var_i := [:: a_18650.(gv) ].

(* Body *)
Definition body___keccakf1600_avx2x4 : cmd :=
  [:: cassgn (Lvar RC.(gv)) (aarr U64 24) (Pvar KECCAK1600_RC)
    ; cassgn (Lvar e_18653.(gv)) (aarr U256 25) (Pvar s_e)
    ; cassgn (Lvar r8_18654.(gv)) (aword U256) (Pvar ROL8)
    ; cassgn (Lvar r56_18655.(gv)) (aword U256) (Pvar ROL56)
    ; cassgn (Lvar c.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar c) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (24)%Z)))
        [:: copn [:: Lvar rc_18657.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Aligned AAscale U64 RC (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar c)) ]
          ; ccall [:: Lvar e_18653.(gv) ] _keccakf1600_4x_pround [:: Pvar e_18653
                                                                   ; Pvar a_18650
                                                                   ; Pvar r8_18654
                                                                   ; Pvar r56_18655 ]
          ; cassgn (Lvar t_18658.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar rc_18657) (Pget Aligned AAscale U256 e_18653 (Pconst (0)%Z)))
          ; cassgn (Laset Aligned AAscale U256 e_18653.(gv) (Pconst (0)%Z)) (aword U256) (Pvar t_18658)
          ; copn [:: Lvar a_18650.(gv); Lvar e_18653.(gv) ] (Opseudo_op (Oswap (aarr U256 25%positive))) [:: Pvar e_18653
                                                                    ; Pvar a_18650 ]
          ; copn [:: Lvar rc_18657.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Aligned AAscale U64 RC (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar c) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]
          ; ccall [:: Lvar a_18650.(gv) ] _keccakf1600_4x_pround [:: Pvar a_18650
                                                                   ; Pvar e_18653
                                                                   ; Pvar r8_18654
                                                                   ; Pvar r56_18655 ]
          ; cassgn (Lvar t_18658.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar rc_18657) (Pget Aligned AAscale U256 a_18650 (Pconst (0)%Z)))
          ; cassgn (Laset Aligned AAscale U256 a_18650.(gv) (Pconst (0)%Z)) (aword U256) (Pvar t_18658)
          ; copn [:: Lvar a_18650.(gv); Lvar e_18653.(gv) ] (Opseudo_op (Oswap (aarr U256 25%positive))) [:: Pvar e_18653
                                                                    ; Pvar a_18650 ]
          ; cassgn (Lvar c.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar c) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))) ] ].

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
