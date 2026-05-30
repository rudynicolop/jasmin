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

(* __stavx2_pos_avx2 *)
(* Local variables *)
Definition POS : gvar := mk_rocq_gvar Slocal (aint) (mkident 18827).
Definition R : gvar := mk_rocq_gvar Slocal (aint) (mkident 18828).
Definition L_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18829).

(* Signature *)
Definition tyin___stavx2_pos_avx2 : seq atype := [:: aint ].
Definition args___stavx2_pos_avx2 : seq var_i := [:: POS.(gv) ].
Definition tyout___stavx2_pos_avx2 : seq atype := [:: aint; aint ].
Definition res___stavx2_pos_avx2 : seq var_i := [:: R.(gv); L_0.(gv) ].

(* Body *)
Definition body___stavx2_pos_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar POS))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pvar POS) (Pconst (4)%Z))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (1)%Z))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar L_0.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar POS) (Pconst (1)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (10)%Z))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (2)%Z))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                            [:: MkI dummy_instr_info (
                                                            Cif
                                                              (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (20)%Z))
                                                              [:: MkI dummy_instr_info (
                                                              Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (2)%Z))
                                                                ; MkI dummy_instr_info (
                                                              Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (1)%Z)) ]
                                                              [:: MkI dummy_instr_info (
                                                              Cif
                                                                (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (5)%Z))
                                                                [:: MkI dummy_instr_info (
                                                                Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (2)%Z))
                                                                  ; MkI dummy_instr_info (
                                                                Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (2)%Z)) ]
                                                                [:: MkI dummy_instr_info (
                                                                Cif
                                                                  (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (15)%Z))
                                                                  [:: MkI dummy_instr_info (
                                                                  Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (2)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                  Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (3)%Z)) ]
                                                                  [:: MkI dummy_instr_info (
                                                                  Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (16)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (3)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (7)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (3)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (1)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (23)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (3)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (2)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (14)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (3)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (3)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (11)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (4)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (22)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (4)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (1)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (8)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (4)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (2)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (19)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (4)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (3)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (21)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (5)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (17)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (5)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (1)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (13)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (5)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (2)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (9)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (5)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (3)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (6)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (6)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (0)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (12)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (6)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (1)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (18)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (6)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (2)%Z)) ]
                                                                    [:: MkI dummy_instr_info (
                                                                    Cif
                                                                    (Papp2 (Oeq (Op_int)) (Pvar POS) (Pconst (24)%Z))
                                                                    [:: MkI dummy_instr_info (
                                                                    Cassgn (Lvar R.(gv)) AT_none (aint) (Pconst (6)%Z))
                                                                    ; MkI dummy_instr_info (
                                                                    Cassgn (Lvar L_0.(gv)) AT_none (aint) (Pconst (3)%Z)) ]
                                                                    [::]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]
                              [::]) ].

Definition fd___stavx2_pos_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___stavx2_pos_avx2;
    f_params := args___stavx2_pos_avx2;
    f_body := body___stavx2_pos_avx2;
    f_tyout := tyout___stavx2_pos_avx2;
    f_res := res___stavx2_pos_avx2;
    f_extra := tt;
  |}.

End IDO.
