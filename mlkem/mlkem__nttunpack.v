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

(* _nttunpack *)
(* Local variables *)
Definition rp : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 19066).
Definition r0_19067 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19067).
Definition r1_19068 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19068).
Definition r2_19069 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19069).
Definition r3_19070 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19070).
Definition r4_19071 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19071).
Definition r5_19072 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19072).
Definition r6_19073 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19073).
Definition r7_19074 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 19074).

(* Signature *)
Definition tyin__nttunpack : seq atype := [:: aarr U16 256 ].
Definition args__nttunpack : seq var_i := [:: rp.(gv) ].
Definition tyout__nttunpack : seq atype := [:: aarr U16 256 ].
Definition res__nttunpack : seq var_i := [:: rp.(gv) ].

(* Body *)
Definition body__nttunpack : cmd :=
  [:: cassgn (Lvar r0_19067.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)))
    ; cassgn (Lvar r1_19068.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)))
    ; cassgn (Lvar r2_19069.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)))
    ; cassgn (Lvar r3_19070.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)))
    ; cassgn (Lvar r4_19071.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)))
    ; cassgn (Lvar r5_19072.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)))
    ; cassgn (Lvar r6_19073.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)))
    ; cassgn (Lvar r7_19074.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)))
    ; ccall [:: Lvar r0_19067.(gv)
              ; Lvar r1_19068.(gv)
              ; Lvar r2_19069.(gv)
              ; Lvar r3_19070.(gv)
              ; Lvar r4_19071.(gv)
              ; Lvar r5_19072.(gv)
              ; Lvar r6_19073.(gv)
              ; Lvar r7_19074.(gv) ] __nttunpack128 [:: Pvar r0_19067
                                                      ; Pvar r1_19068
                                                      ; Pvar r2_19069
                                                      ; Pvar r3_19070
                                                      ; Pvar r4_19071
                                                      ; Pvar r5_19072
                                                      ; Pvar r6_19073
                                                      ; Pvar r7_19074 ]
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))) (aword U256) (Pvar r0_19067)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))) (aword U256) (Pvar r1_19068)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))) (aword U256) (Pvar r2_19069)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))) (aword U256) (Pvar r3_19070)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))) (aword U256) (Pvar r4_19071)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))) (aword U256) (Pvar r5_19072)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))) (aword U256) (Pvar r6_19073)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))) (aword U256) (Pvar r7_19074)
    ; cassgn (Lvar r0_19067.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)))
    ; cassgn (Lvar r1_19068.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z)))
    ; cassgn (Lvar r2_19069.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z)))
    ; cassgn (Lvar r3_19070.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z)))
    ; cassgn (Lvar r4_19071.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z)))
    ; cassgn (Lvar r5_19072.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z)))
    ; cassgn (Lvar r6_19073.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z)))
    ; cassgn (Lvar r7_19074.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z)))
    ; ccall [:: Lvar r0_19067.(gv)
              ; Lvar r1_19068.(gv)
              ; Lvar r2_19069.(gv)
              ; Lvar r3_19070.(gv)
              ; Lvar r4_19071.(gv)
              ; Lvar r5_19072.(gv)
              ; Lvar r6_19073.(gv)
              ; Lvar r7_19074.(gv) ] __nttunpack128 [:: Pvar r0_19067
                                                      ; Pvar r1_19068
                                                      ; Pvar r2_19069
                                                      ; Pvar r3_19070
                                                      ; Pvar r4_19071
                                                      ; Pvar r5_19072
                                                      ; Pvar r6_19073
                                                      ; Pvar r7_19074 ]
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))) (aword U256) (Pvar r0_19067)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))) (aword U256) (Pvar r1_19068)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))) (aword U256) (Pvar r2_19069)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))) (aword U256) (Pvar r3_19070)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))) (aword U256) (Pvar r4_19071)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))) (aword U256) (Pvar r5_19072)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))) (aword U256) (Pvar r6_19073)
    ; cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))) (aword U256) (Pvar r7_19074) ].

Definition fd__nttunpack : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__nttunpack;
    f_params := args__nttunpack;
    f_body := body__nttunpack;
    f_tyout := tyout__nttunpack;
    f_res := res__nttunpack;
    f_extra := tt;
  |}.

End IDO.
