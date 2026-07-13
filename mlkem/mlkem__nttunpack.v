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

(* _nttunpack *)
(* Local variables *)
Definition rp : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 19066).
Definition r0_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19067).
Definition r1_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19068).
Definition r2_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19069).
Definition r3_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19070).
Definition r4_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19071).
Definition r5_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19072).
Definition r6_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19073).
Definition r7_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 19074).

(* Signature *)
Definition tyin__nttunpack : seq atype := [:: aarr U16 256 ].
Definition args__nttunpack : seq var_i := [:: rp.(gv) ].
Definition tyout__nttunpack : seq atype := [:: aarr U16 256 ].
Definition res__nttunpack : seq var_i := [:: rp.(gv) ].

(* Body *)
Definition body__nttunpack : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar r0_3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r1_3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r2_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r3_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r4_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r5_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r6_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r7_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_3.(gv)
                                    ; Lvar r1_3.(gv)
                                    ; Lvar r2_0.(gv)
                                    ; Lvar r3_0.(gv)
                                    ; Lvar r4_0.(gv)
                                    ; Lvar r5_0.(gv)
                                    ; Lvar r6_0.(gv)
                                    ; Lvar r7_0.(gv) ] __nttunpack128 [:: Pvar r0_3
                                                                    ; Pvar r1_3
                                                                    ; Pvar r2_0
                                                                    ; Pvar r3_0
                                                                    ; Pvar r4_0
                                                                    ; Pvar r5_0
                                                                    ; Pvar r6_0
                                                                    ; Pvar r7_0 ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))) AT_none (aword U256) (Pvar r0_3))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))) AT_none (aword U256) (Pvar r1_3))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))) AT_none (aword U256) (Pvar r2_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))) AT_none (aword U256) (Pvar r3_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))) AT_none (aword U256) (Pvar r4_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))) AT_none (aword U256) (Pvar r5_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))) AT_none (aword U256) (Pvar r6_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))) AT_none (aword U256) (Pvar r7_0))
    ; MkI dummy_instr_info (Cassgn (Lvar r0_3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r1_3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r2_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r3_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r4_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r5_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r6_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r7_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_3.(gv)
                                    ; Lvar r1_3.(gv)
                                    ; Lvar r2_0.(gv)
                                    ; Lvar r3_0.(gv)
                                    ; Lvar r4_0.(gv)
                                    ; Lvar r5_0.(gv)
                                    ; Lvar r6_0.(gv)
                                    ; Lvar r7_0.(gv) ] __nttunpack128 [:: Pvar r0_3
                                                                    ; Pvar r1_3
                                                                    ; Pvar r2_0
                                                                    ; Pvar r3_0
                                                                    ; Pvar r4_0
                                                                    ; Pvar r5_0
                                                                    ; Pvar r6_0
                                                                    ; Pvar r7_0 ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))) AT_none (aword U256) (Pvar r0_3))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))) AT_none (aword U256) (Pvar r1_3))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))) AT_none (aword U256) (Pvar r2_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))) AT_none (aword U256) (Pvar r3_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))) AT_none (aword U256) (Pvar r4_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))) AT_none (aword U256) (Pvar r5_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))) AT_none (aword U256) (Pvar r6_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))) AT_none (aword U256) (Pvar r7_0)) ].

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
