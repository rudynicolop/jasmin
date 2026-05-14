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
  [:: MkI dummy_instr_info (Cassgn (Lvar r0_19067.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r1_19068.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r2_19069.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r3_19070.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r4_19071.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r5_19072.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r6_19073.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r7_19074.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_19067.(gv)
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
                                                                    ; Pvar r7_19074 ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))) AT_none (aword U256) (Pvar r0_19067))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))) AT_none (aword U256) (Pvar r1_19068))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))) AT_none (aword U256) (Pvar r2_19069))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))) AT_none (aword U256) (Pvar r3_19070))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))) AT_none (aword U256) (Pvar r4_19071))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))) AT_none (aword U256) (Pvar r5_19072))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))) AT_none (aword U256) (Pvar r6_19073))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))) AT_none (aword U256) (Pvar r7_19074))
    ; MkI dummy_instr_info (Cassgn (Lvar r0_19067.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r1_19068.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r2_19069.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r3_19070.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r4_19071.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r5_19072.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r6_19073.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar r7_19074.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 rp (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar r0_19067.(gv)
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
                                                                    ; Pvar r7_19074 ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))) AT_none (aword U256) (Pvar r0_19067))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))) AT_none (aword U256) (Pvar r1_19068))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))) AT_none (aword U256) (Pvar r2_19069))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))) AT_none (aword U256) (Pvar r3_19070))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))) AT_none (aword U256) (Pvar r4_19071))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))) AT_none (aword U256) (Pvar r5_19072))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))) AT_none (aword U256) (Pvar r6_19073))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))) AT_none (aword U256) (Pvar r7_19074)) ].

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
