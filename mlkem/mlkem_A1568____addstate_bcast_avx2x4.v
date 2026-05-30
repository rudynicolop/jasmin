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

(* A1568____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_84 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15630).
Definition AT_81 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15631).
Definition buf_122 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15632).
Definition offset_123 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15633).
Definition _LEN_77 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15634).
Definition _TRAILB_45 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15635).
Definition DELTA_83 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15636).
Definition AT8_31 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15637).
Definition w_86 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15638).
Definition j_at_13 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15639).

(* Signature *)
Definition tyin_A1568____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1568; aword U64; aint; aint ].
Definition args_A1568____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_84.(gv)
    ; AT_81.(gv)
    ; buf_122.(gv)
    ; offset_123.(gv)
    ; _LEN_77.(gv)
    ; _TRAILB_45.(gv) ].
Definition tyout_A1568____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1568____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_84.(gv); AT_81.(gv); offset_123.(gv) ].

(* Body *)
Definition body_A1568____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_83.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_31.(gv)) AT_none (aint) (Pvar AT_81))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_81.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_81) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_31) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_83.(gv)
                                                                ; Lvar _LEN_77.(gv)
                                                                ; Lvar _TRAILB_45.(gv)
                                                                ; Lvar AT8_31.(gv)
                                                                ; Lvar w_86.(gv) ] A1568____a_ilen_read_bcast_upto8_at [:: Pvar buf_122
                                                                    ; Pvar offset_123
                                                                    ; Pvar DELTA_83
                                                                    ; Pvar _LEN_77
                                                                    ; Pvar _TRAILB_45
                                                                    ; Pvar AT_81
                                                                    ; Pvar AT8_31 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_86.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_86) (Pget Aligned AAscale U256 st_84 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_81) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_84.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_81) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_86))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_81.(gv)) AT_none (aint) (Pvar AT8_31)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_123.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_123) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_83))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_13.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_81) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_13) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_81) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_77) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_86.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_122 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_123)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_123.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_123) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_86.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_86) (Pget Unaligned AAdirect U256 st_84 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_13)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_84.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_13))) AT_none (aword U256) (Pvar w_86))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_13.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_13) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_81.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_81) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_77) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_77.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_77) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_77)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_45) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_83.(gv)
                                                                ; Lvar _LEN_77.(gv)
                                                                ; Lvar _TRAILB_45.(gv)
                                                                ; Lvar AT_81.(gv)
                                                                ; Lvar w_86.(gv) ] A1568____a_ilen_read_bcast_upto8_at [:: Pvar buf_122
                                                                    ; Pvar offset_123
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_77
                                                                    ; Pvar _TRAILB_45
                                                                    ; Pvar AT_81
                                                                    ; Pvar AT_81 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_86.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_86) (Pget Unaligned AAdirect U256 st_84 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_13)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_84.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_13))) AT_none (aword U256) (Pvar w_86))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_123.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_123) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_83)))) ]
                              [::]) ].

Definition fd_A1568____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____addstate_bcast_avx2x4;
    f_params := args_A1568____addstate_bcast_avx2x4;
    f_body := body_A1568____addstate_bcast_avx2x4;
    f_tyout := tyout_A1568____addstate_bcast_avx2x4;
    f_res := res_A1568____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
