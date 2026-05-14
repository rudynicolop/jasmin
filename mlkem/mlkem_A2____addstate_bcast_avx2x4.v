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

(* A2____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_17787 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17787).
Definition AT_17788 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17788).
Definition buf_17789 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17789).
Definition offset_17790 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17790).
Definition _LEN_17791 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17791).
Definition _TRAILB_17792 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17792).
Definition DELTA_17793 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17793).
Definition AT8_17794 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17794).
Definition w_17795 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17795).
Definition j_at_17796 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17796).

(* Signature *)
Definition tyin_A2____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 2; aword U64; aint; aint ].
Definition args_A2____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_17787.(gv)
    ; AT_17788.(gv)
    ; buf_17789.(gv)
    ; offset_17790.(gv)
    ; _LEN_17791.(gv)
    ; _TRAILB_17792.(gv) ].
Definition tyout_A2____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A2____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_17787.(gv); AT_17788.(gv); offset_17790.(gv) ].

(* Body *)
Definition body_A2____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_17793.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_17794.(gv)) AT_none (aint) (Pvar AT_17788))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_17788.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17788) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_17794) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17793.(gv)
                                                                ; Lvar _LEN_17791.(gv)
                                                                ; Lvar _TRAILB_17792.(gv)
                                                                ; Lvar AT8_17794.(gv)
                                                                ; Lvar w_17795.(gv) ] A2____a_ilen_read_bcast_upto8_at [:: Pvar buf_17789
                                                                    ; Pvar offset_17790
                                                                    ; Pvar DELTA_17793
                                                                    ; Pvar _LEN_17791
                                                                    ; Pvar _TRAILB_17792
                                                                    ; Pvar AT_17788
                                                                    ; Pvar AT8_17794 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_17795.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_17795) (Pget Aligned AAscale U256 st_17787 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17788) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_17787.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17788) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_17795))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_17788.(gv)) AT_none (aint) (Pvar AT8_17794)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_17790.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17790) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17793))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_17796.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17788) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_17796) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17788) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17791) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_17795.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_17789 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17790)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_17790.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17790) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_17795.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_17795) (Pget Unaligned AAdirect U256 st_17787 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17796)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_17787.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17796))) AT_none (aword U256) (Pvar w_17795))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_17796.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17796) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_17788.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_17788) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17791) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17791.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17791) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17791)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_17792) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_17793.(gv)
                                                                ; Lvar _LEN_17791.(gv)
                                                                ; Lvar _TRAILB_17792.(gv)
                                                                ; Lvar AT_17788.(gv)
                                                                ; Lvar w_17795.(gv) ] A2____a_ilen_read_bcast_upto8_at [:: Pvar buf_17789
                                                                    ; Pvar offset_17790
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17791
                                                                    ; Pvar _TRAILB_17792
                                                                    ; Pvar AT_17788
                                                                    ; Pvar AT_17788 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_17795.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_17795) (Pget Unaligned AAdirect U256 st_17787 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17796)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_17787.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17796))) AT_none (aword U256) (Pvar w_17795))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_17790.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17790) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17793)))) ]
                              [::]) ].

Definition fd_A2____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____addstate_bcast_avx2x4;
    f_params := args_A2____addstate_bcast_avx2x4;
    f_body := body_A2____addstate_bcast_avx2x4;
    f_tyout := tyout_A2____addstate_bcast_avx2x4;
    f_res := res_A2____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
