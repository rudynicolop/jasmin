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

(* A1600____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_104 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14866).
Definition AT_101 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14867).
Definition buf_150 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14868).
Definition offset_157 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14869).
Definition _LEN_97 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14870).
Definition _TRAILB_57 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14871).
Definition DELTA_105 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14872).
Definition AT8_39 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14873).
Definition w_106 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14874).
Definition j_at_17 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14875).

(* Signature *)
Definition tyin_A1600____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1600; aword U64; aint; aint ].
Definition args_A1600____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_104.(gv)
    ; AT_101.(gv)
    ; buf_150.(gv)
    ; offset_157.(gv)
    ; _LEN_97.(gv)
    ; _TRAILB_57.(gv) ].
Definition tyout_A1600____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1600____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_104.(gv); AT_101.(gv); offset_157.(gv) ].

(* Body *)
Definition body_A1600____addstate_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_105.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_39.(gv)) AT_none (aint) (Pvar AT_101))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_101.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_101) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_39) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_105.(gv)
                                                                ; Lvar _LEN_97.(gv)
                                                                ; Lvar _TRAILB_57.(gv)
                                                                ; Lvar AT8_39.(gv)
                                                                ; Lvar w_106.(gv) ] A1600____a_ilen_read_bcast_upto8_at [:: Pvar buf_150
                                                                    ; Pvar offset_157
                                                                    ; Pvar DELTA_105
                                                                    ; Pvar _LEN_97
                                                                    ; Pvar _TRAILB_57
                                                                    ; Pvar AT_101
                                                                    ; Pvar AT8_39 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_106.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_106) (Pget Aligned AAscale U256 st_104 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_101) (Pconst (8)%Z)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_104.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_101) (Pconst (8)%Z))) AT_none (aword U256) (Pvar w_106))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_101.(gv)) AT_none (aint) (Pvar AT8_39)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_157.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_157) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_105))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_17.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_101) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_17) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_101) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_97) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_106.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_150 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_157)) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_157.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_157) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar w_106.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_106) (Pget Unaligned AAdirect U256 st_104 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_104.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17))) AT_none (aword U256) (Pvar w_106))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_17.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_101.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_101) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_97) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_97.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_97) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_97)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_57) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_105.(gv)
                                                                ; Lvar _LEN_97.(gv)
                                                                ; Lvar _TRAILB_57.(gv)
                                                                ; Lvar AT_101.(gv)
                                                                ; Lvar w_106.(gv) ] A1600____a_ilen_read_bcast_upto8_at [:: Pvar buf_150
                                                                    ; Pvar offset_157
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_97
                                                                    ; Pvar _TRAILB_57
                                                                    ; Pvar AT_101
                                                                    ; Pvar AT_101 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar w_106.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar w_106) (Pget Unaligned AAdirect U256 st_104 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17)))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 st_104.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17))) AT_none (aword U256) (Pvar w_106))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_157.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_157) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_105)))) ]
                              [::]) ].

Definition fd_A1600____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____addstate_bcast_avx2x4;
    f_params := args_A1600____addstate_bcast_avx2x4;
    f_body := body_A1600____addstate_bcast_avx2x4;
    f_tyout := tyout_A1600____addstate_bcast_avx2x4;
    f_res := res_A1600____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
