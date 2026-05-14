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

(* ABUFLEN____addstate_avx2 *)
(* Local variables *)
Definition st_14551 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 14551).
Definition AT_14552 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14552).
Definition buf_14553 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14553).
Definition offset_14554 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14554).
Definition _LEN_14555 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14555).
Definition _TRAILB_14556 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14556).
Definition DELTA_14557 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14557).
Definition r0_14558 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14558).
Definition r1_14559 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14559).
Definition t64_2_14560 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14560).
Definition t128_1_14561 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14561).
Definition t128_2_14562 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14562).
Definition r3_14563 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14563).
Definition t64_3_14564 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14564).
Definition r4_14565 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14565).
Definition t64_4_14566 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14566).
Definition r5_14567 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14567).
Definition t64_5_14568 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14568).
Definition r6_14569 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14569).
Definition r2_14570 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14570).

(* Signature *)
Definition tyin_ABUFLEN____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 536; aword U64; aint; aint ].
Definition args_ABUFLEN____addstate_avx2 : seq var_i :=
  [:: st_14551.(gv)
    ; AT_14552.(gv)
    ; buf_14553.(gv)
    ; offset_14554.(gv)
    ; _LEN_14555.(gv)
    ; _TRAILB_14556.(gv) ].
Definition tyout_ABUFLEN____addstate_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64 ].
Definition res_ABUFLEN____addstate_avx2 : seq var_i :=
  [:: st_14551.(gv); AT_14552.(gv); offset_14554.(gv) ].

(* Body *)
Definition body_ABUFLEN____addstate_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_14557.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pvar AT_14552) (Pconst (8)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_14557.(gv)
                                                                ; Lvar _LEN_14555.(gv)
                                                                ; Lvar _TRAILB_14556.(gv)
                                                                ; Lvar AT_14552.(gv)
                                                                ; Lvar r0_14558.(gv) ] ABUFLEN____a_ilen_read_bcast_upto8_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT_14552 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_14551.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_14551 (Pconst (0)%Z)) (Pvar r0_14558))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oand) (Papp2 (Olt (Cmp_int)) (Pvar AT_14552) (Pconst (40)%Z)) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14555)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14556) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_14557.(gv)
                                                                ; Lvar _LEN_14555.(gv)
                                                                ; Lvar _TRAILB_14556.(gv)
                                                                ; Lvar AT_14552.(gv)
                                                                ; Lvar r1_14559.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT_14552 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_14551.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_14551 (Pconst (1)%Z)) (Pvar r1_14559))) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14555)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14556) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar DELTA_14557.(gv)
                                                                ; Lvar _LEN_14555.(gv)
                                                                ; Lvar _TRAILB_14556.(gv)
                                                                ; Lvar AT_14552.(gv)
                                                                ; Lvar t64_2_14560.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (40)%Z
                                                                    ; Pvar AT_14552 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t128_1_14561.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_2_14560)))
                                ; MkI dummy_instr_info (Copn [:: Lvar t128_2_14562.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14555)) (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14556) (Pconst (0)%Z)))
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14557.(gv)
                                                                  ; Lvar _LEN_14555.(gv)
                                                                  ; Lvar _TRAILB_14556.(gv)
                                                                  ; Lvar AT_14552.(gv)
                                                                  ; Lvar r3_14563.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (48)%Z
                                                                    ; Pvar AT_14552 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14557.(gv)
                                                                  ; Lvar _LEN_14555.(gv)
                                                                  ; Lvar _TRAILB_14556.(gv)
                                                                  ; Lvar AT_14552.(gv)
                                                                  ; Lvar t64_3_14564.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (80)%Z
                                                                    ; Pvar AT_14552 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_2_14562.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_3_14564)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14557.(gv)
                                                                  ; Lvar _LEN_14555.(gv)
                                                                  ; Lvar _TRAILB_14556.(gv)
                                                                  ; Lvar AT_14552.(gv)
                                                                  ; Lvar r4_14565.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (88)%Z
                                                                    ; Pvar AT_14552 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14557.(gv)
                                                                  ; Lvar _LEN_14555.(gv)
                                                                  ; Lvar _TRAILB_14556.(gv)
                                                                  ; Lvar AT_14552.(gv)
                                                                  ; Lvar t64_4_14566.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (120)%Z
                                                                    ; Pvar AT_14552 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_1_14561.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_1_14561
                                                                    ; Pvar t64_4_14566
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14557.(gv)
                                                                  ; Lvar _LEN_14555.(gv)
                                                                  ; Lvar _TRAILB_14556.(gv)
                                                                  ; Lvar AT_14552.(gv)
                                                                  ; Lvar r5_14567.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (128)%Z
                                                                    ; Pvar AT_14552 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14557.(gv)
                                                                  ; Lvar _LEN_14555.(gv)
                                                                  ; Lvar _TRAILB_14556.(gv)
                                                                  ; Lvar AT_14552.(gv)
                                                                  ; Lvar t64_5_14568.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (160)%Z
                                                                    ; Pvar AT_14552 ])
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar t128_2_14562.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar t128_2_14562
                                                                    ; Pvar t64_5_14568
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_14557.(gv)
                                                                  ; Lvar _LEN_14555.(gv)
                                                                  ; Lvar _TRAILB_14556.(gv)
                                                                  ; Lvar AT_14552.(gv)
                                                                  ; Lvar r6_14569.(gv) ] ABUFLEN____a_ilen_read_upto32_at [:: Pvar buf_14553
                                                                    ; Pvar offset_14554
                                                                    ; Pvar DELTA_14557
                                                                    ; Pvar _LEN_14555
                                                                    ; Pvar _TRAILB_14556
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar AT_14552 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_14551.(gv) ] __addstate_r3456_avx2 [:: Pvar st_14551
                                                                    ; Pvar r3_14563
                                                                    ; Pvar r4_14565
                                                                    ; Pvar r5_14567
                                                                    ; Pvar r6_14569 ]) ]
                                                          [::])
                                ; MkI dummy_instr_info (Cassgn (Lvar r2_14570.(gv)) AT_none (aword U256) (Papp1 (Ozeroext U256 U128) (Pvar t128_2_14562)))
                                ; MkI dummy_instr_info (Copn [:: Lvar r2_14570.(gv) ] AT_none (Oasm ((BaseOp ((None), VINSERTI128)))) [:: Pvar r2_14570
                                                                    ; Pvar t128_1_14561
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 st_14551.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 st_14551 (Pconst (2)%Z)) (Pvar r2_14570))) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_14554.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14554) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14557)))) ].

Definition fd_ABUFLEN____addstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____addstate_avx2;
    f_params := args_ABUFLEN____addstate_avx2;
    f_body := body_ABUFLEN____addstate_avx2;
    f_tyout := tyout_ABUFLEN____addstate_avx2;
    f_res := res_ABUFLEN____addstate_avx2;
    f_extra := tt;
  |}.

End IDO.
