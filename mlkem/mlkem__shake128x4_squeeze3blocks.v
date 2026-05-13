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

(* _shake128x4_squeeze3blocks *)
(* Local variables *)
Definition st_14295 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14295).
Definition buf_14296 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2144) (mkident 14296).
Definition buf0_14297 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14297).
Definition buf1_14298 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14298).
Definition buf2_14299 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14299).
Definition buf3_14300 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14300).
Definition offset_14301 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14301).

(* Signature *)
Definition tyin__shake128x4_squeeze3blocks : seq atype :=
  [:: aarr U256 25; aarr U8 2144 ].
Definition args__shake128x4_squeeze3blocks : seq var_i :=
  [:: st_14295.(gv); buf_14296.(gv) ].
Definition tyout__shake128x4_squeeze3blocks : seq atype :=
  [:: aarr U256 25; aarr U8 2144 ].
Definition res__shake128x4_squeeze3blocks : seq var_i :=
  [:: st_14295.(gv); buf_14296.(gv) ].

(* Body *)
Definition body__shake128x4_squeeze3blocks : cmd :=
  [:: cassgn (Lvar buf0_14297.(gv)) (aarr U8 536) (Psub AAscale U8 536 buf_14296 (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (536)%Z)))
    ; cassgn (Lvar buf1_14298.(gv)) (aarr U8 536) (Psub AAscale U8 536 buf_14296 (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (536)%Z)))
    ; cassgn (Lvar buf2_14299.(gv)) (aarr U8 536) (Psub AAscale U8 536 buf_14296 (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (536)%Z)))
    ; cassgn (Lvar buf3_14300.(gv)) (aarr U8 536) (Psub AAscale U8 536 buf_14296 (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (536)%Z)))
    ; cassgn (Lvar offset_14301.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; ccall [:: Lvar st_14295.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14295 ]
    ; ccall [:: Lvar buf0_14297.(gv)
              ; Lvar buf1_14298.(gv)
              ; Lvar buf2_14299.(gv)
              ; Lvar buf3_14300.(gv)
              ; Lvar offset_14301.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_14297
                                                                    ; Pvar buf1_14298
                                                                    ; Pvar buf2_14299
                                                                    ; Pvar buf3_14300
                                                                    ; Pvar offset_14301
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar st_14295 ]
    ; ccall [:: Lvar st_14295.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14295 ]
    ; ccall [:: Lvar buf0_14297.(gv)
              ; Lvar buf1_14298.(gv)
              ; Lvar buf2_14299.(gv)
              ; Lvar buf3_14300.(gv)
              ; Lvar offset_14301.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_14297
                                                                    ; Pvar buf1_14298
                                                                    ; Pvar buf2_14299
                                                                    ; Pvar buf3_14300
                                                                    ; Pvar offset_14301
                                                                    ; Pconst (168)%Z
                                                                    ; Pvar st_14295 ]
    ; ccall [:: Lvar st_14295.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14295 ]
    ; ccall [:: Lvar buf0_14297.(gv)
              ; Lvar buf1_14298.(gv)
              ; Lvar buf2_14299.(gv)
              ; Lvar buf3_14300.(gv)
              ; Lvar offset_14301.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_14297
                                                                    ; Pvar buf1_14298
                                                                    ; Pvar buf2_14299
                                                                    ; Pvar buf3_14300
                                                                    ; Pvar offset_14301
                                                                    ; Pconst (200)%Z
                                                                    ; Pvar st_14295 ]
    ; cassgn (Lasub AAscale U8 536 buf_14296.(gv) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (536)%Z))) (aarr U8 536) (Pvar buf0_14297)
    ; cassgn (Lasub AAscale U8 536 buf_14296.(gv) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (536)%Z))) (aarr U8 536) (Pvar buf1_14298)
    ; cassgn (Lasub AAscale U8 536 buf_14296.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (536)%Z))) (aarr U8 536) (Pvar buf2_14299)
    ; cassgn (Lasub AAscale U8 536 buf_14296.(gv) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (536)%Z))) (aarr U8 536) (Pvar buf3_14300) ].

Definition fd__shake128x4_squeeze3blocks : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__shake128x4_squeeze3blocks;
    f_params := args__shake128x4_squeeze3blocks;
    f_body := body__shake128x4_squeeze3blocks;
    f_tyout := tyout__shake128x4_squeeze3blocks;
    f_res := res__shake128x4_squeeze3blocks;
    f_extra := tt;
  |}.

End IDO.
