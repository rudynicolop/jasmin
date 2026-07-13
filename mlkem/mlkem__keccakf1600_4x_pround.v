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

(* _keccakf1600_4x_pround *)
(* Local variables *)
Definition e : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18659).
Definition a_4 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18660).
Definition r8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18661).
Definition r56 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18662).
Definition c_571 : gvar := mk_rocq_gvar Slocal (aarr U256 5) (mkident 18663).
Definition d_619 : gvar := mk_rocq_gvar Slocal (aarr U256 5) (mkident 18664).
Definition t_574 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18665).
Definition t_577 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18666).
Definition t_580 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18667).
Definition t_583 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18668).
Definition t_586 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18669).
Definition b_606 : gvar := mk_rocq_gvar Slocal (aarr U256 5) (mkident 18670).
Definition t_593 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18671).
Definition t_596 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18672).
Definition t_599 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18673).
Definition t_602 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18674).
Definition t_607 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18675).
Definition t_608 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18676).
Definition t_609 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18677).
Definition t_610 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18678).
Definition t_611 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18679).
Definition t_612 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18680).
Definition t_613 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18681).
Definition t_614 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18682).
Definition t_615 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18683).
Definition t_616 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18684).
Definition b_638 : gvar := mk_rocq_gvar Slocal (aarr U256 5) (mkident 18685).
Definition t_622 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18686).
Definition t_625 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18687).
Definition t_628 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18688).
Definition t_631 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18689).
Definition t_634 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18690).
Definition t_639 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18691).
Definition t_640 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18692).
Definition t_641 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18693).
Definition t_642 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18694).
Definition t_643 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18695).
Definition t_644 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18696).
Definition t_645 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18697).
Definition t_646 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18698).
Definition t_647 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18699).
Definition t_648 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18700).
Definition b_671 : gvar := mk_rocq_gvar Slocal (aarr U256 5) (mkident 18701).
Definition t_655 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18702).
Definition t_658 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18703).
Definition t_661 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18704).
Definition t_667 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18705).
Definition t_672 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18706).
Definition t_673 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18707).
Definition t_674 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18708).
Definition t_675 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18709).
Definition t_676 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18710).
Definition t_677 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18711).
Definition t_678 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18712).
Definition t_679 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18713).
Definition t_680 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18714).
Definition t_681 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18715).
Definition b_704 : gvar := mk_rocq_gvar Slocal (aarr U256 5) (mkident 18716).
Definition t_688 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18717).
Definition t_691 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18718).
Definition t_694 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18719).
Definition t_697 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18720).
Definition t_705 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18721).
Definition t_706 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18722).
Definition t_707 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18723).
Definition t_708 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18724).
Definition t_709 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18725).
Definition t_710 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18726).
Definition t_711 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18727).
Definition t_712 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18728).
Definition t_713 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18729).
Definition t_714 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18730).
Definition b_736 : gvar := mk_rocq_gvar Slocal (aarr U256 5) (mkident 18731).
Definition t_720 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18732).
Definition t_723 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18733).
Definition t_726 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18734).
Definition t_729 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18735).
Definition t_732 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18736).
Definition t_737 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18737).
Definition t_738 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18738).
Definition t_739 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18739).
Definition t_740 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18740).
Definition t_741 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18741).
Definition t_742 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18742).
Definition t_743 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18743).
Definition t_744 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18744).
Definition t_745 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18745).
Definition t_746 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18746).

(* Signature *)
Definition tyin__keccakf1600_4x_pround : seq atype :=
  [:: aarr U256 25; aarr U256 25; aword U256; aword U256 ].
Definition args__keccakf1600_4x_pround : seq var_i :=
  [:: e.(gv); a_4.(gv); r8.(gv); r56.(gv) ].
Definition tyout__keccakf1600_4x_pround : seq atype := [:: aarr U256 25 ].
Definition res__keccakf1600_4x_pround : seq var_i := [:: e.(gv) ].

(* Body *)
Definition body__keccakf1600_4x_pround : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (1)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (2)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (3)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (4)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (5)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (6)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (7)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (9)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (10)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (11)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (12)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (13)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (14)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (15)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (16)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (17)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (18)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (19)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (20)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (21)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (22)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (23)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)) (Pget Aligned AAscale U256 a_4 (Pconst (24)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar t_574.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (0)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)) (Pvar t_574)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar t_577.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (1)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)) (Pvar t_577)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar t_580.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)) (Pvar t_580)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar t_583.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)) (Pvar t_583)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar t_586.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)) (Pvar t_586)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (6)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_593.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (44)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_606.(gv) (Pconst (1)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (20)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)) (Pvar t_593)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (12)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_596.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (43)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_606.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (21)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)) (Pvar t_596)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (18)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_599.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (21)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_606.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (43)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)) (Pvar t_599)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (24)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_602.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (14)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_606.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (50)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)) (Pvar t_602)))
    ; MkI dummy_instr_info (Copn [:: Lvar t_607.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (2)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_608.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_607) (Pget Aligned AAscale U256 b_606 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar t_608))
    ; MkI dummy_instr_info (Copn [:: Lvar t_609.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (3)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_610.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_609) (Pget Aligned AAscale U256 b_606 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pvar t_610))
    ; MkI dummy_instr_info (Copn [:: Lvar t_611.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (4)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_612.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_611) (Pget Aligned AAscale U256 b_606 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Pvar t_612))
    ; MkI dummy_instr_info (Copn [:: Lvar t_613.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_614.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_613) (Pget Aligned AAscale U256 b_606 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Pvar t_614))
    ; MkI dummy_instr_info (Copn [:: Lvar t_615.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_616.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_615) (Pget Aligned AAscale U256 b_606 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Pvar t_616))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (3)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_622.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (28)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (0)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (36)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)) (Pvar t_622)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (9)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_625.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (20)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (1)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (44)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)) (Pvar t_625)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (10)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_628.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (3)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (61)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)) (Pvar t_628)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (16)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_631.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (45)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (19)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)) (Pvar t_631)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (22)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_634.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (61)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (3)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)) (Pvar t_634)))
    ; MkI dummy_instr_info (Copn [:: Lvar t_639.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (2)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_640.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_639) (Pget Aligned AAscale U256 b_638 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (5)%Z)) AT_none (aword U256) (Pvar t_640))
    ; MkI dummy_instr_info (Copn [:: Lvar t_641.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (3)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_642.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_641) (Pget Aligned AAscale U256 b_638 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (6)%Z)) AT_none (aword U256) (Pvar t_642))
    ; MkI dummy_instr_info (Copn [:: Lvar t_643.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (4)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_644.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_643) (Pget Aligned AAscale U256 b_638 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (7)%Z)) AT_none (aword U256) (Pvar t_644))
    ; MkI dummy_instr_info (Copn [:: Lvar t_645.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_646.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_645) (Pget Aligned AAscale U256 b_638 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (8)%Z)) AT_none (aword U256) (Pvar t_646))
    ; MkI dummy_instr_info (Copn [:: Lvar t_647.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_648.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_647) (Pget Aligned AAscale U256 b_638 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (9)%Z)) AT_none (aword U256) (Pvar t_648))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (1)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_655.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (0)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)) (Pvar t_655)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (7)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_658.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (6)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (1)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (58)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)) (Pvar t_658)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (13)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_661.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (25)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (39)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)) (Pvar t_661)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (19)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (3)%Z)
                                                                    ; Pvar r8 ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (20)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_667.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (18)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (46)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)) (Pvar t_667)))
    ; MkI dummy_instr_info (Copn [:: Lvar t_672.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (2)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_673.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_672) (Pget Aligned AAscale U256 b_671 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (10)%Z)) AT_none (aword U256) (Pvar t_673))
    ; MkI dummy_instr_info (Copn [:: Lvar t_674.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (3)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_675.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_674) (Pget Aligned AAscale U256 b_671 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (11)%Z)) AT_none (aword U256) (Pvar t_675))
    ; MkI dummy_instr_info (Copn [:: Lvar t_676.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (4)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_677.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_676) (Pget Aligned AAscale U256 b_671 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (12)%Z)) AT_none (aword U256) (Pvar t_677))
    ; MkI dummy_instr_info (Copn [:: Lvar t_678.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_679.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_678) (Pget Aligned AAscale U256 b_671 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (13)%Z)) AT_none (aword U256) (Pvar t_679))
    ; MkI dummy_instr_info (Copn [:: Lvar t_680.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_681.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_680) (Pget Aligned AAscale U256 b_671 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (14)%Z)) AT_none (aword U256) (Pvar t_681))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (4)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_688.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (27)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (0)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (37)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)) (Pvar t_688)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (5)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_691.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (36)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (1)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (28)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)) (Pvar t_691)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (11)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_694.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (10)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (54)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)) (Pvar t_694)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (17)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_697.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (49)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)) (Pvar t_697)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (23)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (4)%Z)
                                                                    ; Pvar r56 ])
    ; MkI dummy_instr_info (Copn [:: Lvar t_705.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (2)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_706.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_705) (Pget Aligned AAscale U256 b_704 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (15)%Z)) AT_none (aword U256) (Pvar t_706))
    ; MkI dummy_instr_info (Copn [:: Lvar t_707.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (3)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_708.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_707) (Pget Aligned AAscale U256 b_704 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (16)%Z)) AT_none (aword U256) (Pvar t_708))
    ; MkI dummy_instr_info (Copn [:: Lvar t_709.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (4)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_710.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_709) (Pget Aligned AAscale U256 b_704 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (17)%Z)) AT_none (aword U256) (Pvar t_710))
    ; MkI dummy_instr_info (Copn [:: Lvar t_711.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_712.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_711) (Pget Aligned AAscale U256 b_704 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (18)%Z)) AT_none (aword U256) (Pvar t_712))
    ; MkI dummy_instr_info (Copn [:: Lvar t_713.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_714.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_713) (Pget Aligned AAscale U256 b_704 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (19)%Z)) AT_none (aword U256) (Pvar t_714))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (2)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_720.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (62)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (0)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (2)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)) (Pvar t_720)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_723.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (55)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (1)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (9)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (1)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)) (Pvar t_723)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (14)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_726.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (39)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (2)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (25)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (2)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)) (Pvar t_726)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (15)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_729.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (41)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (3)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (23)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (3)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)) (Pvar t_729)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Pget Aligned AAscale U256 a_4 (Pconst (21)%Z)))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Copn [:: Lvar t_732.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (2)%Z) ])
    ; MkI dummy_instr_info (Copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (4)%Z) ] AT_none (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (62)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (4)%Z)) AT_none (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)) (Pvar t_732)))
    ; MkI dummy_instr_info (Copn [:: Lvar t_737.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (2)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_738.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_737) (Pget Aligned AAscale U256 b_736 (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (20)%Z)) AT_none (aword U256) (Pvar t_738))
    ; MkI dummy_instr_info (Copn [:: Lvar t_739.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (3)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_740.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_739) (Pget Aligned AAscale U256 b_736 (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (21)%Z)) AT_none (aword U256) (Pvar t_740))
    ; MkI dummy_instr_info (Copn [:: Lvar t_741.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (4)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_742.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_741) (Pget Aligned AAscale U256 b_736 (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (22)%Z)) AT_none (aword U256) (Pvar t_742))
    ; MkI dummy_instr_info (Copn [:: Lvar t_743.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (0)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_744.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_743) (Pget Aligned AAscale U256 b_736 (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (23)%Z)) AT_none (aword U256) (Pvar t_744))
    ; MkI dummy_instr_info (Copn [:: Lvar t_745.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (1)%Z) ])
    ; MkI dummy_instr_info (Cassgn (Lvar t_746.(gv)) AT_none (aword U256) (Papp2 (Olxor U256) (Pvar t_745) (Pget Aligned AAscale U256 b_736 (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (24)%Z)) AT_none (aword U256) (Pvar t_746)) ].

Definition fd__keccakf1600_4x_pround : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__keccakf1600_4x_pround;
    f_params := args__keccakf1600_4x_pround;
    f_body := body__keccakf1600_4x_pround;
    f_tyout := tyout__keccakf1600_4x_pround;
    f_res := res__keccakf1600_4x_pround;
    f_extra := tt;
  |}.

End IDO.
