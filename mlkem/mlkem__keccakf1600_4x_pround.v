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

(* _keccakf1600_4x_pround *)
(* Local variables *)
Definition e : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18659).
Definition a_18660 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18660).
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
  [:: e.(gv); a_18660.(gv); r8.(gv); r56.(gv) ].
Definition tyout__keccakf1600_4x_pround : seq atype := [:: aarr U256 25 ].
Definition res__keccakf1600_4x_pround : seq var_i := [:: e.(gv) ].

(* Body *)
Definition body__keccakf1600_4x_pround : cmd :=
  [:: cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (0)%Z))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (1)%Z))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (2)%Z))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (3)%Z))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (4)%Z))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (5)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (6)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (7)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (8)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (9)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (10)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (11)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (12)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (13)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (14)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (15)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (16)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (17)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (18)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (19)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (20)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (21)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (22)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (23)%Z)))
    ; cassgn (Laset Aligned AAscale U256 c_571.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)) (Pget Aligned AAscale U256 a_18660 (Pconst (24)%Z)))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (0)%Z)) (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z))
    ; copn [:: Lvar t_574.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (0)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)) (Pvar t_574))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z)))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (1)%Z)) (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z))
    ; copn [:: Lvar t_577.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (1)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)) (Pvar t_577))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z)))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (2)%Z)) (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z))
    ; copn [:: Lvar t_580.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)) (Pvar t_580))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (1)%Z)))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (3)%Z)) (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (4)%Z))
    ; copn [:: Lvar t_583.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)) (Pvar t_583))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (2)%Z)))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (4)%Z)) (aword U256) (Pget Aligned AAscale U256 c_571 (Pconst (0)%Z))
    ; copn [:: Lvar t_586.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 d_619.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)) (Pvar t_586))
    ; cassgn (Laset Aligned AAscale U256 d_619.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)) (Pget Aligned AAscale U256 c_571 (Pconst (3)%Z)))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (0)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (0)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (1)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (6)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)))
    ; copn [:: Lvar t_593.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (44)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_606.(gv) (Pconst (1)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (20)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)) (Pvar t_593))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (2)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (12)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)))
    ; copn [:: Lvar t_596.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (43)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_606.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (21)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)) (Pvar t_596))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (3)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (18)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)))
    ; copn [:: Lvar t_599.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (21)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_606.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (43)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)) (Pvar t_599))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (4)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (24)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)))
    ; copn [:: Lvar t_602.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (14)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_606.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (50)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_606.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)) (Pvar t_602))
    ; copn [:: Lvar t_607.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (2)%Z) ]
    ; cassgn (Lvar t_608.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_607) (Pget Aligned AAscale U256 b_606 (Pconst (0)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (0)%Z)) (aword U256) (Pvar t_608)
    ; copn [:: Lvar t_609.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (3)%Z) ]
    ; cassgn (Lvar t_610.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_609) (Pget Aligned AAscale U256 b_606 (Pconst (1)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (1)%Z)) (aword U256) (Pvar t_610)
    ; copn [:: Lvar t_611.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (4)%Z) ]
    ; cassgn (Lvar t_612.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_611) (Pget Aligned AAscale U256 b_606 (Pconst (2)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (2)%Z)) (aword U256) (Pvar t_612)
    ; copn [:: Lvar t_613.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (0)%Z) ]
    ; cassgn (Lvar t_614.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_613) (Pget Aligned AAscale U256 b_606 (Pconst (3)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (3)%Z)) (aword U256) (Pvar t_614)
    ; copn [:: Lvar t_615.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_606 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_606 (Pconst (1)%Z) ]
    ; cassgn (Lvar t_616.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_615) (Pget Aligned AAscale U256 b_606 (Pconst (4)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (4)%Z)) (aword U256) (Pvar t_616)
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (0)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (3)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)))
    ; copn [:: Lvar t_622.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (28)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (0)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (36)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)) (Pvar t_622))
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (1)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (9)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)))
    ; copn [:: Lvar t_625.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (20)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (1)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (44)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)) (Pvar t_625))
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (2)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (10)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)))
    ; copn [:: Lvar t_628.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (3)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (61)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)) (Pvar t_628))
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (3)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (16)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)))
    ; copn [:: Lvar t_631.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (45)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (19)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)) (Pvar t_631))
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (4)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (22)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)))
    ; copn [:: Lvar t_634.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (61)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_638.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (3)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_638.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)) (Pvar t_634))
    ; copn [:: Lvar t_639.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (2)%Z) ]
    ; cassgn (Lvar t_640.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_639) (Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (5)%Z)) (aword U256) (Pvar t_640)
    ; copn [:: Lvar t_641.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (3)%Z) ]
    ; cassgn (Lvar t_642.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_641) (Pget Aligned AAscale U256 b_638 (Pconst (1)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (6)%Z)) (aword U256) (Pvar t_642)
    ; copn [:: Lvar t_643.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (4)%Z) ]
    ; cassgn (Lvar t_644.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_643) (Pget Aligned AAscale U256 b_638 (Pconst (2)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (7)%Z)) (aword U256) (Pvar t_644)
    ; copn [:: Lvar t_645.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (0)%Z) ]
    ; cassgn (Lvar t_646.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_645) (Pget Aligned AAscale U256 b_638 (Pconst (3)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (8)%Z)) (aword U256) (Pvar t_646)
    ; copn [:: Lvar t_647.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_638 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_638 (Pconst (1)%Z) ]
    ; cassgn (Lvar t_648.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_647) (Pget Aligned AAscale U256 b_638 (Pconst (4)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (9)%Z)) (aword U256) (Pvar t_648)
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (0)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (1)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)))
    ; copn [:: Lvar t_655.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (1)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (0)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (63)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)) (Pvar t_655))
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (1)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (7)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)))
    ; copn [:: Lvar t_658.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (6)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (1)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (58)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)) (Pvar t_658))
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (2)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (13)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)))
    ; copn [:: Lvar t_661.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (25)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (39)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)) (Pvar t_661))
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (3)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (19)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)))
    ; copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (3)%Z)
                                                                    ; Pvar r8 ]
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (4)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (20)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)))
    ; copn [:: Lvar t_667.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (18)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_671.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (46)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_671.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)) (Pvar t_667))
    ; copn [:: Lvar t_672.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (2)%Z) ]
    ; cassgn (Lvar t_673.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_672) (Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (10)%Z)) (aword U256) (Pvar t_673)
    ; copn [:: Lvar t_674.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (3)%Z) ]
    ; cassgn (Lvar t_675.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_674) (Pget Aligned AAscale U256 b_671 (Pconst (1)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (11)%Z)) (aword U256) (Pvar t_675)
    ; copn [:: Lvar t_676.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (4)%Z) ]
    ; cassgn (Lvar t_677.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_676) (Pget Aligned AAscale U256 b_671 (Pconst (2)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (12)%Z)) (aword U256) (Pvar t_677)
    ; copn [:: Lvar t_678.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (0)%Z) ]
    ; cassgn (Lvar t_679.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_678) (Pget Aligned AAscale U256 b_671 (Pconst (3)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (13)%Z)) (aword U256) (Pvar t_679)
    ; copn [:: Lvar t_680.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_671 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_671 (Pconst (1)%Z) ]
    ; cassgn (Lvar t_681.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_680) (Pget Aligned AAscale U256 b_671 (Pconst (4)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (14)%Z)) (aword U256) (Pvar t_681)
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (0)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (4)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)))
    ; copn [:: Lvar t_688.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (27)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (0)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (37)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)) (Pvar t_688))
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (1)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (5)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)))
    ; copn [:: Lvar t_691.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (36)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (1)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (28)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)) (Pvar t_691))
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (2)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (11)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)))
    ; copn [:: Lvar t_694.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (10)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (54)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)) (Pvar t_694))
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (3)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (17)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)))
    ; copn [:: Lvar t_697.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (15)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (49)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)) (Pvar t_697))
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (4)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (23)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_704.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_704 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)))
    ; copn [:: Laset Aligned AAscale U256 b_704.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (4)%Z)
                                                                    ; Pvar r56 ]
    ; copn [:: Lvar t_705.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (2)%Z) ]
    ; cassgn (Lvar t_706.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_705) (Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (15)%Z)) (aword U256) (Pvar t_706)
    ; copn [:: Lvar t_707.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (3)%Z) ]
    ; cassgn (Lvar t_708.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_707) (Pget Aligned AAscale U256 b_704 (Pconst (1)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (16)%Z)) (aword U256) (Pvar t_708)
    ; copn [:: Lvar t_709.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (4)%Z) ]
    ; cassgn (Lvar t_710.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_709) (Pget Aligned AAscale U256 b_704 (Pconst (2)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (17)%Z)) (aword U256) (Pvar t_710)
    ; copn [:: Lvar t_711.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (0)%Z) ]
    ; cassgn (Lvar t_712.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_711) (Pget Aligned AAscale U256 b_704 (Pconst (3)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (18)%Z)) (aword U256) (Pvar t_712)
    ; copn [:: Lvar t_713.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_704 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_704 (Pconst (1)%Z) ]
    ; cassgn (Lvar t_714.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_713) (Pget Aligned AAscale U256 b_704 (Pconst (4)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (19)%Z)) (aword U256) (Pvar t_714)
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (0)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (2)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (2)%Z)))
    ; copn [:: Lvar t_720.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (62)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (0)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (2)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (0)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)) (Pvar t_720))
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (1)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (8)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (3)%Z)))
    ; copn [:: Lvar t_723.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (55)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (1)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (9)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (1)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)) (Pvar t_723))
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (2)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (14)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (4)%Z)))
    ; copn [:: Lvar t_726.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (39)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (2)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (25)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (2)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)) (Pvar t_726))
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (3)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (15)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (0)%Z)))
    ; copn [:: Lvar t_729.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (41)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (3)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (23)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (3)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)) (Pvar t_729))
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (4)%Z)) (aword U256) (Pget Aligned AAscale U256 a_18660 (Pconst (21)%Z))
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olxor U256) (Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)) (Pget Aligned AAscale U256 d_619 (Pconst (1)%Z)))
    ; copn [:: Lvar t_732.(gv) ] (Oasm ((BaseOp ((None), (VPSLL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (2)%Z) ]
    ; copn [:: Laset Aligned AAscale U256 b_736.(gv) (Pconst (4)%Z) ] (Oasm ((BaseOp ((None), (VPSRL VE64 U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)
                                                                    ; Papp1 (Oword_of_int U128) (Pconst (62)%Z) ]
    ; cassgn (Laset Aligned AAscale U256 b_736.(gv) (Pconst (4)%Z)) (aword U256) (Papp2 (Olor U256) (Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)) (Pvar t_732))
    ; copn [:: Lvar t_737.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (2)%Z) ]
    ; cassgn (Lvar t_738.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_737) (Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (20)%Z)) (aword U256) (Pvar t_738)
    ; copn [:: Lvar t_739.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (3)%Z) ]
    ; cassgn (Lvar t_740.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_739) (Pget Aligned AAscale U256 b_736 (Pconst (1)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (21)%Z)) (aword U256) (Pvar t_740)
    ; copn [:: Lvar t_741.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (4)%Z) ]
    ; cassgn (Lvar t_742.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_741) (Pget Aligned AAscale U256 b_736 (Pconst (2)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (22)%Z)) (aword U256) (Pvar t_742)
    ; copn [:: Lvar t_743.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (0)%Z) ]
    ; cassgn (Lvar t_744.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_743) (Pget Aligned AAscale U256 b_736 (Pconst (3)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (23)%Z)) (aword U256) (Pvar t_744)
    ; copn [:: Lvar t_745.(gv) ] (Oasm ((BaseOp ((None), (VPANDN U256))))) [:: Pget Aligned AAscale U256 b_736 (Pconst (0)%Z)
                                                                    ; Pget Aligned AAscale U256 b_736 (Pconst (1)%Z) ]
    ; cassgn (Lvar t_746.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar t_745) (Pget Aligned AAscale U256 b_736 (Pconst (4)%Z)))
    ; cassgn (Laset Aligned AAscale U256 e.(gv) (Pconst (24)%Z)) (aword U256) (Pvar t_746) ].

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
