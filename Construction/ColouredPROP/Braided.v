Require Import Category.Lib.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CFreeBraided.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cfree_braid_square {x y z w : list Colour}
  (g : CTerm S x y) (h : CTerm S z w) :
  CTermEq S
    (CT_comp (CT_comp (CT_tens h (CT_id y)) (CT_tens (CT_id z) g))
             (CT_braid x z))
    (CT_comp (CT_comp (CT_braid y w) (CT_tens (CT_id y) h))
             (CT_tens g (CT_id z))).
Proof.
  apply CTE_trans with (CT_comp (CT_tens h g) (CT_braid x z)).
  - apply CTE_comp_cong.
    + apply ctens_fuse_l.
    + apply CTE_refl.
  - apply CTE_trans with (CT_comp (CT_braid y w) (CT_tens g h)).
    + apply CTE_braid_natural.
    + apply CTE_sym.
      apply CTE_trans with
        (CT_comp (CT_braid y w)
                 (CT_comp (CT_tens (CT_id y) h) (CT_tens g (CT_id z)))).
      * apply CTE_assoc.
      * apply CTE_comp_cong.
        -- apply CTE_refl.
        -- apply ctens_fuse_r.
Qed.

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cbraid_hex_right_cast (x y z : list Colour) :
  CTermEq S
    (CT_comp (CT_cast (eq_sym (app_assoc y z x))) (CT_braid x (y ++ z)))
    (CT_comp (CT_comp (CT_tens (CT_id y) (CT_braid x z))
                      (CT_cast (eq_sym (app_assoc y x z))))
             (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                      (CT_cast (app_assoc x y z)))).
Proof.
  apply CTE_trans with
    (eq_rect ((y ++ z) ++ x)
             (fun t => CTerm S (x ++ (y ++ z)) t)
             (CT_braid x (y ++ z))
             (y ++ (z ++ x))
             (eq_sym (app_assoc y z x))).
  - apply CTE_sym, ceq_rect_cod_cast.
  - apply CTE_trans with
      (CT_comp
         (eq_rect (y ++ (x ++ z))
                  (fun s => CTerm S s (y ++ (z ++ x)))
                  (CT_tens (CT_id y) (CT_braid x z))
                  ((y ++ x) ++ z)
                  (app_assoc y x z))
         (eq_rect ((x ++ y) ++ z)
                  (fun s => CTerm S s ((y ++ x) ++ z))
                  (CT_tens (CT_braid x y) (CT_id z))
                  (x ++ (y ++ z))
                  (eq_sym (app_assoc x y z)))).
    + apply CTE_braid_hex_right.
    + apply CTE_comp_cong.
      * apply ceq_rect_dom_cast.
      * rewrite <- (CT_cast_sym_sym S (app_assoc x y z)).
        apply ceq_rect_dom_cast.
Qed.

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cfree_hexagon (x y z : list Colour) :
  CTermEq S
    (CT_comp (CT_comp (CT_cast (eq_sym (app_assoc y z x)))
                      (CT_braid x (y ++ z)))
             (CT_cast (eq_sym (app_assoc x y z))))
    (CT_comp (CT_comp (CT_tens (CT_id y) (CT_braid x z))
                      (CT_cast (eq_sym (app_assoc y x z))))
             (CT_tens (CT_braid x y) (CT_id z))).
Proof.
  apply CTE_trans with
    (CT_comp (CT_comp (CT_comp (CT_tens (CT_id y) (CT_braid x z))
                               (CT_cast (eq_sym (app_assoc y x z))))
                      (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                               (CT_cast (app_assoc x y z))))
             (CT_cast (eq_sym (app_assoc x y z)))).
  - apply CTE_comp_cong.
    + apply cbraid_hex_right_cast.
    + apply CTE_refl.
  - apply CTE_trans with
      (CT_comp (CT_comp (CT_tens (CT_id y) (CT_braid x z))
                        (CT_cast (eq_sym (app_assoc y x z))))
               (CT_comp (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                                 (CT_cast (app_assoc x y z)))
                        (CT_cast (eq_sym (app_assoc x y z))))).
    + apply CTE_assoc.
    + apply CTE_comp_cong.
      * apply CTE_refl.
      * apply CTE_trans with
          (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                   (CT_comp (CT_cast (app_assoc x y z))
                            (CT_cast (eq_sym (app_assoc x y z))))).
        -- apply CTE_assoc.
        -- apply CTE_trans with
             (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                      (CT_id ((x ++ y) ++ z))).
           ++ apply CTE_comp_cong.
              ** apply CTE_refl.
              ** apply CT_cast_inv.
           ++ apply CTE_id_right.
Qed.

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cbraid_hex_left_cast (x y z : list Colour) :
  CTermEq S
    (CT_comp (CT_braid (x ++ y) z) (CT_cast (app_assoc x y z)))
    (CT_comp (CT_comp (CT_cast (eq_sym (app_assoc z x y)))
                      (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                               (CT_cast (app_assoc x z y))))
             (CT_tens (CT_id x) (CT_braid y z))).
Proof.
  apply CTE_trans with
    (eq_rect ((x ++ y) ++ z)
             (fun s => CTerm S s (z ++ (x ++ y)))
             (CT_braid (x ++ y) z)
             (x ++ (y ++ z))
             (eq_sym (app_assoc x y z))).
  - apply CTE_sym.
    rewrite <- (CT_cast_sym_sym S (app_assoc x y z)).
    apply ceq_rect_dom_cast.
  - apply CTE_trans with
      (CT_comp
         (eq_rect ((z ++ x) ++ y)
                  (fun t => CTerm S (x ++ (z ++ y)) t)
                  (eq_rect ((x ++ z) ++ y)
                           (fun s => CTerm S s ((z ++ x) ++ y))
                           (CT_tens (CT_braid x z) (CT_id y))
                           (x ++ (z ++ y))
                           (eq_sym (app_assoc x z y)))
                  (z ++ (x ++ y))
                  (eq_sym (app_assoc z x y)))
         (CT_tens (CT_id x) (CT_braid y z))).
    + apply CTE_braid_hex_left.
    + apply CTE_comp_cong.
      * apply CTE_trans with
          (CT_comp (CT_cast (eq_sym (app_assoc z x y)))
                   (eq_rect ((x ++ z) ++ y)
                            (fun s => CTerm S s ((z ++ x) ++ y))
                            (CT_tens (CT_braid x z) (CT_id y))
                            (x ++ (z ++ y))
                            (eq_sym (app_assoc x z y)))).
        -- apply ceq_rect_cod_cast.
        -- apply CTE_comp_cong.
           ++ apply CTE_refl.
           ++ rewrite <- (CT_cast_sym_sym S (app_assoc x z y)).
              apply ceq_rect_dom_cast.
      * apply CTE_refl.
Qed.

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cfree_hexagon_sym (x y z : list Colour) :
  CTermEq S
    (CT_comp (CT_comp (CT_cast (app_assoc z x y)) (CT_braid (x ++ y) z))
             (CT_cast (app_assoc x y z)))
    (CT_comp (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                      (CT_cast (app_assoc x z y)))
             (CT_tens (CT_id x) (CT_braid y z))).
Proof.
  apply CTE_trans with
    (CT_comp (CT_cast (app_assoc z x y))
             (CT_comp (CT_braid (x ++ y) z) (CT_cast (app_assoc x y z)))).
  - apply CTE_assoc.
  - apply CTE_trans with
      (CT_comp (CT_cast (app_assoc z x y))
               (CT_comp (CT_comp (CT_cast (eq_sym (app_assoc z x y)))
                                 (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                                          (CT_cast (app_assoc x z y))))
                        (CT_tens (CT_id x) (CT_braid y z)))).
    + apply CTE_comp_cong.
      * apply CTE_refl.
      * apply cbraid_hex_left_cast.
    + apply CTE_trans with
        (CT_comp (CT_comp (CT_cast (app_assoc z x y))
                          (CT_comp (CT_cast (eq_sym (app_assoc z x y)))
                                   (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                                            (CT_cast (app_assoc x z y)))))
                 (CT_tens (CT_id x) (CT_braid y z))).
      * apply CTE_sym, CTE_assoc.
      * apply CTE_comp_cong.
        -- apply CTE_trans with
             (CT_comp (CT_comp (CT_cast (app_assoc z x y))
                               (CT_cast (eq_sym (app_assoc z x y))))
                      (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                               (CT_cast (app_assoc x z y)))).
           ++ apply CTE_sym, CTE_assoc.
           ++ apply CTE_trans with
                (CT_comp (CT_id ((z ++ x) ++ y))
                         (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                                  (CT_cast (app_assoc x z y)))).
              ** apply CTE_comp_cong.
                 --- apply CT_cast_inv.
                 --- apply CTE_refl.
              ** apply CTE_id_left.
        -- apply CTE_refl.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CFreeCat_Braided : @BraidedMonoidal (CFreeCat S) :=
  @Build_BraidedMonoidal (CFreeCat S)
    (CFreeCat_Monoidal S Cdec)
    (fun cs ds => CT_braid cs ds)
    (fun x y g z w h => cfree_braid_square g h)
    (fun x y z => cfree_hexagon x y z)
    (fun x y z => cfree_hexagon_sym x y z).

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cfree_braid_invol (x y : list Colour) :
  CTermEq S (CT_comp (CT_braid y x) (CT_braid x y)) (CT_id (x ++ y)).
Proof.
  apply CTE_braid_invol.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CFreeCat_Symmetric : @SymmetricMonoidal (CFreeCat S) :=
  @Build_SymmetricMonoidal (CFreeCat S)
    CFreeCat_Braided
    (fun x y => cfree_braid_invol x y).

End CFreeBraided.

Arguments CFreeCat_Braided {Colour} S Cdec : assert.
Arguments CFreeCat_Symmetric {Colour} S Cdec : assert.
