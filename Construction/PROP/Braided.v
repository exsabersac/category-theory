Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Monoidal.

From Coq Require Import Arith.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeBraided.

Context (S : Signature).

Open Scope nat_scope.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma free_braid_square {x y z w : nat} (g : Term S x y) (h : Term S z w) :
  TermEq S
    (T_comp (T_comp (T_tens h (T_id y)) (T_tens (T_id z) g)) (T_braid x z))
    (T_comp (T_comp (T_braid y w) (T_tens (T_id y) h)) (T_tens g (T_id z))).
Proof.
  apply TE_trans with (T_comp (T_tens h g) (T_braid x z)).
  - apply TE_comp_cong.
    + apply tens_fuse_l.
    + apply TE_refl.
  - apply TE_trans with (T_comp (T_braid y w) (T_tens g h)).
    + apply TE_braid_natural.
    + apply TE_sym.
      apply TE_trans with
        (T_comp (T_braid y w)
                (T_comp (T_tens (T_id y) h) (T_tens g (T_id z)))).
      * apply TE_assoc.
      * apply TE_comp_cong.
        -- apply TE_refl.
        -- apply tens_fuse_r.
Qed.

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma braid_hex_right_cast (x y z : nat) :
  TermEq S
    (T_comp (T_cast (eq_sym (Nat.add_assoc y z x))) (T_braid x (y + z)))
    (T_comp (T_comp (T_tens (T_id y) (T_braid x z))
                    (T_cast (eq_sym (Nat.add_assoc y x z))))
            (T_comp (T_tens (T_braid x y) (T_id z))
                    (T_cast (Nat.add_assoc x y z)))).
Proof.
  apply TE_trans with
    (eq_rect ((y + z) + x)
             (fun t => Term S (x + (y + z)) t)
             (T_braid x (y + z))
             (y + (z + x))
             (eq_sym (Nat.add_assoc y z x))).
  - apply TE_sym, eq_rect_cod_cast.
  - apply TE_trans with
      (T_comp
         (eq_rect (y + (x + z))
                  (fun s => Term S s (y + (z + x)))
                  (T_tens (T_id y) (T_braid x z))
                  ((y + x) + z)
                  (Nat.add_assoc y x z))
         (eq_rect ((x + y) + z)
                  (fun s => Term S s ((y + x) + z))
                  (T_tens (T_braid x y) (T_id z))
                  (x + (y + z))
                  (eq_sym (Nat.add_assoc x y z)))).
    + apply TE_braid_hex_right.
    + apply TE_comp_cong.
      * apply eq_rect_dom_cast.
      * rewrite <- (T_cast_sym_sym S (Nat.add_assoc x y z)).
        apply eq_rect_dom_cast.
Qed.

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma free_hexagon (x y z : nat) :
  TermEq S
    (T_comp (T_comp (T_cast (eq_sym (Nat.add_assoc y z x)))
                    (T_braid x (y + z)))
            (T_cast (eq_sym (Nat.add_assoc x y z))))
    (T_comp (T_comp (T_tens (T_id y) (T_braid x z))
                    (T_cast (eq_sym (Nat.add_assoc y x z))))
            (T_tens (T_braid x y) (T_id z))).
Proof.
  apply TE_trans with
    (T_comp (T_comp (T_comp (T_tens (T_id y) (T_braid x z))
                            (T_cast (eq_sym (Nat.add_assoc y x z))))
                    (T_comp (T_tens (T_braid x y) (T_id z))
                            (T_cast (Nat.add_assoc x y z))))
            (T_cast (eq_sym (Nat.add_assoc x y z)))).
  - apply TE_comp_cong.
    + apply braid_hex_right_cast.
    + apply TE_refl.
  - apply TE_trans with
      (T_comp (T_comp (T_tens (T_id y) (T_braid x z))
                      (T_cast (eq_sym (Nat.add_assoc y x z))))
              (T_comp (T_comp (T_tens (T_braid x y) (T_id z))
                              (T_cast (Nat.add_assoc x y z)))
                      (T_cast (eq_sym (Nat.add_assoc x y z))))).
    + apply TE_assoc.
    + apply TE_comp_cong.
      * apply TE_refl.
      * apply TE_trans with
          (T_comp (T_tens (T_braid x y) (T_id z))
                  (T_comp (T_cast (Nat.add_assoc x y z))
                          (T_cast (eq_sym (Nat.add_assoc x y z))))).
        -- apply TE_assoc.
        -- apply TE_trans with
             (T_comp (T_tens (T_braid x y) (T_id z))
                     (T_id ((x + y) + z))).
           ++ apply TE_comp_cong.
              ** apply TE_refl.
              ** apply T_cast_inv_sym.
           ++ apply TE_id_right.
Qed.

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma braid_hex_left_cast (x y z : nat) :
  TermEq S
    (T_comp (T_braid (x + y) z) (T_cast (Nat.add_assoc x y z)))
    (T_comp (T_comp (T_cast (eq_sym (Nat.add_assoc z x y)))
                    (T_comp (T_tens (T_braid x z) (T_id y))
                            (T_cast (Nat.add_assoc x z y))))
            (T_tens (T_id x) (T_braid y z))).
Proof.
  apply TE_trans with
    (eq_rect ((x + y) + z)
             (fun s => Term S s (z + (x + y)))
             (T_braid (x + y) z)
             (x + (y + z))
             (eq_sym (Nat.add_assoc x y z))).
  - apply TE_sym.
    rewrite <- (T_cast_sym_sym S (Nat.add_assoc x y z)).
    apply eq_rect_dom_cast.
  - apply TE_trans with
      (T_comp
         (eq_rect ((z + x) + y)
                  (fun t => Term S (x + (z + y)) t)
                  (eq_rect ((x + z) + y)
                           (fun s => Term S s ((z + x) + y))
                           (T_tens (T_braid x z) (T_id y))
                           (x + (z + y))
                           (eq_sym (Nat.add_assoc x z y)))
                  (z + (x + y))
                  (eq_sym (Nat.add_assoc z x y)))
         (T_tens (T_id x) (T_braid y z))).
    + apply TE_braid_hex_left.
    + apply TE_comp_cong.
      * apply TE_trans with
          (T_comp (T_cast (eq_sym (Nat.add_assoc z x y)))
                  (eq_rect ((x + z) + y)
                           (fun s => Term S s ((z + x) + y))
                           (T_tens (T_braid x z) (T_id y))
                           (x + (z + y))
                           (eq_sym (Nat.add_assoc x z y)))).
        -- apply eq_rect_cod_cast.
        -- apply TE_comp_cong.
           ++ apply TE_refl.
           ++ rewrite <- (T_cast_sym_sym S (Nat.add_assoc x z y)).
              apply eq_rect_dom_cast.
      * apply TE_refl.
Qed.

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma free_hexagon_sym (x y z : nat) :
  TermEq S
    (T_comp (T_comp (T_cast (Nat.add_assoc z x y)) (T_braid (x + y) z))
            (T_cast (Nat.add_assoc x y z)))
    (T_comp (T_comp (T_tens (T_braid x z) (T_id y))
                    (T_cast (Nat.add_assoc x z y)))
            (T_tens (T_id x) (T_braid y z))).
Proof.
  apply TE_trans with
    (T_comp (T_cast (Nat.add_assoc z x y))
            (T_comp (T_braid (x + y) z) (T_cast (Nat.add_assoc x y z)))).
  - apply TE_assoc.
  - apply TE_trans with
      (T_comp (T_cast (Nat.add_assoc z x y))
              (T_comp (T_comp (T_cast (eq_sym (Nat.add_assoc z x y)))
                              (T_comp (T_tens (T_braid x z) (T_id y))
                                      (T_cast (Nat.add_assoc x z y))))
                      (T_tens (T_id x) (T_braid y z)))).
    + apply TE_comp_cong.
      * apply TE_refl.
      * apply braid_hex_left_cast.
    + apply TE_trans with
        (T_comp (T_comp (T_cast (Nat.add_assoc z x y))
                        (T_comp (T_cast (eq_sym (Nat.add_assoc z x y)))
                                (T_comp (T_tens (T_braid x z) (T_id y))
                                        (T_cast (Nat.add_assoc x z y)))))
                (T_tens (T_id x) (T_braid y z))).
      * apply TE_sym, TE_assoc.
      * apply TE_comp_cong.
        -- apply TE_trans with
             (T_comp (T_comp (T_cast (Nat.add_assoc z x y))
                             (T_cast (eq_sym (Nat.add_assoc z x y))))
                     (T_comp (T_tens (T_braid x z) (T_id y))
                             (T_cast (Nat.add_assoc x z y)))).
           ++ apply TE_sym, TE_assoc.
           ++ apply TE_trans with
                (T_comp (T_id ((z + x) + y))
                        (T_comp (T_tens (T_braid x z) (T_id y))
                                (T_cast (Nat.add_assoc x z y)))).
              ** apply TE_comp_cong.
                 --- apply T_cast_inv_sym.
                 --- apply TE_refl.
              ** apply TE_id_left.
        -- apply TE_refl.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreeCat_Braided : @BraidedMonoidal (FreeCat S) := {|
  braided_is_monoidal := FreeCat_Monoidal S;
  braid := fun m n => T_braid m n;
  braid_natural := fun x y g z w h => free_braid_square g h;
  hexagon_identity := fun x y z => free_hexagon x y z;
  hexagon_identity_sym := fun x y z => free_hexagon_sym x y z
|}.

End FreeBraided.

Arguments FreeCat_Braided S : assert.
