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

(** * The braided and symmetric monoidal structures on the free coloured PROP *)

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

(** ** Braid naturality in [ArityTwo] form

    The [braid_natural] field of [BraidedMonoidal] unfolds, through
    the [Mapping] instances of [Structure/Monoidal/Naturality.v], to
    the square below: each side tensors one morphism against a
    half-identity before composing with the braid.  [ctens_fuse_l]
    collapses the left-hand pair to [h ⊕c g] and [ctens_fuse_r] the
    right-hand pair to [g ⊕c h], after which the square is exactly
    [CTE_braid_natural]. *)

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

(** ** The right hexagon in [CT_cast] form

    [CTE_braid_hex_right x y z] asserts the hexagon for [σ_{x,y++z}]
    with its boundary mismatches carried by [eq_rect] transports over
    [app_assoc] equations.  Converting the codomain transport on the
    left-hand side by [ceq_rect_cod_cast] and the two domain
    transports on the right-hand side by [ceq_rect_dom_cast] (plus
    [CT_cast_sym_sym] to erase a double [eq_sym]) restates the axiom
    purely in terms of [CT_cast] composites. *)

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

(** ** First hexagon identity

    The [hexagon_identity] field of [BraidedMonoidal] at [x y z],
    with every associator spelled as the [CT_cast] of the matching
    [app_assoc] equation (the [to] direction is the [eq_sym] cast,
    per [CFreeCat_tensor_assoc]).  Post-composing both sides of
    [cbraid_hex_right_cast] with the incoming associator and
    cancelling the resulting cast-inverse pair by [CT_cast_inv]
    yields the class field verbatim. *)

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

(** ** The left hexagon in [CT_cast] form

    Mirror bridge: [CTE_braid_hex_left x y z] is the hexagon for
    [σ_{x++y,z}], and its transports convert by the same three
    bridges.  Here the inverse associators appear, so the casts are
    the forward [app_assoc] equations (the [from] direction of
    [CFreeCat_tensor_assoc]). *)

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

(** ** Second hexagon identity

    The [hexagon_identity_sym] field of [BraidedMonoidal] at [x y z],
    phrased through the inverse associators.  Pre-composing both
    sides of [cbraid_hex_left_cast] with the outgoing inverse
    associator [CT_cast (app_assoc z x y)], reassociating, and
    cancelling the cast-inverse pair by [CT_cast_inv] gives the class
    field. *)

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

(** ** THE BraidedMonoidal record on [CFreeCat S]

    [braided_is_monoidal] names the ONE shared [Monoidal] record
    [CFreeCat_Monoidal S Cdec]; the braid is [CT_braid] (recall that
    on objects the tensor is [++], so [cs ⨂ ds] and [cs ++ ds] agree
    definitionally); all proof fields are the standalone lemmas
    above.  The record is an explicit [Build_BraidedMonoidal]
    application, so no Program obligations are generated and no
    inference is left to a record literal. *)

Definition CFreeCat_Braided : @BraidedMonoidal (CFreeCat S) :=
  @Build_BraidedMonoidal (CFreeCat S)
    (CFreeCat_Monoidal S Cdec)
    (fun cs ds => CT_braid cs ds)
    (fun x y g z w h => cfree_braid_square g h)
    (fun x y z => cfree_hexagon x y z)
    (fun x y z => cfree_hexagon_sym x y z).

(** ** Braid involution

    The [braid_invol] field of [SymmetricMonoidal] at [x y]: the
    composite [σ_{y,x} ⊙c σ_{x,y} : x ++ y ⇒ x ++ y] is the identity.
    This is the primitive constructor [CTE_braid_invol] applied at
    [cs := x], [ds := y]. *)

Lemma cfree_braid_invol (x y : list Colour) :
  CTermEq S (CT_comp (CT_braid y x) (CT_braid x y)) (CT_id (x ++ y)).
Proof.
  apply CTE_braid_invol.
Qed.

(** ** THE SymmetricMonoidal record on [CFreeCat S]

    A coloured PROP is a SYMMETRIC strict monoidal category, so the
    braiding installed above must be its own inverse.
    [symmetric_is_braided] names the ONE braided record
    [CFreeCat_Braided] (hence, through it, the ONE shared [Monoidal]
    record [CFreeCat_Monoidal S Cdec]); the involution proof is the
    standalone lemma above. *)

Definition CFreeCat_Symmetric : @SymmetricMonoidal (CFreeCat S) :=
  @Build_SymmetricMonoidal (CFreeCat S)
    CFreeCat_Braided
    (fun x y => cfree_braid_invol x y).

End CFreeBraided.

Arguments CFreeCat_Braided {Colour} S Cdec : assert.
Arguments CFreeCat_Symmetric {Colour} S Cdec : assert.
