Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Functor.Hom.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/local+object
         https://ncatlab.org/nlab/show/reflective+subcategory
         https://ncatlab.org/nlab/show/localization

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于localization的来源与用途

   nLab:  https://ncatlab.org/nlab/show/localization
   https://ncatlab.org/nlab/show/reflective+localization
   https://ncatlab.org/nlab/show/orthogonal+subcategory+problem
   Wikipedia:
   https://en.wikipedia.org/wiki/Localization_(commutative_algebra)

   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition WLocal {C : Category} (W : MorphismClass C) (x : C) : Type :=
  ∀ (a b : C) (w : a ~> b), W a b w →
    IsIsomorphism (@fmap (C^op) Sets (Curried_CoHom C x) b a w).

(* From W-locality, two elementary hom-set facts used downstream: the
 precomposition [(- ∘ w)] W-local 对象 split-surjective ... （已译） *)

Lemma WLocal_surj {C : Category} {W : MorphismClass C} {x : C} (Hx : WLocal W x)
      {a b : C} (w : a ~> b) (Hw : W a b w) (p : a ~> x) :
  { q : b ~> x & q ∘ w ≈ p }.
Proof.
  destruct (Hx a b w Hw) as [phi Hr Hl].
  exists (phi p).
  exact (Hr p).
Qed.

(* ... and injective. *)

Lemma WLocal_inj {C : Category} {W : MorphismClass C} {x : C} (Hx : WLocal W x)
      {a b : C} (w : a ~> b) (Hw : W a b w) (g1 g2 : b ~> x) :
  g1 ∘ w ≈ g2 ∘ w → g1 ≈ g2.
Proof.
  destruct (Hx a b w Hw) as [phi Hr Hl].
  intro Heq.
  transitivity (phi (g1 ∘ w)).
  - symmetry. exact (Hl g1).
  - transitivity (phi (g2 ∘ w)).
    + apply (proper_morphism phi). exact Heq.
    + exact (Hl g2).
Qed.

(* The full subcategory W-local 对象. Objects W-local ones;
 every C-态射 between them retained ([shom := True]), so 复合
 identities closed trivially. （已译） *)

Definition C_W {C : Category} (W : MorphismClass C) : Subcategory C :=
  {| sobj  := fun x => WLocal W x
   ; shom  := fun x y ox oy f => True
   ; scomp := fun x y z ox oy oz f g _ _ => I
   ; sid   := fun x ox => I |}.

(* The subcategory C_W full: every 态射 between W-local 对象 it
 ([shom] witness [I]). （已译） *)

Definition Full_C_W {C : Category} (W : MorphismClass C) :
  Construction.Subcategory.Full C (C_W W) :=
  fun x y ox oy f => I.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma unit_at_local_iso {C : Category} {W : MorphismClass C}
      (R : Reflective (C_W W)) (s : Sub C (C_W W)) :
  IsIsomorphism
    (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
       (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)).
Proof.
  (* zeta : unit at [Incl s], lifted 进入 subcategory fullness. （已译） *)
  pose (zeta := (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
                   (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)
                 ; reflective_full R (Incl C (C_W W) s)
                     (Incl C (C_W W) (reflector R (Incl C (C_W W) s)))
                     (`2 s) (`2 (reflector R (Incl C (C_W W) s)))
                     (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
                        (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)))
                : s ~{Sub C (C_W W)}~> reflector R (Incl C (C_W W) s)).
  (* 相关说明。 （已译） *)
  assert (Hlaw2 : zeta ∘ (@counit (Sub C (C_W W)) C (reflector R)
                            (Incl C (C_W W)) (reflective_adj R) s) ≈ id).
  { rewrite <- (counit_naturality (reflective_adj R)).
    apply (@counit_fmap_unit (Sub C (C_W W)) C (reflector R)
             (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)). }
  unshelve econstructor.
  - (* the inverse: 含入 counit （已译） *)
    exact (fmap[Incl C (C_W W)]
             (@counit (Sub C (C_W W)) C (reflector R)
                (Incl C (C_W W)) (reflective_adj R) s)).
  - (* is_right_inverse: η ∘ fmap[Incl] counit ≈ id *)
    change (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
              (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s))
      with (fmap[Incl C (C_W W)] zeta).
    rewrite <- fmap_comp.
    rewrite Hlaw2.
    apply fmap_id.
  - (* is_left_inverse: fmap[Incl] counit ∘ η ≈ id, a triangle identity *)
    apply (@fmap_counit_unit (Sub C (C_W W)) C (reflector R)
             (Incl C (C_W W)) (reflective_adj R) s).
Qed.

(*
   本节说明伴随、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Inverts.
Context {C : Category} {W : MorphismClass C}.
Context (R : Reflective (C_W W)).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Notation Su   := (Sub C (C_W W)).
Local Notation Iota := (Incl C (C_W W)).
Local Notation Refl := (reflector R).
Local Notation A    := (reflective_adj R).

Theorem reflector_inverts_W {a b : C} (w : a ~> b) (Hw : W a b w) :
  IsIsomorphism (fmap[Refl] w).
Proof.
  (* 相关说明。 （已译） *)
  destruct (WLocal_surj (`2 (Refl a)) w Hw
              (@Category.Theory.Adjunction.unit Su C Refl Iota A a)) as [q Hq].
  (* the candidate inverse, transposed back 进入 subcategory （已译） *)
  assert (Hli : from (@adj Su C Refl Iota A b (Refl a)) q ∘ fmap[Refl] w ≈ id).
  { transitivity
      (from (@adj Su C Refl Iota A a (Refl a))
        (to (@adj Su C Refl Iota A a (Refl a))
           (from (@adj Su C Refl Iota A b (Refl a)) q ∘ fmap[Refl] w))).
    { symmetry. apply (@to_adj_comp_law Su C Refl Iota A a (Refl a)). }
    transitivity
      (from (@adj Su C Refl Iota A a (Refl a))
        (to (@adj Su C Refl Iota A a (Refl a)) id)).
    2:{ apply (@to_adj_comp_law Su C Refl Iota A a (Refl a)). }
    apply (proper_morphism (from (@adj Su C Refl Iota A a (Refl a)))).
    rewrite (@to_adj_nat_l Su C Refl Iota A a b (Refl a)
               (from (@adj Su C Refl Iota A b (Refl a)) q) w).
    rewrite (@from_adj_comp_law Su C Refl Iota A b (Refl a) q).
    exact Hq. }
  unshelve refine {| two_sided_inverse := from (@adj Su C Refl Iota A b (Refl a)) q |}.
  - (* is_right_inverse: fmap[Refl] w ∘ ⌈q⌉ ≈ id *)
    transitivity
      (from (@adj Su C Refl Iota A b (Refl b))
        (to (@adj Su C Refl Iota A b (Refl b))
           (fmap[Refl] w ∘ from (@adj Su C Refl Iota A b (Refl a)) q))).
    { symmetry. apply (@to_adj_comp_law Su C Refl Iota A b (Refl b)). }
    transitivity
      (from (@adj Su C Refl Iota A b (Refl b))
        (to (@adj Su C Refl Iota A b (Refl b)) id)).
    2:{ apply (@to_adj_comp_law Su C Refl Iota A b (Refl b)). }
    apply (proper_morphism (from (@adj Su C Refl Iota A b (Refl b)))).
    apply (WLocal_inj (`2 (Refl b)) w Hw).
    rewrite <- (@to_adj_nat_l Su C Refl Iota A a b (Refl b)
                 (fmap[Refl] w ∘ from (@adj Su C Refl Iota A b (Refl a)) q) w).
    rewrite <- (@to_adj_nat_l Su C Refl Iota A a b (Refl b) id w).
    apply (proper_morphism (to (@adj Su C Refl Iota A a (Refl b)))).
    rewrite id_left.
    rewrite <- comp_assoc.
    rewrite Hli.
    rewrite id_right.
    reflexivity.
  - (* is_left_inverse: ⌈q⌉ ∘ fmap[Refl] w ≈ id *)
    exact Hli.
Qed.

End Inverts.
