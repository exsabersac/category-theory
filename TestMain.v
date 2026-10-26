Require Import Category.Lib.
Require Import Category.Theory.Category.

Section Walkthrough.
  Context {C : Category} {x y z : C} (f : y ~> z) (g : x ~> y).

  Example id_after_comp : id ∘ (f ∘ g) ≈ f ∘ g.
  Proof.
    (* Goal: id ∘ (f ∘ g) ≈ f ∘ g *)
    rewrite id_left.
    (* Goal: f ∘ g ≈ f ∘ g *)
    reflexivity.
  Qed.

  Example assoc_once :
    f ∘ (g ∘ id) ≈ (f ∘ g) ∘ id.
  Proof.
    rewrite id_right.           (* 内层 g ∘ id ≈ g，需 setoid 在 ∘ 下 Proper *)
    rewrite id_right.
    reflexivity.
  Qed.
End Walkthrough.
