Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Orthogonality.

Generalizable All Variables.

(*
 Strong epimorphisms.

 nLab:      https://ncatlab.org/nlab/show/strong+epimorphism
 Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

 An epimorphism f : x ~> y is *strong* when it is left orthogonal to every
 monomorphism: for every monic m : u ~> v, every commuting square

 p
 x ----> u
 |       |
 f |       | m
 v       v
 y ----> v
 q

 (that is, m ∘ p ≈ q ∘ f) has a unique diagonal filler d : y ~> u with
 d ∘ f ≈ p and m ∘ d ≈ q. Strong epimorphisms sit between the split and
 the plain epimorphisms: every split epimorphism is strong
 (split_epi_strong), the class is closed under composition
 (strong_epi_compose) and under right cancellation — if f ∘ g is strong
 then so is f (strong_epi_cancel) — and a morphism that is both a strong
 epimorphism and a monomorphism is an isomorphism
 (strong_epi_mono_is_iso). These are exactly the closure properties
 enjoyed by the left class of an orthogonal factorization system, of
 which (strong epi, mono) is the motivating example. 

 --------
 强满射。

 nLab:       https://ncatlab.org/nlab/show/strong+epimorphism 
 维基百科:  https://en.wikipedia.org/wiki/Epimorphism 

 当一个满射 f : x ~> y 对每一个单射都是左正交时，它就是*强*满射：对于每一个单射 m : u ~> v, 每一个交换方阵

 p
 x ----> u
 |       |
 f |       | m
 v       v
 y ----> v
 q（也就是说，m ∘ p ≈ q ∘ f）有一个唯一的对角填充 d : y ~> u，满足 d ∘ f ≈ p 且 m ∘ d ≈ q。强射（强表态的态射）介于分裂满射和普通满射之间：每一个分裂满射都是强满射（split_epi_strong），该类在复合下闭合（strong_epi_compose）并且在右消去下闭合——如果 f ∘ g 是强满射，那么 f 也是强满射（strong_epi_cancel）——并且一个既是强满射又是单射的态射是一个同构（strong_epi_mono_is_iso）。这些正是正交分解系统的左类所具有的闭合性质，其中（强满射，单射）是一个典型示例。
*)

Record StrongEpi {C : Category} {x y : C} (f : x ~> y) := {
  strong_epic : Epic f;
  strong_lift {u v : C} (m : u ~> v) : Monic m → f ⫫ m
}.

(*
 Strong epimorphisms are closed under composition: the epic parts compose
 by epi_compose, and the lifting parts compose because the left
 orthogonality class is closed under composition (ortho_left_compose). 

 --------
 强外射在复合下是封闭的：外射部分通过 epi_compose 复合，提升部分复合的原因是左正交类在复合下是封闭的（ortho_left_compose）。
*)
Lemma strong_epi_compose {C : Category} {x y z : C}
  (f : y ~> z) (g : x ~> y) :
  StrongEpi f → StrongEpi g → StrongEpi (f ∘ g).
Proof.
  intros [Hfe Hfl] [Hge Hgl].
  constructor.
  - exact (epi_compose Hfe Hge).
  - intros u v m Hm.
    apply ortho_left_compose.
    + exact (Hgl _ _ m Hm).
    + exact (Hfl _ _ m Hm).
Qed.

(*
 Right cancellation: if a composite f ∘ g is a strong epimorphism, then so
 is its left factor f. The epic part right-cancels through the composite;
 a lifting problem for f against a monic m is whiskered with g into a
 lifting problem for f ∘ g, solved there, and the filler is checked
 against the original square by cancelling m. 

 --------
 右消去：如果复合 f ∘ g 是强满态射，则
 是其左因子f。史诗部分通过复合体右抵消;
 F 对 monic m 的提拔问题用 g 修饰为
 对于 f ∘ g 的提升问题，在那里解决，并检查填充物
 通过取消 M 来对原方形。
*)
Lemma strong_epi_cancel {C : Category} {x y z : C}
  (f : y ~> z) (g : x ~> y) :
  StrongEpi (f ∘ g) → StrongEpi f.
Proof.
  intros [He Hl].
  constructor.
  - (* Epic f: this is exactly [epic_cancel] (Theory/Morphisms.v), which was for a long time inlined here and nowhere exposed. / Epic f: 这正是 [epic_cancel]（Theory/Morphisms.v），它曾经长期被内联在这里，没有在其他地方公开。 *)
    exact (epic_cancel He).
  - (* f ⫫ m for every monomorphism m. / 对于每一个单态射 m，f ⫫ m。 *)
    intros u v m Hm.
    constructor.
    intros p q comm.
    (*
 Whiskering the square with g yields a square over f ∘ g. 

 --------
 用 g 对平方进行胡须化会得到 f ∘ g 上的平方。
*)
    assert (comm' : m ∘ (p ∘ g) ≈ q ∘ (f ∘ g)). {
      rewrite !comp_assoc.
      rewrite comm.
      reflexivity.
    }
    pose proof (@ortho_lift _ _ _ _ _ (f ∘ g) m (Hl _ _ m Hm)
                  (p ∘ g) q comm') as U.
    destruct (unique_property U) as [Ue Um].
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * (* d ∘ f ≈ p, by cancelling the monomorphism m: m ∘ (d ∘ f) ≈ (m ∘ d) ∘ f ≈ q ∘ f ≈ m ∘ p. / d ∘ f ≈ p，通过消去单态射 m： m ∘ (d ∘ f) ≈ (m ∘ d) ∘ f ≈ q ∘ f ≈ m ∘ p。 *)
        apply (@monic C u v m Hm).
        rewrite comp_assoc.
        rewrite Um.
        rewrite comm.
        reflexivity.
      * exact Um.
    + intros d' [Hd'f Hmd'].
      (*
 Any filler of the f-square also fills the whiskered square, so it
 coincides with the lift obtained there. 

 --------
 任意 f 方格的填充也会填充有须方格，因此它与那里的提升相符。
*)
      apply (uniqueness U).
      split.
      * rewrite comp_assoc.
        rewrite Hd'f.
        reflexivity.
      * exact Hmd'.
Qed.

(*
 Every split epimorphism is strong: it is epic (retractions_are_epic),
 and the section provides the filler p ∘ retract directly, with the monic
 on the right forcing both the lower triangle and uniqueness. 

 --------
 每个分裂上射都是强的：它是上射的（retractions_are_epic），并且截面直接提供填充 p ∘ retract，右侧的单射强制下方三角形和唯一性。
*)
Lemma split_epi_strong {C : Category} {x y : C} (f : x ~> y) :
  Retraction f → StrongEpi f.
Proof.
  intros Hr.
  constructor.
  - exact (retractions_are_epic _ _ f Hr).
  - intros u v m Hm.
    constructor.
    intros p q comm.
    destruct Hr as [r rcomp].
    unshelve refine {| unique_obj := p ∘ r |}.
    + split.
      * (* (p ∘ r) ∘ f ≈ p, by cancelling m: m ∘ ((p ∘ r) ∘ f) ≈ ((q ∘ f) ∘ r) ∘ f ≈ q ∘ f ≈ m ∘ p. / (p ∘ r) ∘ f ≈ p，通过消去 m: m ∘ ((p ∘ r) ∘ f) ≈ ((q ∘ f) ∘ r) ∘ f ≈ q ∘ f ≈ m ∘ p。 *)
        apply (@monic C u v m Hm).
        rewrite !comp_assoc.
        rewrite comm.
        rewrite <- (comp_assoc q f r).
        rewrite rcomp.
        rewrite id_right.
        reflexivity.
      * (* m ∘ (p ∘ r) ≈ (q ∘ f) ∘ r ≈ q ∘ id ≈ q / m ∘ (p ∘ r) ≈ (q ∘ f) ∘ r ≈ q ∘ id ≈ q *)
        rewrite comp_assoc.
        rewrite comm.
        rewrite <- comp_assoc.
        rewrite rcomp.
        apply id_right.
    + intros d' [Hd'f Hmd'].
      (*
 Fillers are unique because m is monic: m ∘ (p ∘ r) ≈ q ≈ m ∘ d'. 

 --------
 填充物是独特的，因为 m 是单一的：m ∘ (p ∘ r) ≈ q ≈ m ∘ d'。
*)
      apply (@monic C u v m Hm).
      rewrite Hmd'.
      rewrite comp_assoc.
      rewrite comm.
      rewrite <- comp_assoc.
      rewrite rcomp.
      apply id_right.
Qed.

(*
 A morphism that is both a strong epimorphism and a monomorphism is an
 isomorphism: lifting the identity square f ∘ id ≈ id ∘ f against f
 itself (which is monic by hypothesis) produces a two-sided inverse. 

 --------
 一个既是强满射又是单射的态射是一个同构：将恒等方形 f ∘ id ≈ id ∘ f 关于 f 本身（根据假设是单射）升起，会产生一个双边逆元。
*)
Lemma strong_epi_mono_is_iso {C : Category} {x y : C} (f : x ~> y) :
  StrongEpi f → Monic f → IsIsomorphism f.
Proof.
  intros [He Hl] Hm.
  assert (comm : f ∘ id ≈ id ∘ f). {
    cat.
  }
  pose proof (@ortho_lift _ _ _ _ _ f f (Hl _ _ f Hm) id id comm) as U.
  destruct (unique_property U) as [Ul Ur].
  (*
 Ul : unique_obj U ∘ f ≈ id (left inverse);
 Ur : f ∘ unique_obj U ≈ id (right inverse). 

 --------
 Ul：unique_obj U ∘ f ≈ id（左逆）;
 Ur：f ∘ unique_obj U ≈ id（右逆）。
*)
  exact {| two_sided_inverse := unique_obj U;
           is_right_inverse  := Ur;
           is_left_inverse   := Ul |}.
Qed.
