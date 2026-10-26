Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Factorization.StrongEpi.

Generalizable All Variables.

(*
 Regular categories: kernel pairs, regular epimorphisms, and stability.

 nLab:      https://ncatlab.org/nlab/show/regular+category
 Wikipedia: https://en.wikipedia.org/wiki/Regular_category

 A regular category is a finitely complete category in which every kernel
 pair has a coequalizer, and regular epimorphisms are stable under
 pullback.  The kernel pair of f : x ~> y is the pullback of f along
 itself ([kernel_pair]); its two projections p1, p2 : x ×_y x ~> x are the
 categorical rendering of the relation “f a = f b” on x.  A regular
 epimorphism ([RegularEpi]) is a morphism that arises as the coequalizer
 of some parallel pair; in a regular category, every regular epimorphism
 is in fact the coequalizer of its own kernel pair.

 For the finite-completeness clause we package a terminal object together
 with all pullbacks ([regular_terminal], [regular_pullbacks]).  This is
 the standard economical presentation, and it is a theorem here:
 [Structure/Limit/Finite.v]'s [finitely_complete_of_pullbacks_terminal]
 turns the two fields into every finite limit ([FinitelyComplete]).

 The theorems below place the regular epimorphisms among the epimorphism
 classes: every regular epimorphism is epic ([regular_epi_epic], read off
 [coequalizer_epic]) and moreover strong ([regular_epi_strong]) — it
 lifts uniquely against every monomorphism, which is the left
 orthogonality condition of Theory/Orthogonality.v.  Finally, the
 coequalizing map that [regular_coeq] supplies for a kernel pair is
 itself a regular epimorphism ([regular_epi_of_kernel_coeq]), packaged by
 pointing back at the kernel-pair projections it coequalizes. 

 --------
 常规范畴：核对、正则满射和稳定性。

 nLab：https://ncatlab.org/nlab/show/regular+category
 Wikipedia：https://en.wikipedia.org/wiki/Regular_category

 一个正则范畴是一个有限完备的范畴，其中每一个核对都有一个余等化子，并且正则满射在拉回下是稳定的。对于 f : x ~> y 的核对是 f 自身的拉回（[kernel_pair]）；它的两个投影 p1, p2 : x ×_y x ~> x 是在 x 上关系“f a = f b”的范畴表示。一个正则满射（[RegularEpi]）是由某个平行对的余等化子产生的态射；在正则范畴中，每个正则满射实际上都是其自身核对的余等化子。对于有限完备性条款，我们将一个末端对象与所有拉回（[regular_terminal], [regular_pullbacks]）打包在一起。这是标准的简明表示，在这里是一个定理：[Structure/Limit/Finite.v] 的 [finitely_complete_of_pullbacks_terminal] 将这两个域转变为每一个有限极限（[FinitelyComplete]）。

 下面的定理将正射影态放在射影态类中：每一个正射影态都是满射（[regular_epi_epic]，可参考 [coequalizer_epic]），而且还是强射（[regular_epi_strong]）——它能唯一地相对于每一个单射提升，这就是 Theory/Orthogonality.v 中的左正交性条件。最后，[regular_coeq] 为核对（kernel pair）提供的等化映射本身是正射影态（[regular_epi_of_kernel_coeq]），通过指回它所等化的核对投射将其打包。
*)

(*
 The kernel pair of f : x ~> y is the pullback of f along itself: an
 object x ×_y x with projections p1, p2 : x ×_y x ~> x satisfying
 f ∘ p1 ≈ f ∘ p2, universal among such pairs.

 nLab: https://ncatlab.org/nlab/show/kernel+pair 

 --------
 f : x ~> y 的核对是 f 沿自身的拉回：一个对象 x ×_y x，带有投射 p1, p2 : x ×_y x ~> x，满足 f ∘ p1 ≈ f ∘ p2，在这样的对中具有普遍性。

 nLab:  https://ncatlab.org/nlab/show/kernel+pair
*)
Definition kernel_pair {C : Category} `{H : @HasPullbacks C} {x y : C}
  (f : x ~> y) : Pullback f f := pullback f f.

(*
 A regular epimorphism is a morphism f : x ~> y that coequalizes some
 parallel pair p1, p2 : d ~> x.  The witness records the pair together
 with the elementary coequalizer structure of Structure/Coequalizer.v.

 nLab: https://ncatlab.org/nlab/show/regular+epimorphism 

 --------
 一个正规满射是一个态射 f : x ~> y，使其对某个平行对 p1, p2 : d ~> x 取得等化。该证据记录了该对以及 Structure/Coequalizer.v 的基本等化器结构。

 nLab: https://ncatlab.org/nlab/show/regular+epimorphism
*)
Record RegularEpi {C : Category} {x y : C} (f : x ~> y) := {
  regepi_dom : C;
  regepi_p1 : regepi_dom ~> x;
  regepi_p2 : regepi_dom ~> x;
  regepi_is_coeq : IsCoequalizer regepi_p1 regepi_p2 y f
}.

(*
 A regular category: a terminal object and all pullbacks (hence all
 finite limits), coequalizers of kernel pairs, and pullback-stability of
 regular epimorphisms.  Stability is phrased on the chosen pullbacks:
 pulling a regular epimorphism f : x ~> z back along any g : y ~> z
 yields a regular epimorphism x ×_z y ~> y. 

 --------
 正规范畴：一个终端对象和所有拉回（因此所有有限极限）、核对偶的伴随余化，以及正规满射的拉回稳定性。稳定性是在所选择的拉回上表达的：将一个正规满射 f : x ~> z 沿任意 g : y ~> z 拉回，得到的都是一个正规满射 x ×_z y ~> y。
*)
Class Regular (C : Category) := {
  regular_terminal  : @Terminal C;
  regular_pullbacks : @HasPullbacks C;

  (* every kernel pair has a coequalizer / 每个内核对都有一个共同化器 *)
  regular_coeq {x y : C} (f : x ~> y) :
    ∃ (q : C) (e : x ~> q),
      IsCoequalizer
        (pullback_fst f f (@kernel_pair C regular_pullbacks x y f))
        (pullback_snd f f (@kernel_pair C regular_pullbacks x y f))
        q e;

  (* regular epimorphisms are stable under pullback / 正射映射在拉回下是稳定的 *)
  regular_stable {x y z : C} (f : x ~> z) (g : y ~> z) :
    RegularEpi f →
    RegularEpi (pullback_snd f g (@pullback C regular_pullbacks x y z f g))
}.

#[export] Existing Instance regular_terminal.
#[export] Existing Instance regular_pullbacks.

(*
 Every regular epimorphism is an epimorphism: coequalizing maps are epic
 (Wikipedia: “every coequalizer is an epimorphism”). 

 --------
 每个正规满射都是满射：共轭映射是史密映射（Wikipedia：“每个共轭化器都是满射”）。
*)
Lemma regular_epi_epic {C : Category} {x y : C} (f : x ~> y) :
  RegularEpi f → Epic f.
Proof.
  intros [d p1 p2 E].
  exact (coequalizer_epic p1 p2 E).
Qed.

(*
 Every regular epimorphism is a strong epimorphism.  Given a monic
 m : u ~> v and a commuting square m ∘ a ≈ b ∘ f with f coequalizing
 p1, p2 : d ~> x, the top leg a coforks the pair — m absorbs into the
 square on both sides and f ∘ p1 ≈ f ∘ p2, so cancelling the monic m
 gives a ∘ p1 ≈ a ∘ p2 — hence a descends uniquely through f.  The
 descent is the diagonal filler: its upper triangle is the descent
 equation, its lower triangle follows by cancelling the epic f, and any
 filler satisfies the descent equation, so descent uniqueness applies. 

 --------
 每一个正规上射都是强上射。给定一个单射 m : u ~> v 以及一个交换方形 m ∘ a ≈ b ∘ f，其中 f 共同等化 p1, p2 : d ~> x，上方的边 a 对这一对进行共叉——m 在方形的两边都被吸收，并且 f ∘ p1 ≈ f ∘ p2，因此消去单射 m 得到 a ∘ p1 ≈ a ∘ p2——因此 a 可以唯一地通过 f 下降。这个下降就是对角填充：它的上方三角形是下降方程，下方三角形通过消去上射 f 得到，并且任何填充都满足下降方程，因此下降是唯一的。
*)
Lemma regular_epi_strong {C : Category} {x y : C} (f : x ~> y) :
  RegularEpi f → StrongEpi f.
Proof.
  intros [d p1 p2 E].
  constructor.
  - exact (coequalizer_epic p1 p2 E).
  - intros u v m Hm.
    constructor.
    intros a b comm.
    (* a coforks the pair p1, p2, by cancelling the monomorphism m: m ∘ (a ∘ p1) ≈ b ∘ (f ∘ p1) ≈ b ∘ (f ∘ p2) ≈ m ∘ (a ∘ p2). / a 通过消去单射 m 对偶对 p1, p2 进行共叉： m ∘ (a ∘ p1) ≈ b ∘ (f ∘ p1) ≈ b ∘ (f ∘ p2) ≈ m ∘ (a ∘ p2). *)
    assert (Ha : a ∘ p1 ≈ a ∘ p2). {
      apply (@monic C u v m Hm).
      rewrite !comp_assoc.
      rewrite comm.
      rewrite <- !comp_assoc.
      rewrite (cofork E).
      reflexivity.
    }
    pose proof (coeq_desc E a Ha) as U.
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * (* upper triangle: the descent equation d ∘ f ≈ a / 上三角：下降方程 d ∘ f ≈ a *)
        exact (unique_property U).
      * (* lower triangle m ∘ d ≈ b, by cancelling the epimorphism f: (m ∘ d) ∘ f ≈ m ∘ (d ∘ f) ≈ m ∘ a ≈ b ∘ f. / 下三角形 m ∘ d ≈ b，通过消去满射 f： (m ∘ d) ∘ f ≈ m ∘ (d ∘ f) ≈ m ∘ a ≈ b ∘ f。 *)
        apply (@epic C x y f (coequalizer_epic p1 p2 E) v
                 (m ∘ unique_obj U) b).
        rewrite <- comp_assoc.
        rewrite (unique_property U).
        exact comm.
    + intros d' [Hd'f Hmd'].
      (* any filler satisfies d' ∘ f ≈ a, so descent uniqueness applies / 任何填充物都满足 d' ∘ f ≈ a，因此适用下降唯一性 *)
      apply (uniqueness U).
      exact Hd'f.
Qed.

(*
 In a regular category, the coequalizing map supplied by [regular_coeq]
 for the kernel pair of f is itself a regular epimorphism: it manifestly
 coequalizes the kernel-pair projections. 

 --------
 在一个正规范畴中，由 [regular_coeq] 为 f 的核对偶提供的共同等化映射本身就是一个正规满射：它显然能共同等化核对偶投影。
*)
Definition regular_epi_of_kernel_coeq {C : Category} {R : Regular C}
  {x y : C} (f : x ~> y) :
  RegularEpi (`1 (`2 (regular_coeq f))) := {|
  regepi_dom := Pull f f (kernel_pair f);
  regepi_p1  := pullback_fst f f (kernel_pair f);
  regepi_p2  := pullback_snd f f (kernel_pair f);
  regepi_is_coeq := `2 (`2 (regular_coeq f))
|}.
