Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Factorization.StrongEpi.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(*
 The (regular epi, mono) orthogonal factorization system of a regular
 category.

 nLab:      https://ncatlab.org/nlab/show/regular+category
 https://ncatlab.org/nlab/show/regular+epimorphism
 https://ncatlab.org/nlab/show/image
 Wikipedia: https://en.wikipedia.org/wiki/Regular_category

 In a regular category every morphism f : x ~> y factors as a regular
 epimorphism followed by a monomorphism — the image factorization — and
 the two classes are orthogonal, so the factorizations assemble into an
 orthogonal factorization system (Structure/Factorization.v) whose left
 class is the regular epimorphisms ([RegularEpiClass]) and whose right
 class is the monomorphisms ([MonoClass] of Theory/Morphisms/Classes.v).

 The factorization of f: take its kernel pair p1, p2 : x ×_y x ~> x (the
 pullback of f along itself) and the coequalizer e : x ~> q of p1, p2
 supplied by [regular_coeq].  Since f coforks its own kernel pair —
 f ∘ p1 ≈ f ∘ p2 is the pullback square — it descends across e to a
 comparison morphism m : q ~> y with m ∘ e ≈ f.  The left leg e is a
 regular epimorphism by construction ([regular_epi_of_kernel_coeq]); the
 heart of the theorem is that the comparison m is monic
 ([image_comparison_monic]), proved by the classical double-cover
 argument, which uses pullback-stability of regular epimorphisms twice:

 Given a, b : T ~> q with m ∘ a ≈ m ∘ b, pull e back along a, obtaining
 a regular-epic cover pi1 : P1 ~> T with e ∘ s1 ≈ a ∘ pi1; then pull e
 back along b ∘ pi1, obtaining a further regular-epic cover
 pi2 : P2 ~> P1 with e ∘ s2 ≈ (b ∘ pi1) ∘ pi2.  On the double cover P2
 the two legs s1 ∘ pi2, s2 : P2 ~> x are identified by f (compute with
 m ∘ e ≈ f and m ∘ a ≈ m ∘ b), so they factor through the kernel pair
 of f; and e coequalizes the kernel pair, so e ∘ (s1 ∘ pi2) ≈ e ∘ s2.
 Unwinding the two pullback squares then gives
 a ∘ (pi1 ∘ pi2) ≈ b ∘ (pi1 ∘ pi2), and pi1 ∘ pi2 is epic (regular
 epimorphisms are epic, and epimorphisms compose), so a ≈ b.

 Orthogonality of the two classes is exactly [regular_epi_strong] of
 Structure/Regular.v: every regular epimorphism lifts uniquely against
 every monomorphism.  The packaged system is [Regular_OFS]. 

 --------
 一个正则范畴的（正则满射，单射）正交分解系统。

 nLab:       https://ncatlab.org/nlab/show/regular+category 
 https://ncatlab.org/nlab/show/regular+epimorphism 
 https://ncatlab.org/nlab/show/image 
 Wikipedia:  https://en.wikipedia.org/wiki/Regular_category 

 在正则范畴中，每个态射 f : x ~> y 都可以分解为一个正则满射后跟一个单射——即像分解——并且这两类是正交的，因此这些分解组成了一个正交分解系统（Structure/Factorization.v），其左类是正则满射（[RegularEpiClass]），右类是单射（[MonoClass]，见 Theory/Morphisms/Classes.v）。f 的分解：取其核对 p1, p2 : x ×_y x ~> x（沿自身的拉回）以及由 [regular_coeq] 提供的 p1, p2 的余等化子 e : x ~> q。由于 f 协调其自身的核对——f ∘ p1 ≈ f ∘ p2 是拉回方格——它可以通过 e 下传到比较态射 m : q ~> y，使得 m ∘ e ≈ f。左侧的 e 按构造是正规满射（[regular_epi_of_kernel_coeq]）；该定理的核心是比较态射 m 是单态（[image_comparison_monic]），通过经典的双重覆盖论证证明，该论证使用了正规满射的拉回稳定性两次：设 a, b : T ~> q 并且 m ∘ a ≈ m ∘ b，沿 a 拉回 e，得到一个正交满射覆盖 pi1 : P1 ~> T，使得 e ∘ s1 ≈ a ∘ pi1；然后沿 b ∘ pi1 拉回 e，得到一个进一步的正交满射覆盖 pi2 : P2 ~> P1，使得 e ∘ s2 ≈ (b ∘ pi1) ∘ pi2。在双重覆盖 P2 上，两条腿 s1 ∘ pi2, s2 : P2 ~> x 被 f 识别（通过计算 m ∘ e ≈ f 和 m ∘ a ≈ m ∘ b），所以它们通过 f 的核对偶进行分解；并且 e 齐次核对偶，因此 e ∘ (s1 ∘ pi2) ≈ e ∘ s2。展开两个拉回方格后得到 a ∘ (pi1 ∘ pi2) ≈ b ∘ (pi1 ∘ pi2)，并且 pi1 ∘ pi2 是满射的（正交满射是满射，并且满射可以复合），因此 a ≈ b。这两个类的正交性正是 Structure/Regular.v 中的 [regular_epi_strong]：每个正规满射对每个单射都有唯一的提升。封装的系统是 [Regular_OFS]。
*)

(*
 The class of regular epimorphisms, as a morphism class in the sense of
 Theory/Morphisms/Classes.v. 

 --------
 正同态的类，作为《Theory/Morphisms/Classes.v》中意义上的态射类。
*)
Definition RegularEpiClass {C : Category} : MorphismClass C :=
  fun _ _ f => RegularEpi f.

(* The elementary coequalizer property transports along ≈ of the coequalizing map: the cofork equation rewrites, and equivalent maps carry exactly the same descents. / 初等共轭子等化器性质沿着等化映射的≈传送：共叉方程可以重写，且等价映射携带完全相同的下降。 *)
Lemma is_coequalizer_respects {C : Category} {x y q : C}
  (f g : x ~> y) (e e' : y ~> q) :
  e ≈ e' → IsCoequalizer f g q e → IsCoequalizer f g q e'.
Proof.
  intros Heq E.
  unshelve refine {| cofork := _; coeq_desc := _ |}.
  - (* e' absorbs the parallel pair because e does / e' 吸收了并联对，因为 e 也吸收 *)
    rewrite <- Heq.
    exact (cofork E).
  - intros z h Hh.
    pose proof (coeq_desc E h Hh) as U.
    unshelve refine {| unique_obj := unique_obj U |}.
    + (* the descent across e also descends across e' / 沿 e 的下降也沿 e' 下降 *)
      rewrite <- Heq.
      exact (unique_property U).
    + intros v Hv.
      apply (uniqueness U).
      rewrite Heq.
      exact Hv.
Qed.

(* Being a regular epimorphism transports along ≈: the same parallel pair, with the transported coequalizer structure, is a witness. / 作为一个正射态射沿 ≈ 传递：相同的平行对，带有传递的余等化子结构，是一个见证。 *)
Lemma regular_epi_respects {C : Category} {x y : C} (f g : x ~> y) :
  f ≈ g → RegularEpi f → RegularEpi g.
Proof.
  intros Heq H.
  destruct H as [d p1 p2 E].
  exact {| regepi_dom := d
         ; regepi_p1  := p1
         ; regepi_p2  := p2
         ; regepi_is_coeq := is_coequalizer_respects p1 p2 f g Heq E |}.
Qed.

(*
 Being a monomorphism transports along ≈: left cancellation of g reduces
 to left cancellation of f. 

 --------
 作为单态沿 ≈ 传输：g 的左消去约化为 f 的左消去。
*)
Lemma monic_respects {C : Category} {x y : C} (f g : x ~> y) :
  f ≈ g → Monic f → Monic g.
Proof.
  intros Heq Hm.
  constructor.
  intros z g1 g2 Hgg.
  apply (@monic C x y f Hm z g1 g2).
  rewrite Heq.
  exact Hgg.
Qed.

(*
 Every regular epimorphism is orthogonal to every monomorphism: regular
 epimorphisms are strong ([regular_epi_strong]), and strength is exactly
 the unique lifting property against monomorphisms. 

 --------
 每个正则满射都与每个单射正交：正则满射是强的（[regular_epi_strong]），而强度恰好是针对单射的唯一提升性质。
*)
Lemma regular_epi_mono_orthogonal {C : Category} {a b u v : C}
  (e : a ~> b) (m : u ~> v) :
  RegularEpi e → Monic m → e ⫫ m.
Proof.
  intros He Hm.
  destruct (regular_epi_strong e He) as [Hepic Hlift].
  exact (Hlift u v m Hm).
Qed.

Section RegularFactorization.

Context {C : Category}.
Context (R : Regular C).

(* The kernel pair of f, on the chosen pullbacks of the regular structure. / 在选定的正规结构的拉回上，f 的核对。 *)
Definition image_kernel_pair {x y : C} (f : x ~> y) : Pullback f f :=
  @kernel_pair C (@regular_pullbacks C R) x y f.

(* The image object of f: the coequalizer of its kernel pair. / f 的像对象：其核对偶的共同等化子。 *)
Definition image_obj {x y : C} (f : x ~> y) : C :=
  `1 (@regular_coeq C R x y f).

(* The coequalizing map onto the image. / 到像的共等化映射。 *)
Definition image_epi {x y : C} (f : x ~> y) : x ~> image_obj f :=
  `1 (`2 (@regular_coeq C R x y f)).

(* The elementary coequalizer structure carried by the image. / 图像所携带的初等共同化结构。 *)
Definition image_is_coeq {x y : C} (f : x ~> y) :
  IsCoequalizer
    (pullback_fst f f (image_kernel_pair f))
    (pullback_snd f f (image_kernel_pair f))
    (image_obj f) (image_epi f) :=
  `2 (`2 (@regular_coeq C R x y f)).

(* f coforks its own kernel pair — the pullback square — so it descends uniquely across the coequalizing map. / f 共轭其自身的核对 — 拉回平方 — 因此它可以唯一地沿着共轭化映射下降。 *)
Definition image_desc {x y : C} (f : x ~> y) :
  ∃! u : image_obj f ~> y, u ∘ image_epi f ≈ f :=
  coeq_desc (image_is_coeq f) f
    (pullback_commutes f f (image_kernel_pair f)).

(* The comparison morphism from the image into the codomain. / 从像到余域的比较态射。 *)
Definition image_mor {x y : C} (f : x ~> y) : image_obj f ~> y :=
  unique_obj (image_desc f).

(* The factorization equation: m ∘ e ≈ f. / 分解方程：m ∘ e ≈ f。 *)
Definition image_commutes {x y : C} (f : x ~> y) :
  image_mor f ∘ image_epi f ≈ f :=
  unique_property (image_desc f).

(* The left leg is a regular epimorphism: it coequalizes the kernel pair of f. / 左边的腿是一个常规的满射：它对 f 的核对偶进行等化。 *)
Definition image_epi_regular {x y : C} (f : x ~> y) :
  RegularEpi (image_epi f) :=
  @regular_epi_of_kernel_coeq C R x y f.

(*
 The image-factorization theorem: the comparison morphism out of the
 image is monic.  This is the double-cover argument sketched in the
 header: pulling the coequalizing map e back along a and then along
 b ∘ pi1 produces a composite regular-epic cover of the common domain of
 a and b, on which a and b agree because their difference is detected by
 the kernel pair of f and erased by e. 

 --------
 像分解定理：来自像的比较态射是单态。这是标题中概述的双覆盖论证：沿着 a 再沿着 b ∘ pi1 拉回共等化映射 e 会产生一个对 a 和 b 的公共定义域的复合正射覆盖，在该公共定义域上 a 和 b 相等，因为它们的差异被 f 的核对检测并被 e 消除。
*)
Lemma image_comparison_monic {x y : C} (f : x ~> y) : Monic (image_mor f).
Proof using C R.
  constructor.
  intros T a b Hab.
  (* (i) pull e back along a; stability covers T by a regular epi pi1 / (i) 沿 a 将 e 拉回；稳定性通过正则外射 π₁ 覆盖 T *)
  pose (P1 := @pullback C (@regular_pullbacks C R) x T (image_obj f)
                (image_epi f) a).
  pose (s1 := pullback_fst (image_epi f) a P1).
  pose (pi1 := pullback_snd (image_epi f) a P1).
  assert (Hc1 : image_epi f ∘ s1 ≈ a ∘ pi1). {
    exact (pullback_commutes (image_epi f) a P1).
  }
  assert (Hpi1 : RegularEpi pi1). {
    exact (@regular_stable C R x T (image_obj f) (image_epi f) a
             (image_epi_regular f)).
  }
  (*
 (ii) pull e back along b ∘ pi1; stability covers P1 by a regular
 epi pi2 

 --------
 (ii) 沿 b ∘ pi1 拉回 e；稳定性通过正则 epi pi2 覆盖 P1
*)
  pose (P2 := @pullback C (@regular_pullbacks C R) x
                (Pull (image_epi f) a P1) (image_obj f)
                (image_epi f) (b ∘ pi1)).
  pose (s2 := pullback_fst (image_epi f) (b ∘ pi1) P2).
  pose (pi2 := pullback_snd (image_epi f) (b ∘ pi1) P2).
  assert (Hc2 : image_epi f ∘ s2 ≈ (b ∘ pi1) ∘ pi2). {
    exact (pullback_commutes (image_epi f) (b ∘ pi1) P2).
  }
  assert (Hpi2 : RegularEpi pi2). {
    exact (@regular_stable C R x (Pull (image_epi f) a P1) (image_obj f)
             (image_epi f) (b ∘ pi1) (image_epi_regular f)).
  }
  (* (iii) the two legs of the double cover into x agree under f: f ∘ (s1 ∘ pi2) ≈ m ∘ e ∘ s1 ∘ pi2 ≈ m ∘ a ∘ pi1 ∘ pi2 ≈ m ∘ b ∘ pi1 ∘ pi2 ≈ m ∘ e ∘ s2 ≈ f ∘ s2 / (iii) 在 f 下双覆盖的两条支线在 x 上一致： f ∘ (s1 ∘ pi2) ≈ m ∘ e ∘ s1 ∘ pi2 ≈ m ∘ a ∘ pi1 ∘ pi2 ≈ m ∘ b ∘ pi1 ∘ pi2 ≈ m ∘ e ∘ s2 ≈ f ∘ s2 *)
  assert (Hcone : f ∘ (s1 ∘ pi2) ≈ f ∘ s2). {
    transitivity ((image_mor f ∘ image_epi f) ∘ (s1 ∘ pi2)).
    - apply compose_respects.
      + symmetry.
        exact (image_commutes f).
      + reflexivity.
    - transitivity ((image_mor f ∘ image_epi f) ∘ s2).
      + rewrite <- !comp_assoc.
        rewrite Hc2.
        rewrite (comp_assoc (image_epi f) s1 pi2).
        rewrite Hc1.
        rewrite !comp_assoc.
        rewrite Hab.
        reflexivity.
      + apply compose_respects.
        * exact (image_commutes f).
        * reflexivity.
  }
  (* the legs therefore factor through the kernel pair of f / 因此，这些腿通过 f 的核对偶映射因子化 *)
  pose proof (ump_pullbacks f f (image_kernel_pair f) _
                (s1 ∘ pi2) s2 Hcone) as Uw.
  destruct (unique_property Uw) as [Hw1 Hw2].
  (* (iv) e coequalizes the kernel pair, so the legs agree under e / (iv) e 共同化核对偶对，因此在 e 下两条腿相符 *)
  assert (Hes : image_epi f ∘ (s1 ∘ pi2) ≈ image_epi f ∘ s2). {
    transitivity
      (image_epi f
         ∘ (pullback_fst f f (image_kernel_pair f) ∘ unique_obj Uw)).
    - apply compose_respects.
      + reflexivity.
      + symmetry.
        exact Hw1.
    - transitivity
        (image_epi f
           ∘ (pullback_snd f f (image_kernel_pair f) ∘ unique_obj Uw)).
      + rewrite !comp_assoc.
        rewrite (cofork (image_is_coeq f)).
        reflexivity.
      + apply compose_respects.
        * reflexivity.
        * exact Hw2.
  }
  (* unwinding the two pullback squares identifies a and b on the double cover / 展开两个回退方块可以在双重覆盖上识别 a 和 b *)
  assert (Hfinal : a ∘ (pi1 ∘ pi2) ≈ b ∘ (pi1 ∘ pi2)). {
    rewrite !comp_assoc.
    rewrite <- Hc1.
    rewrite <- (comp_assoc (image_epi f) s1 pi2).
    rewrite Hes.
    exact Hc2.
  }
  (* (v) the double cover is epic, so a ≈ b / (v) 双重封面很史诗，所以 a ≈ b *)
  assert (Hepi : Epic (pi1 ∘ pi2)). {
    apply epi_compose.
    - exact (regular_epi_epic pi1 Hpi1).
    - exact (regular_epi_epic pi2 Hpi2).
  }
  apply (@epic C _ T (pi1 ∘ pi2) Hepi (image_obj f) a b).
  exact Hfinal.
Qed.

(* The image factorization of f, as an (E, M)-factorization for E the regular epimorphisms and M the monomorphisms. / f 的像分解，作为 (E, M)-分解，其中 E 是正规满射，M 是单射。 *)
Definition regular_factorization {x y : C} (f : x ~> y) :
  Factorization f (@RegularEpiClass C) (@MonoClass C) := {|
  fact_mid  := image_obj f;
  fact_e    := image_epi f;
  fact_e_in := image_epi_regular f;
  fact_m    := image_mor f;
  fact_m_in := image_comparison_monic f;
  fact_comm := image_commutes f
|}.

(*
 The (regular epi, mono) orthogonal factorization system of a regular
 category. 

 --------
 正规范畴的（正则Epi、单）正交分解系统。
*)
Definition Regular_OFS : OFS (@RegularEpiClass C) (@MonoClass C) := {|
  ofs_e_respects := @regular_epi_respects C;
  ofs_m_respects := @monic_respects C;
  ofs_factor     := @regular_factorization;
  ofs_orth       := @regular_epi_mono_orthogonal C
|}.

End RegularFactorization.
