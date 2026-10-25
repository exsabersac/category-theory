Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(** * Kernels and cokernels / * 核和余核 *)

(*
 nLab:      https://ncatlab.org/nlab/show/kernel
 https://ncatlab.org/nlab/show/cokernel
 Wikipedia: https://en.wikipedia.org/wiki/Kernel_(category_theory)
 https://en.wikipedia.org/wiki/Cokernel

 In a category with a zero object, the kernel of f : x ~> y is the
 equalizer of f with the zero morphism, and the cokernel of f is the
 coequalizer of f with the zero morphism (nLab; Wikipedia).  With the
 elementary presentations [IsEqualizer] (Structure/Equalizer/Fork.v) and
 [IsCoequalizer] (Structure/Coequalizer.v) in hand, both notions are one
 definition each: [IsKernel f i := IsEqualizer f zero_mor k i] and
 [IsCokernel f e := IsCoequalizer f zero_mor q e].

 The frozen plan sketched obtaining the cokernel by transfer along the
 opposite category, but Phase 8's covariant [IsCoequalizer] already lives
 directly in C, so the direct definition below is exactly the accessor
 form that plan asked for.

 The classical facts follow immediately from the donor lemmas: kernels
 are monomorphisms ([kernel_monic], via [equalizer_monic]) and cokernels
 are epimorphisms ([cokernel_epic], via [coequalizer_epic]).  The descent
 lemmas [kernel_desc] and [cokernel_desc] restate the universal
 properties in the zero-composite phrasing preferred downstream: any h
 with f ∘ h ≈ 0 factors uniquely through the kernel, and dually.  A
 monomorphism is *normal* when it arises as a kernel ([normal_mono]), an
 epimorphism *conormal* when it arises as a cokernel ([normal_epi]);
 these feed the abelian-category axioms.  Finally,
 [cokernel_regular_epi] records that every cokernel map is a regular
 epimorphism — it manifestly coequalizes the pair (f, 0) — which is the
 bridge Abelian.v uses to reach the strong-epi/mono factorization. 

 --------
 nLab:       https://ncatlab.org/nlab/show/kernel 
 https://ncatlab.org/nlab/show/cokernel 
 维基百科:  https://en.wikipedia.org/wiki/Kernel_(category_theory) 
 https://en.wikipedia.org/wiki/Cokernel 

 在具有零对象的范畴中，f : x ~> y 的核是 f 与零态射的等化子，f 的余核是 f 与零态射的余等化子（nLab；维基百科）。有了基本的表示 [IsEqualizer]（Structure/Equalizer/Fork.v）和 [IsCoequalizer]（Structure/Coequalizer.v），这两种概念各自只有一个定义：[IsKernel f i := IsEqualizer f zero_mor k i] 和 [IsCokernel f e := IsCoequalizer f zero_mor q e]。

 先前的计划勾画了通过沿对偶范畴传递来获得余核，但第 8 阶段的协变 [IsCoequalizer] 已经直接位于 C 中，因此下面的直接定义正是该计划所要求的访问器形式。经典的事实直接来自于给予引理：核是单态（[kernel_monic]，通过[equalizer_monic]），余核是满态（[cokernel_epic]，通过[coequalizer_epic]）。下降引理[kernel_desc]和[cokernel_desc]以下游偏好的零复合表述重述了普遍性质：任何满足f ∘ h ≈ 0的h都可以唯一地通过核进行因子分解，反之亦然。当一个单态来自于核时，它是*正规*的（[normal_mono]），当一个满态来自于余核时，它是*余正规*的（[normal_epi]）；这些构成了阿贝尔范畴公理。最后，[cokernel_regular_epi]记录了每个余核映射都是正规满态——它显然使得(f, 0)对的共均化成立——这是Abelian.v用来达成强满/单分解的桥梁。
*)

Section Kernel.

Context {C : Category}.
Context `{Z : @ZeroObject C}.

(*
 The kernel of f : x ~> y, presented elementarily: i : k ~> x equalizes
 f against the zero morphism. 

 --------
 f 的核 : x ~> y，以初等方式表示：i : k ~> x 等化 f 与零态射。
*)
Definition IsKernel {x y k : C} (f : x ~> y) (i : k ~> x) : Type :=
  IsEqualizer f zero_mor k i.

(*
 The cokernel of f : x ~> y, presented elementarily: e : y ~> q
 coequalizes f against the zero morphism. 

 --------
 f : x ~> y 的余核，元素呈现为：e : y ~> q，使 f 与零态射共轭。
*)
Definition IsCokernel {x y q : C} (f : x ~> y) (e : y ~> q) : Type :=
  IsCoequalizer f zero_mor q e.

(*
 A category (with zero object) has kernels when every morphism carries
 a chosen kernel. 

 --------
 一个（具有零对象的）范畴有核，当且仅当每个态射都有一个选定的核。
*)
Class HasKernels := {
  kernel {x y : C} (f : x ~> y) : ∃ (k : C) (i : k ~> x), IsKernel f i
}.

(*
 Dually, it has cokernels when every morphism carries a chosen
 cokernel. 

 --------
 同样地，当每个态射都有一个选定的余核时，它具有余核。
*)
Class HasCokernels := {
  cokernel {x y : C} (f : x ~> y) : ∃ (q : C) (e : y ~> q), IsCokernel f e
}.

(* * ** The defining composites are zero / * ** 定义的复合数为零 *)

(*
 The kernel inclusion is absorbed by f: from the fork equation
 f ∘ i ≈ zero_mor ∘ i, the right-hand side collapses by zero-morphism
 absorption. 

 --------
 内核包含被 f 吸收：从叉方程 f ∘ i ≈ zero_mor ∘ i，右侧通过零态射吸收而简化。
*)
Lemma kernel_comp_zero {x y k : C} {f : x ~> y} {i : k ~> x}
  (K : IsKernel f i) : f ∘ i ≈ zero_mor.
Proof.
  rewrite (fork_eq K).
  apply zero_mor_right.
Qed.

(*
 Dually, the cokernel projection absorbs f: from the cofork equation
 e ∘ f ≈ e ∘ zero_mor, the right-hand side collapses by zero-morphism
 absorption. 

 --------
 同样地，余核投影吸收 f：根据余叉方程 e ∘ f ≈ e ∘ zero_mor，右侧通过零态射吸收而消去。
*)
Lemma cokernel_comp_zero {x y q : C} {f : x ~> y} {e : y ~> q}
  (K : IsCokernel f e) : e ∘ f ≈ zero_mor.
Proof.
  rewrite (cofork K).
  apply zero_mor_left.
Qed.

(* * ** Kernels are monic, cokernels are epic / * ** 核是单首的，余核是满射的 *)

(*
 Wikipedia: "every kernel is a monomorphism" — read off the equalizer. 

 --------
 维基百科：“每个核都是单射”——读出等化器。
*)
Lemma kernel_monic {x y k : C} {f : x ~> y} {i : k ~> x}
  (K : IsKernel f i) : Monic i.
Proof.
  exact (equalizer_monic f zero_mor K).
Qed.

(*
 Wikipedia: "every cokernel is an epimorphism" — read off the
 coequalizer. 

 --------
 维基百科：“每个余核都是一个满射”——从共等化器中读出。
*)
Lemma cokernel_epic {x y q : C} {f : x ~> y} {e : y ~> q}
  (K : IsCokernel f e) : Epic e.
Proof.
  exact (coequalizer_epic f zero_mor K).
Qed.

(* * ** Descent in the zero-composite phrasing / * ** 在零复合短语中的下降 *)

(*
 Any h with f ∘ h ≈ 0 factors uniquely through the kernel.  The
 hypothesis of [eq_desc] reads f ∘ h ≈ zero_mor ∘ h; the adapter step
 converts the zero-composite hypothesis into that shape via absorption
 of zero morphisms under precomposition. 

 --------
 任何与 f ∘ h ≈ 0 的 h 都可以唯一地通过核因子分解。[eq_desc] 的假设写作 f ∘ h ≈ zero_mor ∘ h；适配步骤通过在前合成下吸收零态射，将零复合假设转换为这种形式。
*)
Lemma kernel_desc {x y k : C} {f : x ~> y} {i : k ~> x}
  (K : IsKernel f i) {z : C} (h : z ~> x) (Hh : f ∘ h ≈ zero_mor) :
  ∃! u : z ~> k, i ∘ u ≈ h.
Proof.
  apply (eq_desc K).
  rewrite Hh.
  symmetry.
  apply zero_mor_right.
Qed.

(*
 Dually, any h with h ∘ f ≈ 0 descends uniquely through the cokernel.
 The hypothesis of [coeq_desc] reads h ∘ f ≈ h ∘ zero_mor; the adapter
 step converts the zero-composite hypothesis into that shape via
 absorption of zero morphisms under postcomposition. 

 --------
 同样地，任何满足 h ∘ f ≈ 0 的 h 都可以唯一地通过余核下降。
 [coeq_desc] 的假设是 h ∘ f ≈ h ∘ zero_mor；适配步骤通过吸收后合成下的零态射，将零复合假设转换为该形式。
*)
Lemma cokernel_desc {x y q : C} {f : x ~> y} {e : y ~> q}
  (K : IsCokernel f e) {z : C} (h : y ~> z) (Hh : h ∘ f ≈ zero_mor) :
  ∃! u : q ~> z, u ∘ e ≈ h.
Proof.
  apply (coeq_desc K).
  rewrite Hh.
  symmetry.
  apply zero_mor_left.
Qed.

(* * ** Normal monomorphisms and normal epimorphisms / * ** 正单态和正满态 *)

(*
 A morphism is a normal monomorphism when it is the kernel of some
 morphism.  nLab: https://ncatlab.org/nlab/show/normal+monomorphism 

 --------
 当一个态射是某些态射的核时，它是一个正常单射。 nLab: https://ncatlab.org/nlab/show/normal+monomorphism
*)
Definition normal_mono {k x : C} (i : k ~> x) : Type :=
  ∃ (y : C) (f : x ~> y), IsKernel f i.

(*
 Dually, a normal (or conormal) epimorphism is the cokernel of some
 morphism.  nLab: https://ncatlab.org/nlab/show/normal+epimorphism 

 --------
 相对地，正常（或共正常）满射是某个态射的余核。 nLab: https://ncatlab.org/nlab/show/normal+epimorphism
*)
Definition normal_epi {y q : C} (e : y ~> q) : Type :=
  ∃ (x : C) (f : x ~> y), IsCokernel f e.

(* * ** Cokernels are regular epimorphisms / * ** 共核是正则表态射 *)

(*
 Every cokernel map is a regular epimorphism: it coequalizes the
 parallel pair (f, 0) by definition.  This is the bridge Abelian.v uses
 to inherit the strong-epi/mono factorization from Structure/Regular.v
 ([regular_epi_strong]). 

 --------
 每一个余核映射都是正则的上射：根据定义，它使平行对 (f, 0) 相等。 这是 Abelian.v 用来从 Structure/Regular.v ([regular_epi_strong]) 继承强上射/单射分解的桥梁。
*)
Definition cokernel_regular_epi {x y q : C} {f : x ~> y} {e : y ~> q}
  (K : IsCokernel f e) : RegularEpi e := {|
  regepi_dom := x;
  regepi_p1 := f;
  regepi_p2 := zero_mor;
  regepi_is_coeq := K
|}.

(* * ** Normality against the chosen (co)kernels / * ** 针对所选（共）核的正规性 *)

(*
 A kernel of anything is a kernel of EVERY cokernel of itself: the
 original morphism descends through the cokernel, so anything the
 cokernel projection kills is already killed by the original morphism
 and factors through the kernel.  Together with its dual this makes the
 chosen-cokernel phrasing of the normality interface (the class fields
 of Structure/Abelian.v) carry full generality, as a theorem rather
 than a remark. 

 --------
 任何事物的核都是它自身的每个余核的核：原始的态射通过余核下降，所以余核投射映射消去的任何东西已经被原始态射消去，并且可以通过核分解。与其对偶结合，这使得正规性接口的选定余核表述（Structure/Abelian.v 的类域）具有完全的一般性，作为一个定理而非注解。
*)
Lemma kernel_of_any_cokernel {k x y q : C} {f : x ~> y} {i : k ~> x}
  (K : IsKernel f i) {e : x ~> q} (CK : IsCokernel i e) :
  IsKernel e i.
Proof.
  unshelve refine {| fork_eq := _ |}.
  - (* e ∘ i ≈ zero_mor ∘ i / e ∘ i ≈ zero_mor ∘ i *)
    rewrite (cokernel_comp_zero CK).
    symmetry.
    apply zero_mor_right.
  - (* descent: anything killed by e is killed by f, then use K / 下降：如果 e 杀死的任何东西被 f 杀死，则使用 K *)
    intros z h Hh.
    assert (He : e ∘ h ≈ zero_mor).
    { rewrite Hh.
      apply zero_mor_right. }
    pose proof (cokernel_desc CK f (kernel_comp_zero K)) as S.
    assert (Hf : f ∘ h ≈ zero_mor).
    { rewrite <- (unique_property S).
      rewrite <- comp_assoc.
      rewrite He.
      apply zero_mor_left. }
    exact (kernel_desc K h Hf).
Defined.

(*
 Dual: a cokernel of anything is a cokernel of every kernel of itself. 

 --------
 对偶：任何东西的余核都是其自身每个核的余核。
*)
Lemma cokernel_of_any_kernel {x y q k : C} {f : x ~> y} {e : y ~> q}
  (CK : IsCokernel f e) {i : k ~> y} (K : IsKernel e i) :
  IsCokernel i e.
Proof.
  unshelve refine {| cofork := _ |}.
  - (* e ∘ i ≈ e ∘ zero_mor / e ∘ i ≈ e ∘ zero_mor *)
    rewrite (kernel_comp_zero K).
    symmetry.
    apply zero_mor_left.
  - (* descent through CK after showing h kills f / 在显示 h 杀死 f 后通过 CK 的下降 *)
    intros z h Hh.
    assert (He : h ∘ i ≈ zero_mor).
    { rewrite Hh.
      apply zero_mor_left. }
    pose proof (kernel_desc K f (cokernel_comp_zero CK)) as S.
    assert (Hf : h ∘ f ≈ zero_mor).
    { rewrite <- (unique_property S).
      rewrite comp_assoc.
      rewrite He.
      apply zero_mor_right. }
    exact (cokernel_desc CK h Hf).
Defined.

(*
 At the CHOSEN cokernel/kernel: a normal mono is a kernel of its chosen
 cokernel, and dually. 

 --------
 在所选余核/核上：一个普通单射是其所选余核的核，反之亦然。
*)
Corollary normal_mono_kernel_of_cokernel {HCK : HasCokernels} {k x : C}
  (i : k ~> x) (N : normal_mono i) :
  IsKernel (`1 (`2 (cokernel i))) i.
Proof.
  destruct N as [y [f K]].
  exact (kernel_of_any_cokernel K (`2 (`2 (cokernel i)))).
Qed.

Corollary normal_epi_cokernel_of_kernel {HK : HasKernels} {y q : C}
  (e : y ~> q) (N : normal_epi e) :
  IsCokernel (`1 (`2 (kernel e))) e.
Proof.
  destruct N as [x [f CK]].
  exact (cokernel_of_any_kernel CK (`2 (`2 (kernel e)))).
Qed.

End Kernel.
