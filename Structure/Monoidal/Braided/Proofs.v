Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/braided+monoidal+category

 Derived coherence between the braiding and the unitors. In any braided
 monoidal category the two unit isomorphisms are exchanged by the braiding:

 rho ≈ lambda ∘ beta        ([braid_unit_left]),
 lambda ≈ rho ∘ beta        ([braid_unit_right]),

 i.e. ρ_x ≈ λ_x ∘ β_{x,I} and λ_x ≈ ρ_x ∘ β_{I,x}. This is Proposition 2.1
 of Joyal & Street, “Braided tensor categories” (Adv. Math. 102, 1993). Like
 the Kelly lemmas of Structure/Monoidal/Proofs.v, these are not part of the
 braided data: they follow from the hexagon identity, the triangle identity,
 and naturality of the braiding and the unitors.

 The argument instantiates the first hexagon at (x, I, I), post-composes
 with id ⨂ λ, and contracts both sides with the triangle identities and
 naturality until the braid-free composite ρ remains; the auxiliary
 tensorings by id[I] are then cancelled with [tensor_id_left_inj] and the
 invertible structural maps.

 The proofs are carried out for a *symmetric* monoidal category: this
 library's [BraidedMonoidal] class exposes the braiding as a natural family
 of morphisms without an inverse, so the cancellation of a trailing
 [braid ⨂ id] is obtained from the symmetry law [braid_invol]. (In the
 braided-but-not-symmetric case the same argument goes through once the
 braiding is packaged as an isomorphism; every consumer in this development
 is symmetric.)

 This supplies the coherence needed to package the derived right strength
 of a strong monad over a symmetric base (ρ ≈ λ ∘ β):
 Monad/Strong/Symmetric.v consumes it to build [rstr_RightStrongFunctor]
 and [rstr_RightStrongMonad].  It also discharges the braid-unitor
 compatibilities that a cartesian monoidal structure must satisfy.

 Beyond the braid-unitor coherence, this file hosts the shared
 monoidal/symmetric coherence toolkit consumed by the copy-discard stack
 (the files under Structure/Monoidal/CopyDiscard) and the collapse theorems
 (Structure/Monoidal/Collapse.v): iso-cancellation lemmas in
 mid-composition (“cons”) position, bimap fusion and associator-naturality
 shuffles with solved pentagon and triangle forms, and the four-object
 middle interchange [swap_inner] with its braiding, associativity and unit
 coherences.  Everything is stated for a bare [Monoidal] or
 [SymmetricMonoidal] structure — deliberately independent of the
 copy-discard and hypergraph stacks, so later developments can import the
 kit without dragging in those dependencies.  (The identification of
 [swap_inner]'s diagonal with Hypergraph.v's [mid_swap_inv] lives in
 Structure/Monoidal/CopyDiscard/Deterministic.v for exactly this
 reason.) 

 --------
 nLab: https://ncatlab.org/nlab/show/braided+monoidal+category

 在编织和单位子之间导出的相干性。在任何编织单范畴中，两个单位同构会被编织交换：

 rho ≈ lambda ∘ beta        ([braid_unit_left]),
 lambda ≈ rho ∘ beta        ([braid_unit_right]),

 即 ρ_x ≈ λ_x ∘ β_{x,I} 和 λ_x ≈ ρ_x ∘ β_{I,x}。这是 Joyal & Street 《Braided tensor categories》(Adv. Math. 102, 1993) 的命题 2.1。像 Structure/Monoidal/Proofs.v 中的 Kelly 引理一样，这些不属于编织数据的一部分：它们是从六边形恒等式、三角形恒等式，以及编织和单位子的自然性推导出来的。该论证在 (x, I, I) 处实例化第一个六边形，随后与 id ⨂ λ 复合，并通过三角恒等式和自然性对两边进行约简，直到只剩下无编织的复合 ρ；然后通过 id [I] 对辅助张量进行的操作与 [tensor_id_left_inj] 及可逆的结构映射相抵消。

 这些证明是在*对称*单范畴下进行的：该库的 [BraidedMonoidal] 类将编织作为没有逆的自然态射族公开，因此尾随的 [braid ⨂ id] 的抵消是通过对称律 [braid_invol] 获得的。（在有编织但非对称的情况下，一旦将编织封装为同构，相同的论证也成立；在这个开发过程中，每个使用者都是对称的。）这提供了包装强单子在对称基下导出右强度所需的连贯性 (ρ ≈ λ ∘ β)：Monad/Strong/Symmetric.v 使用它来构建 [rstr_RightStrongFunctor] 和 [rstr_RightStrongMonad]。它还解除笛卡尔幺半群结构必须满足的编织-单位元兼容性。超越辫子-联合器一致性，这个文件包含了由复制-丢弃栈（Structure/Monoidal/CopyDiscard 下的文件）和塌缩定理（Structure/Monoidal/Collapse.v）使用的共享单体/对称一致性工具包：中间组合（“cons”）位置的等距抵消引理，双映射融合和关联子自然性洗牌，伴随已解决的五边形和三角形形式，以及四对象中间交换 [swap_inner] 及其编织性、结合性和单位一致性。所有内容都针对裸 [Monoidal] 或 [SymmetricMonoidal] 结构进行陈述——有意独立于复制-丢弃和超图栈，因此后续开发可以导入该工具包而不带入这些依赖项。（将 [swap_inner] 的对角线与 Hypergraph.v 的 [mid_swap_inv] 对应，正是出于这个原因，它存在于 Structure/Monoidal/CopyDiscard/Deterministic.v 中。）
*)

(* ------------------------------------------------------------------ *)

(*
   * ** Toolkit: iso cancellation in mid-composition position

   Rewriting inside long composites constantly needs to cancel an adjacent
   [to i ∘ from i] pair that is followed by a continuation [k]; these
   “cons” forms keep every rewrite a single step. 

   --------
   * ** 工具包：在中间组合位置取消 ISO

   在长组合内部不断重写时，需要取消紧邻的
   [to i ∘ from i] 对，该对后面跟着一个续接的 [k]；这些
   “cons” 形式使每次重写保持单步操作。
*)

Section IsoCancellation.

Context {C : Category}.

Lemma cancel_from_to_cons {x y z : C} (i : x ≅ y) (k : z ~> x) :
  i⁻¹ ∘ (to i ∘ k) ≈ k.
Proof.
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.

Lemma cancel_to_from_cons {x y z : C} (i : x ≅ y) (k : z ~> y) :
  to i ∘ (i⁻¹ ∘ k) ≈ k.
Proof.
  rewrite comp_assoc.
  rewrite iso_to_from.
  apply id_left.
Qed.

End IsoCancellation.

(* ------------------------------------------------------------------ *)

(*
   * ** Toolkit: monoidal shuffles

   Bimap fusion/cancellation, associator naturality and derived pentagon
   shapes, all stated in right-associated “cons” form so that they apply
   by a single [rewrite] in the middle of a right-associated chain.

   The kit is exported, citable API: plain and mirror-image forms are
   included for completeness even where only one orientation currently has
   an in-tree consumer (e.g. [triangle_inverse_left]). 

   --------
   * ** 工具包：幺半群洗牌

   双映射融合/消去、结合子自然性和派生五边形结构，均以右关联的“cons”形式陈述，以便它们可以通过右关联链中间的单个 [rewrite] 应用。

   该工具包是导出的、可引用的 API：为了完整性，即使当前树中只有一个方向有使用者（例如 [triangle_inverse_left]），也包括普通形式和镜像形式。
*)

Section MonoidalToolkit.

Context {C : Category}.
Context `{M : @Monoidal C}.

Lemma bimap_id_cancel_cons {h x y z : C} (i : x ≅ y)
      (k : z ~> (h ⨂ x)%object) :
  (id[h] ⨂ i⁻¹) ∘ ((id[h] ⨂ to i) ∘ k) ≈ k.
Proof.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite iso_from_to, id_left, bimap_id_id.
  apply id_left.
Qed.

Lemma bimap_cancel_right_cons {h x y z : C} (i : x ≅ y)
      (k : z ~> (x ⨂ h)%object) :
  (i⁻¹ ⨂ id[h]) ∘ ((to i ⨂ id[h]) ∘ k) ≈ k.
Proof.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite iso_from_to, id_left, bimap_id_id.
  apply id_left.
Qed.

Lemma bimap_cancel_right {h x y : C} (i : x ≅ y) :
  (i⁻¹ ⨂ id[h]) ∘ (to i ⨂ id[h]) ≈ id[(x ⨂ h)%object].
Proof.
  rewrite <- bimap_comp.
  rewrite iso_from_to, id_left, bimap_id_id.
  reflexivity.
Qed.

Lemma bimap_swap_cons {x y z w v : C} (f : x ~> y) (g : z ~> w)
      (k : v ~> (z ⨂ x)%object) :
  (id[w] ⨂ f) ∘ ((g ⨂ id[x]) ∘ k) ≈ (g ⨂ f) ∘ k.
Proof.
  rewrite comp_assoc.
  rewrite bimap_id_left_right.
  reflexivity.
Qed.

Lemma bimap_swap2_cons {x y z w v : C} (f : x ~> y) (g : z ~> w)
      (k : v ~> (x ⨂ z)%object) :
  (f ⨂ id[w]) ∘ ((id[x] ⨂ g) ∘ k) ≈ (id[y] ⨂ g) ∘ ((f ⨂ id[z]) ∘ k).
Proof.
  rewrite !comp_assoc.
  rewrite bimap_id_right_left.
  rewrite bimap_id_left_right.
  reflexivity.
Qed.

Lemma bimap_id_fuse {h x y z : C} (p : y ~> z) (q : x ~> y) :
  (id[h] ⨂ p) ∘ (id[h] ⨂ q) ≈ id[h] ⨂ (p ∘ q).
Proof.
  rewrite <- bimap_comp.
  rewrite id_left.
  reflexivity.
Qed.

Lemma bimap_id_fuse_cons {h x y z w : C} (p : y ~> z) (q : x ~> y)
      (k : w ~> (h ⨂ x)%object) :
  (id[h] ⨂ p) ∘ ((id[h] ⨂ q) ∘ k) ≈ (id[h] ⨂ (p ∘ q)) ∘ k.
Proof.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_left.
  reflexivity.
Qed.

Lemma bimap_id_split_cons {h x y z w : C} (p : y ~> z) (q : x ~> y)
      (k : w ~> (h ⨂ x)%object) :
  (id[h] ⨂ (p ∘ q)) ∘ k ≈ (id[h] ⨂ p) ∘ ((id[h] ⨂ q) ∘ k).
Proof. symmetry; apply bimap_id_fuse_cons. Qed.

Lemma bimap_fuse_cons {x y z x' y' z' w : C}
      (p : y ~> z) (q : y' ~> z') (r : x ~> y) (s : x' ~> y')
      (k : w ~> (x ⨂ x')%object) :
  (p ⨂ q) ∘ ((r ⨂ s) ∘ k) ≈ ((p ∘ r) ⨂ (q ∘ s)) ∘ k.
Proof.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  reflexivity.
Qed.

Lemma bimap_fuse_id_right {h x y z : C} (p : y ~> z) (r : x ~> y) :
  (p ⨂ id[h]) ∘ (r ⨂ id[h]) ≈ (p ∘ r) ⨂ id[h].
Proof.
  rewrite <- bimap_comp.
  rewrite id_left.
  reflexivity.
Qed.

(** Associator naturality, cons forms. / 关联器的自然性，cons 形式。 *)

Lemma to_assoc_nat_cons {x y z w v u t : C}
      (g : x ~> y) (h : z ~> w) (i : v ~> u)
      (k : t ~> ((x ⨂ z) ⨂ v)%object) :
  (g ⨂ (h ⨂ i)) ∘ (to tensor_assoc ∘ k)
    ≈ to tensor_assoc ∘ (((g ⨂ h) ⨂ i) ∘ k).
Proof.
  rewrite !comp_assoc.
  rewrite to_tensor_assoc_natural.
  reflexivity.
Qed.

Lemma from_assoc_nat_cons {x y z w v u t : C}
      (g : x ~> y) (h : z ~> w) (i : v ~> u)
      (k : t ~> (x ⨂ (z ⨂ v))%object) :
  ((g ⨂ h) ⨂ i) ∘ (tensor_assoc⁻¹ ∘ k)
    ≈ tensor_assoc⁻¹ ∘ ((g ⨂ (h ⨂ i)) ∘ k).
Proof.
  rewrite !comp_assoc.
  rewrite from_tensor_assoc_natural.
  reflexivity.
Qed.

(*
 Naturality against a map in the third slot, the first two slots being a
 fused identity. 

 --------
 在第三个槽位中与地图的自然性，前两个槽位是一个融合的身份。
*)
Lemma to_assoc_nat_id2_cons {u v x y w : C} (g : x ~> y)
      (k : w ~> ((u ⨂ v) ⨂ x)%object) :
  to tensor_assoc ∘ ((id[(u ⨂ v)%object] ⨂ g) ∘ k)
    ≈ (id[u] ⨂ (id[v] ⨂ g)) ∘ (to tensor_assoc ∘ k).
Proof.
  spose (to_tensor_assoc_natural (id[u]) (id[v]) g) as X.
  rewrite bimap_id_id in X.
  rewrite !comp_assoc.
  rewrite <- X.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Lemma from_assoc_nat_id2_cons {u v x y w : C} (Z : x ~> y)
      (k : w ~> (u ⨂ (v ⨂ x))%object) :
  (id[(u ⨂ v)%object] ⨂ Z) ∘ (tensor_assoc⁻¹ ∘ k)
    ≈ tensor_assoc⁻¹ ∘ ((id[u] ⨂ (id[v] ⨂ Z)) ∘ k).
Proof.
  spose (from_tensor_assoc_natural (id[u]) (id[v]) Z) as X.
  rewrite bimap_id_id in X.
  rewrite !comp_assoc.
  rewrite X.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(*
   * Pentagon shapes.  [pentagon_a] is the pentagon axiom right-associated;
   the [pentagon_solved*] family solves it for the various two-factor
   associator composites that appear while normalizing. 

   --------
   * 五边形形状。   [pentagon_a] 是五边形公理右结合的；[pentagon_solved*] 系列在规范化过程中出现的各种双因子结合子复合上求解它。
*)

Lemma pentagon_a {u v w t : C} :
  (id[u] ⨂ to tensor_assoc)
    ∘ (to tensor_assoc ∘ (to tensor_assoc ⨂ id[t]))
    ≈ to (@tensor_assoc C _ u v (w ⨂ t))
        ∘ to (@tensor_assoc C _ (u ⨂ v) w t).
Proof.
  rewrite !comp_assoc.
  apply pentagon_identity.
Qed.

Lemma pentagon_cons {u v w t z : C} (k : z ~> (((u ⨂ v) ⨂ w) ⨂ t)%object) :
  (id[u] ⨂ to tensor_assoc)
    ∘ (to tensor_assoc ∘ ((to tensor_assoc ⨂ id[t]) ∘ k))
    ≈ to tensor_assoc ∘ (to tensor_assoc ∘ k).
Proof.
  rewrite !comp_assoc.
  rewrite pentagon_identity.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Lemma pentagon_solved {u v w t : C} :
  to tensor_assoc ∘ (tensor_assoc⁻¹ ⨂ id[t])
    ≈ tensor_assoc⁻¹
        ∘ ((id[u] ⨂ to tensor_assoc)
             ∘ to (@tensor_assoc C _ u (v ⨂ w) t)).
Proof.
  apply (iso_to_monic tensor_assoc).
  rewrite (cancel_to_from_cons tensor_assoc).
  rewrite <- pentagon_cons.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_left.
  rewrite bimap_id_id.
  rewrite id_right.
  reflexivity.
Qed.

Lemma pentagon_solved_cons {u v w t z : C}
      (k : z ~> ((u ⨂ (v ⨂ w)) ⨂ t)%object) :
  to tensor_assoc ∘ ((tensor_assoc⁻¹ ⨂ id[t]) ∘ k)
    ≈ tensor_assoc⁻¹
        ∘ ((id[u] ⨂ to tensor_assoc)
             ∘ (to (@tensor_assoc C _ u (v ⨂ w) t) ∘ k)).
Proof.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  apply pentagon_solved.
Qed.

Lemma pentagon_solved2 {u v w t : C} :
  (id[u] ⨂ to tensor_assoc) ∘ to (@tensor_assoc C _ u (v ⨂ w) t)
    ≈ to tensor_assoc
        ∘ (to tensor_assoc ∘ (tensor_assoc⁻¹ ⨂ id[t])).
Proof.
  rewrite <- pentagon_cons.
  rewrite <- bimap_comp.
  rewrite iso_to_from, id_left, bimap_id_id, id_right.
  reflexivity.
Qed.

Lemma pentagon_solved2_cons {u v w t z : C}
      (k : z ~> ((u ⨂ (v ⨂ w)) ⨂ t)%object) :
  (id[u] ⨂ to tensor_assoc) ∘ (to (@tensor_assoc C _ u (v ⨂ w) t) ∘ k)
    ≈ to tensor_assoc
        ∘ (to tensor_assoc ∘ ((tensor_assoc⁻¹ ⨂ id[t]) ∘ k)).
Proof.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  apply pentagon_solved2.
Qed.

Lemma pentagon_solved3 {u v w t : C} :
  to (@tensor_assoc C _ u (v ⨂ w) t) ∘ (to tensor_assoc ⨂ id[t])
    ≈ (id[u] ⨂ tensor_assoc⁻¹)
        ∘ (to tensor_assoc ∘ to (@tensor_assoc C _ (u ⨂ v) w t)).
Proof.
  rewrite <- pentagon_a.
  rewrite (bimap_id_cancel_cons tensor_assoc).
  reflexivity.
Qed.

Lemma pentagon_solved3_cons {u v w t z : C}
      (k : z ~> (((u ⨂ v) ⨂ w) ⨂ t)%object) :
  to (@tensor_assoc C _ u (v ⨂ w) t) ∘ ((to tensor_assoc ⨂ id[t]) ∘ k)
    ≈ (id[u] ⨂ tensor_assoc⁻¹)
        ∘ (to tensor_assoc ∘ (to tensor_assoc ∘ k)).
Proof.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  apply pentagon_solved3.
Qed.

Lemma pentagon_from_solved {u v w t : C} :
  tensor_assoc⁻¹
    ∘ ((id[u] ⨂ tensor_assoc⁻¹) ∘ to (@tensor_assoc C _ u v (w ⨂ t)))
    ≈ (to tensor_assoc ⨂ id[t]) ∘ tensor_assoc⁻¹.
Proof.
  apply (iso_to_epic tensor_assoc).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  rewrite <- pentagon_a.
  rewrite (bimap_id_cancel_cons tensor_assoc).
  rewrite (cancel_from_to_cons tensor_assoc).
  reflexivity.
Qed.

Lemma pentagon_from_solved_cons {u v w t z : C}
      (k : z ~> ((u ⨂ v) ⨂ (w ⨂ t))%object) :
  tensor_assoc⁻¹
    ∘ ((id[u] ⨂ tensor_assoc⁻¹)
         ∘ (to (@tensor_assoc C _ u v (w ⨂ t)) ∘ k))
    ≈ (to tensor_assoc ⨂ id[t]) ∘ (tensor_assoc⁻¹ ∘ k).
Proof.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  apply pentagon_from_solved.
Qed.

(* The pentagon, solved for α⁻¹ ∘ (id ⨂ α). / 五边形，对 α⁻¹ ∘ (id ⨂ α) 求解。 *)
Lemma pentagon_step {a b c e : C} :
  (@tensor_assoc C _ a b (c ⨂ e))⁻¹ ∘ id[a] ⨂ to (@tensor_assoc C _ b c e)
    ≈ to (@tensor_assoc C _ (a ⨂ b) c e)
        ∘ (@tensor_assoc C _ a b c)⁻¹ ⨂ id[e]
        ∘ (@tensor_assoc C _ a (b ⨂ c) e)⁻¹.
Proof.
  apply (iso_to_epic (@tensor_assoc C _ a (b ⨂ c)%object e)).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  assert (Ha : to (@tensor_assoc C _ a b c) ⨂ id[e]
                 ∘ ((@tensor_assoc C _ a b c)⁻¹ ⨂ id[e])
                 ≈ id[((a ⨂ (b ⨂ c)) ⨂ e)%object]).
  { rewrite <- bimap_comp.
    rewrite iso_to_from, id_left.
    apply bimap_id_id. }
  rewrite <- (id_right (id[a] ⨂ to (@tensor_assoc C _ b c e) ∘ to tensor_assoc)).
  rewrite <- Ha.
  rewrite (comp_assoc _ (to tensor_assoc ⨂ id[e])).
  rewrite pentagon_identity.
  rewrite !comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.

(** Triangle identities solved for the inverse unitors. / 为逆单位元求解的三角恒等式。 *)

(* α ∘ (ρ⁻¹ ⨂ id) ≈ id ⨂ λ⁻¹ : u ⨂ v ~> u ⨂ (I ⨂ v). / α ∘ (ρ⁻¹ ⨂ id) ≈ id ⨂ λ⁻¹ : u ⨂ v ~> u ⨂ (I ⨂ v). *)
Lemma triangle_inverse_middle {u v : C} :
  to tensor_assoc ∘ (unit_right⁻¹ ⨂ id[v])
    ≈ id[u] ⨂ unit_left⁻¹.
Proof.
  transitivity ((id[u] ⨂ unit_left⁻¹)
                  ∘ ((id[u] ⨂ unit_left)
                       ∘ (to tensor_assoc ∘ (unit_right⁻¹ ⨂ id[v])))).
  - rewrite (comp_assoc (id[u] ⨂ unit_left⁻¹)).
    rewrite <- bimap_comp.
    rewrite iso_from_to.
    rewrite id_left.
    rewrite bimap_id_id.
    rewrite id_left.
    reflexivity.
  - rewrite (comp_assoc (id[u] ⨂ unit_left)).
    rewrite <- triangle_identity.
    rewrite <- bimap_comp.
    rewrite iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    rewrite id_right.
    reflexivity.
Qed.

(* α ∘ (λ⁻¹ ⨂ id) ≈ λ⁻¹ : u ⨂ v ~> I ⨂ (u ⨂ v). *)
Lemma triangle_inverse_left {u v : C} :
  to tensor_assoc ∘ (unit_left⁻¹ ⨂ id[v])
    ≈ (@unit_left C _ (u ⨂ v))⁻¹.
Proof.
  transitivity (unit_left⁻¹
                  ∘ (unit_left
                       ∘ (to tensor_assoc ∘ ((@unit_left C _ u)⁻¹ ⨂ id[v])))).
  - rewrite (comp_assoc (unit_left⁻¹)).
    rewrite iso_from_to.
    rewrite id_left.
    reflexivity.
  - rewrite (comp_assoc unit_left).
    rewrite <- triangle_identity_left.
    rewrite <- bimap_comp.
    rewrite iso_to_from.
    rewrite id_left.
    rewrite bimap_id_id.
    rewrite id_right.
    reflexivity.
Qed.

(* α ∘ ρ⁻¹ ≈ id ⨂ ρ⁻¹ : a ⨂ b ~> a ⨂ (b ⨂ I). *)
Lemma tensor_assoc_unit_right {a b : C} :
  to (@tensor_assoc C _ a b I) ∘ unit_right⁻¹ ≈ id[a] ⨂ unit_right⁻¹.
Proof.
  apply (iso_to_epic (@unit_right C _ (a ⨂ b)%object)).
  rewrite <- comp_assoc.
  rewrite iso_from_to, id_right.
  rewrite bimap_triangle_right.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id, id_left.
  reflexivity.
Qed.

(* α⁻¹ ∘ (id ⨂ λ⁻¹) ≈ ρ⁻¹ ⨂ id : a ⨂ b ~> (a ⨂ I) ⨂ b. / α⁻¹ ∘ (id ⨂ λ⁻¹) ≈ ρ⁻¹ ⨂ id : a ⨂ b ~> (a ⨂ I) ⨂ b. *)
Lemma tensor_assoc_from_unit_left {a b : C} :
  (@tensor_assoc C _ a I b)⁻¹ ∘ id[a] ⨂ unit_left⁻¹ ≈ unit_right⁻¹ ⨂ id[b].
Proof.
  apply (iso_to_monic (@tensor_assoc C _ a I b)).
  rewrite comp_assoc, iso_to_from, id_left.
  (* id ⨂ λ⁻¹ ≈ α ∘ (ρ⁻¹ ⨂ id) *)
  assert (Hr : @unit_right C _ a ⨂ id[b] ∘ ((@unit_right C _ a)⁻¹ ⨂ id[b])
                 ≈ id[(a ⨂ b)%object]).
  { rewrite <- bimap_comp.
    rewrite iso_to_from, id_left.
    apply bimap_id_id. }
  rewrite <- (id_right (id[a] ⨂ unit_left⁻¹)).
  rewrite <- Hr.
  rewrite comp_assoc.
  rewrite triangle_identity.
  rewrite !comp_assoc.
  rewrite <- bimap_comp.
  rewrite iso_from_to, id_left.
  rewrite bimap_id_id, id_left.
  reflexivity.
Qed.

(* Kelly's [unit_identity], inverted: λ_I⁻¹ ≈ ρ_I⁻¹. / Kelly 的 [unit_identity]，倒置：λ_I⁻¹ ≈ ρ_I⁻¹。 *)
Lemma unit_identity_from :
  (@unit_left C _ I)⁻¹ ≈ (@unit_right C _ I)⁻¹.
Proof.
  apply (iso_to_monic unit_left).
  rewrite iso_to_from.
  rewrite unit_identity.
  rewrite iso_to_from.
  reflexivity.
Qed.

End MonoidalToolkit.

(* ------------------------------------------------------------------ *)

Section BraidedUnitors.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(*
 In a symmetric monoidal category the braiding is self-inverse
 ([braid_invol]), hence [braid ⨂ id] is invertible and in particular epic:
 a trailing [braid ⨂ id] may be cancelled on the right. 

 --------
 在对称单模范畴中，编织是自逆的（[braid_invol]），因此[braid ⨂ id]是可逆的，特别是它是满射的：右侧可以消去末尾的[braid ⨂ id]。
*)
Lemma braid_id_cancel {x y z w} (f g : (y ⨂ x) ⨂ z ~> w) :
  f ∘ braid ⨂ id[z] ≈ g ∘ braid ⨂ id[z] → f ≈ g.
Proof.
  intro H1.
  assert (H2 : f ∘ braid ⨂ id[z] ∘ braid ⨂ id[z]
                 ≈ g ∘ braid ⨂ id[z] ∘ braid ⨂ id[z])
    by (rewrite H1; reflexivity).
  rewrite <- !comp_assoc in H2.
  rewrite <- !bimap_comp in H2.
  rewrite !braid_invol in H2.
  rewrite !id_left in H2.
  rewrite !bimap_id_id in H2.
  rewrite !id_right in H2.
  exact H2.
Qed.

(* Joyal & Street, Proposition 2.1: the right unitor is the left unitor composed with the braiding, ρ_x ≈ λ_x ∘ β_{x,I}. / Joyal & Street，命题 2.1：右单位子是左单位子与换位子组成的，ρ_x ≈ λ_x ∘ β_{x,I}。 *)
Theorem braid_unit_left {x : C} :
  unit_left ∘ braid << x ⨂ I ~~> x >> unit_right.
Proof.
  apply tensor_id_left_inj.
  apply (iso_to_epic tensor_assoc).
  apply braid_id_cancel.
  (* Expose the right-hand side of the hexagon at (x, I, I). / 暴露位于 (x, I, I) 的六边形右侧。 *)
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (id[I] ⨂ braid)).
  rewrite <- hexagon_identity.
  rewrite !comp_assoc.
  (*
 Contract the left-hand side: triangle, braid naturality, then the
 derived triangle ρ_{x ⨂ I} ≈ (id ⨂ ρ) ∘ α. 

 --------
 收缩左侧：三角形，编织自然性，然后得到的三角形 ρ_{x ⨂ I} ≈ (id ⨂ ρ) ∘ α。
*)
  rewrite <- triangle_identity.
  rewrite bimap_braid.
  (* Contract the right-hand side to β ∘ ρ via ρ's naturality. / 通过 ρ 的自然性，将右侧收缩到 β ∘ ρ。 *)
  rewrite <- bimap_triangle_right.
  rewrite <- to_unit_right_natural.
  rewrite <- comp_assoc.
  rewrite <- bimap_triangle_right.
  reflexivity.
Qed.

(*
 The mirror coherence: λ_x ≈ ρ_x ∘ β_{I,x}, from [braid_unit_left] by
 pre-composing with the braiding and cancelling via [braid_invol]. 

 --------
 镜像相干性：λ_x ≈ ρ_x ∘ β_{I,x，来自[braid_unit_left]，通过与编织前组合并通过[braid_invol]消去。
*)
Theorem braid_unit_right {x : C} :
  unit_right ∘ braid << I ⨂ x ~~> x >> unit_left.
Proof.
  rewrite <- braid_unit_left.
  rewrite <- comp_assoc.
  rewrite braid_invol.
  apply id_right.
Qed.

(* [braid_unit_left] shuffled across the inverses: β_{x,I} ∘ ρ⁻¹ ≈ λ⁻¹. / [braid_unit_left] 在逆元间洗牌：β_{x,I} ∘ ρ⁻¹ ≈ λ⁻¹。 *)
Corollary braid_unit_left_from {x : C} :
  braid ∘ unit_right⁻¹ << x ~~> I ⨂ x >> unit_left⁻¹.
Proof.
  apply (iso_to_monic unit_left).
  rewrite comp_assoc.
  rewrite braid_unit_left.
  rewrite !iso_to_from.
  reflexivity.
Qed.

(* [braid_unit_right] shuffled across the inverses: β_{I,x} ∘ λ⁻¹ ≈ ρ⁻¹. / [braid_unit_right] 在逆元之间洗牌：β_{I,x} ∘ λ⁻¹ ≈ ρ⁻¹。 *)
Corollary braid_unit_right_from {x : C} :
  braid ∘ unit_left⁻¹ << x ~~> x ⨂ I >> unit_right⁻¹.
Proof.
  apply (iso_to_monic unit_right).
  rewrite comp_assoc.
  rewrite braid_unit_right.
  rewrite !iso_to_from.
  reflexivity.
Qed.

(*
 On the unit object the braiding degenerates to the identity: combine
 [braid_unit_left] at x := I with Kelly's [unit_identity] (λ_I ≈ ρ_I) and
 cancel the monic λ_I. 

 --------
 在单位对象上，交换退化为恒等式：在 x := I 上将 [braid_unit_left] 与 Kelly 的 [unit_identity] (λ_I ≈ ρ_I) 结合，并消去单射 λ_I。
*)
Corollary braid_I_I : braid << I ⨂ I ~~> I ⨂ I >> id.
Proof.
  apply (iso_to_monic unit_left).
  rewrite braid_unit_left.
  rewrite id_right.
  symmetry.
  apply unit_identity.
Qed.

End BraidedUnitors.

(* ------------------------------------------------------------------ *)

(*
   * ** The middle interchange and its coherence

   [swap_inner a b c d : (a ⨂ b) ⨂ (c ⨂ d) ~> (a ⨂ c) ⨂ (b ⨂ d)] braids
   the two middle factors.  The coherence laws — four-slot naturality
   ([swap_inner_natural]), involution ([swap_inner_invol]), braid
   compatibility ([swap_inner_braid]), associativity ([swap_inner_assoc],
   via the two nesting laws [swap_inner_nested] / [swap_inner_nested2],
   plus its inverted form [swap_inner_assoc_inv]) and unit coherence
   ([swap_inner_unit_left2] / [swap_inner_unit_right2] with their solved
   and inverse-orientation forms) — are precisely the conditions making
   the squaring functor [x ↦ x ⨂ x] of a symmetric monoidal category
   symmetric (strong) monoidal.  Everything is stated at general (mixed)
   arguments; the diagonal special cases ([swap_inner_nat1],
   [swap_inner_unit_left] / [swap_inner_unit_right],
   [braid_conjugate_left]) are one-line instances, currently consumed
   only within this file — the copy-discard stack takes its diagonal
   corollaries from CopyDiscard/Deterministic.v instead.  The diagonal [swap_inner x x y y] is definitionally
   Hypergraph.v's [mid_swap_inv]; that identification
   ([swap_inner_diag]) and its corollaries live in
   Structure/Monoidal/CopyDiscard/Deterministic.v, keeping this file
   independent of the hypergraph stack (Hypergraph.v itself instantiates
   [swap_inner_invol] for its [mid_swap_iso] lemmas).

   Mirror forms are kept as citable API even where currently unconsumed
   in-tree: [braid_conjugate_right] (which itself consumes the otherwise
   unconsumed [braid_I_right]). 

   --------
   * ** 中间互换及其连贯性[swap_inner a b c d : (a ⨂ b) ⨂ (c ⨂ d) ~> (a ⨂ c) ⨂ (b ⨂ d)] 编织两个中间因子。相干律——四槽自然性（[swap_inner_natural]）、反演（[swap_inner_invol]）、编织兼容性（[swap_inner_braid]）、结合性（[swap_inner_assoc]，通过两个嵌套律 [swap_inner_nested] / [swap_inner_nested2]，以及它的反向形式 [swap_inner_assoc_inv]）和单位相干（[swap_inner_unit_left2] / [swap_inner_unit_right2]，及其已解决和反向定向形式）——恰好是使对称单体范畴的平方函子 [x ↦ x ⨂ x] 成为对称（强）单体的条件。一切都在一般（混合）参数下陈述；对角线特殊情况（[swap_inner_nat1]、[swap_inner_unit_left] / [swap_inner_unit_right]、[braid_conjugate_left]）是一行实例，目前仅在此文件内使用——复制-丢弃栈从 CopyDiscard/Deterministic.v 中获取其对角推论。对角线 [swap_inner x x y y] 在定义上是 Hypergraph.v 的 [mid_swap_inv]；该识别（[swap_inner_diag]）及其推论存在于 Structure/Monoidal/CopyDiscard/Deterministic.v 中，使得此文件独立于超图堆栈（Hypergraph.v 本身为其 [mid_swap_iso] 引理实例化 [swap_inner_invol]）。

   镜像形式作为可引用的 API 保留，即使当前在树内未被使用：[braid_conjugate_right]（它自身使用了否则未被使用的 [braid_I_right]）。
*)

Section Interchange.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(** Hexagon shapes. / 六边形形状。 *)

Lemma hexagon_a {u v w : C} :
  to tensor_assoc ∘ (@braid C _ u (v ⨂ w)%object ∘ to tensor_assoc)
    ≈ (id[v] ⨂ braid) ∘ (to tensor_assoc ∘ (braid ⨂ id[w])).
Proof.
  rewrite !comp_assoc.
  apply hexagon_identity.
Qed.

(* Braiding an object out of a tensor on its right, solved form. / 从其右侧的张量编织一个物体，求解形式。 *)
Lemma hexagon_a_solved {u v w : C} :
  @braid C _ u (v ⨂ w)%object
    ≈ tensor_assoc⁻¹
        ∘ ((id[v] ⨂ braid)
             ∘ (to tensor_assoc
                  ∘ ((@braid C _ u v ⨂ id[w]) ∘ tensor_assoc⁻¹))).
Proof.
  apply (iso_to_monic tensor_assoc).
  rewrite (cancel_to_from_cons tensor_assoc).
  apply (iso_to_epic tensor_assoc).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  rewrite !comp_assoc.
  apply hexagon_identity.
Qed.

(* Braiding a tensor past an object, solved form. / 将张量穿过一个对象的编织，求解形式。 *)
Lemma hexagon_b {u v w : C} :
  @braid C _ (u ⨂ v)%object w
    ≈ to tensor_assoc
        ∘ ((@braid C _ u w ⨂ id[v])
             ∘ (tensor_assoc⁻¹
                  ∘ ((id[u] ⨂ @braid C _ v w) ∘ to tensor_assoc))).
Proof.
  apply (iso_from_monic tensor_assoc).
  rewrite (cancel_from_to_cons tensor_assoc).
  apply (iso_to_epic (iso_sym tensor_assoc)).
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  rewrite id_right.
  rewrite comp_assoc.
  rewrite hexagon_identity_sym.
  rewrite !comp_assoc.
  reflexivity.
Qed.

(* The rotated hexagon of Symmetric.v, post-composed with the braiding it rotates around: the two inner braids cancel by [braid_invol]. / Symmetric.v 的旋转六边形，与它旋转的编织进行后合成：通过 [braid_invol] 两个内部编织抵消。 *)
Lemma braid_rotate_cancel {u v w : C} :
  to tensor_assoc ∘ (@braid C _ u v ⨂ id[w]) ∘ tensor_assoc⁻¹
    ∘ @braid C _ (v ⨂ w)%object u
    ≈ (id[v] ⨂ @braid C _ w u) ∘ to tensor_assoc.
Proof.
  rewrite hexagon_rotated.
  rewrite <- comp_assoc.
  rewrite braid_invol.
  apply id_right.
Qed.

Lemma braid_rotate_cancel_cons {h u v w z : C}
      (k : z ~> (h ⨂ ((v ⨂ w) ⨂ u))%object) :
  (id[h] ⨂ to tensor_assoc)
    ∘ ((id[h] ⨂ (@braid C _ u v ⨂ id[w]))
         ∘ ((id[h] ⨂ tensor_assoc⁻¹)
              ∘ ((id[h] ⨂ @braid C _ (v ⨂ w)%object u) ∘ k)))
    ≈ (id[h] ⨂ (id[v] ⨂ @braid C _ w u))
        ∘ ((id[h] ⨂ to tensor_assoc) ∘ k).
Proof.
  rewrite !comp_assoc.
  normal.
  comp_right.
  bimap_left.
  apply braid_rotate_cancel.
Qed.

(** Braiding against the unit object, solved for the braid. / 针对单位对象进行编织，求解编织。 *)

Lemma braid_I_left {x : C} :
  @braid C _ I x ≈ unit_right⁻¹ ∘ unit_left.
Proof.
  apply (iso_to_monic unit_right).
  rewrite braid_unit_right.
  rewrite comp_assoc.
  rewrite iso_to_from; cat.
Qed.

Lemma braid_I_right {x : C} :
  @braid C _ x I ≈ unit_left⁻¹ ∘ unit_right.
Proof.
  apply (iso_to_monic unit_left).
  rewrite braid_unit_left.
  rewrite comp_assoc.
  rewrite iso_to_from; cat.
Qed.

(*
 The middle conjugate of [swap_inner I I x y]: braiding I past x between
 two associators is a unitor shuffle. 

 --------
 [swap_inner I I x y] 的中间结合元：在两个结合子之间穿过 x 编织 I 是一个单元洗牌。
*)
Lemma braid_conjugate_left2 {x y : C} :
  to tensor_assoc ∘ (@braid C _ I x ⨂ id[y]) ∘ tensor_assoc⁻¹
    ≈ (id[x] ⨂ unit_left⁻¹) ∘ unit_left.
Proof.
  rewrite braid_I_left.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite triangle_inverse_middle.
  rewrite <- comp_assoc.
  rewrite <- bimap_triangle_left.
  reflexivity.
Qed.

(* The diagonal special case [y := x]. / 对角特殊情况 [y := x]。 *)
Lemma braid_conjugate_left {x : C} :
  to tensor_assoc ∘ (@braid C _ I x ⨂ id[x]) ∘ tensor_assoc⁻¹
    ≈ (id[x] ⨂ unit_left⁻¹) ∘ unit_left.
Proof. exact braid_conjugate_left2. Qed.

(* Mirror image, kept as citable API (see the section header). / 镜像，作为可引用的 API 保留（参见章节标题）。 *)
Lemma braid_conjugate_right {x : C} :
  to tensor_assoc ∘ (@braid C _ x I ⨂ id[I]) ∘ tensor_assoc⁻¹
    ≈ unit_left⁻¹ ∘ (id[x] ⨂ unit_left).
Proof.
  rewrite braid_I_right.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite triangle_inverse_left.
  rewrite <- comp_assoc.
  rewrite <- inverse_triangle_identity.
  reflexivity.
Qed.

(* * *** The interchange of four objects / * *** 四个物体的交换 *)

Definition swap_inner (a b c d : C) :
  (a ⨂ b) ⨂ (c ⨂ d) ~> (a ⨂ c) ⨂ (b ⨂ d) :=
  (@tensor_assoc C _ a c (b ⨂ d))⁻¹
    ∘ bimap id[a] (to (@tensor_assoc C _ c b d))
    ∘ bimap id[a] (bimap (@braid C _ b c) id[d])
    ∘ bimap id[a] ((@tensor_assoc C _ b c d)⁻¹)
    ∘ to (@tensor_assoc C _ a b (c ⨂ d)).

Lemma swap_inner_unfold {a b c d : C} :
  (@tensor_assoc C _ a c (b ⨂ d))⁻¹
    ∘ bimap id[a] (to (@tensor_assoc C _ c b d))
    ∘ bimap id[a] (bimap (@braid C _ b c) id[d])
    ∘ bimap id[a] ((@tensor_assoc C _ b c d)⁻¹)
    ∘ to (@tensor_assoc C _ a b (c ⨂ d))
    ≈ swap_inner a b c d.
Proof. reflexivity. Qed.

(** Naturality of the interchange in all four slots at once. / 四个位置同时交换的自然性。 *)
Lemma swap_inner_natural {a a' b b' c c' d d' : C}
      (f : a ~> a') (g : b ~> b') (h : c ~> c') (k : d ~> d') :
  swap_inner a' b' c' d' ∘ ((f ⨂ g) ⨂ (h ⨂ k))
    ≈ ((f ⨂ h) ⨂ (g ⨂ k)) ∘ swap_inner a b c d.
Proof.
  unfold swap_inner.
  rewrite <- !comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal.
  rewrite from_tensor_assoc_natural.
  normal.
  comp_right.
  comp_left.
  normal.
  bimap_left.
  rewrite to_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  comp_left.
  comp_right.
  normal.
  bimap_right.
  symmetry.
  apply bimap_braid.
Qed.

(*
 The same naturality in mid-composition (“cons”) position, oriented
 for pushing a tensor-of-tensors across the interchange from the
 left. 

 --------
 在中间组合（“cons”）位置相同的自然性，旨在将一个张量的张量从左侧沿互换推送。
*)
Lemma swap_inner_natural_cons {a a' b b' c c' d d' z : C}
      (f : a ~> a') (g : b ~> b') (h : c ~> c') (k : d ~> d')
      (m : z ~> ((a ⨂ b) ⨂ (c ⨂ d))%object) :
  ((f ⨂ h) ⨂ (g ⨂ k)) ∘ (swap_inner a b c d ∘ m)
    ≈ swap_inner a' b' c' d' ∘ (((f ⨂ g) ⨂ (h ⨂ k)) ∘ m).
Proof.
  rewrite comp_assoc.
  rewrite <- swap_inner_natural.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

(* Naturality of the interchange in its first argument. / 其第一个参数交换的自然性。 *)
Lemma swap_inner_nat1 {a a' b c d : C} (f : a ~> a') :
  ((f ⨂ id[c]) ⨂ id[(b ⨂ d)%object]) ∘ swap_inner a b c d
    ≈ swap_inner a' b c d ∘ ((f ⨂ id[b]) ⨂ id[(c ⨂ d)%object]).
Proof.
  spose (swap_inner_natural f (id[b]) (id[c]) (id[d])) as X.
  rewrite !bimap_id_id in X.
  symmetry; apply X.
Qed.

(*
   * Involution: swapping the two middle factors twice is the identity.
   The braid pair inside dies by [braid_invol]. 

   --------
   * 归 involution ：将两个中间因子交换两次就是恒等变换。
   内部的编织对由 [braid_invol] 消亡。
*)
Lemma swap_inner_invol {a b c d : C} :
  swap_inner a c b d ∘ swap_inner a b c d
    ≈ id[((a ⨂ b) ⨂ (c ⨂ d))%object].
Proof.
  unfold swap_inner.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to tensor_assoc) ((tensor_assoc)⁻¹)).
  rewrite iso_to_from, id_left.
  rewrite (comp_assoc (bimap id ((tensor_assoc)⁻¹))
                      (bimap id (to tensor_assoc))).
  rewrite <- bimap_comp, id_left.
  rewrite iso_from_to, bimap_id_id, id_left.
  rewrite (comp_assoc (bimap id (bimap (@braid C _ c b) id[d]))
                      (bimap id (bimap (@braid C _ b c) id[d]))).
  rewrite <- bimap_comp, id_left.
  rewrite <- bimap_comp, id_left.
  rewrite braid_invol, !bimap_id_id, id_left.
  rewrite (comp_assoc (bimap id (to tensor_assoc))
                      (bimap id ((tensor_assoc)⁻¹))).
  rewrite <- bimap_comp, id_left.
  rewrite iso_to_from, bimap_id_id, id_left.
  rewrite iso_from_to.
  reflexivity.
Qed.

Lemma swap_inner_invol_cons {a b c d z : C}
      (k : z ~> ((a ⨂ b) ⨂ (c ⨂ d))%object) :
  swap_inner a c b d ∘ (swap_inner a b c d ∘ k) ≈ k.
Proof.
  rewrite comp_assoc.
  rewrite swap_inner_invol.
  apply id_left.
Qed.

(*
   * Compatibility of the interchange with the braiding: braiding the two
   tensor pairs and interchanging equals interchanging and braiding
   pairwise. 

   --------
   * 交换性与编结的兼容性：对两个张量对进行编结再交换等同于先成对交换再编结。
*)
Lemma swap_inner_braid {a b c d : C} :
  swap_inner c d a b ∘ braid
    ≈ (@braid C _ a c ⨂ @braid C _ b d) ∘ swap_inner a b c d.
Proof.
  apply (iso_to_epic tensor_assoc).
  unfold swap_inner.
  rewrite <- !comp_assoc.
  rewrite hexagon_a.
  rewrite braid_rotate_cancel_cons.
  rewrite hexagon_b.
  rewrite !bimap_comp_id_right.
  rewrite pentagon_cons.
  rewrite to_assoc_nat_cons.
  rewrite bimap_id_id.
  rewrite (cancel_from_to_cons tensor_assoc).
  rewrite <- to_assoc_nat_cons.
  rewrite bimap_id_id.
  rewrite bimap_swap_cons.
  rewrite <- pentagon_a.
  rewrite (bimap_id_cancel_cons tensor_assoc).
  rewrite to_assoc_nat_cons.
  comp_left.
  rewrite !comp_assoc.
  comp_right.
  comp_right.
  rewrite pentagon_solved.
  rewrite !comp_assoc.
  reflexivity.
Qed.

(*
   * The first nesting law: interchanging under a fixed leading tensorand
   equals interchanging with the merged pair.  Pure pentagon bookkeeping
   (the braid inside is inert). 

   --------
   * 第一个嵌套律：在固定的前导张量下交换  
   等于与合并对交换。纯五边形记账  
   （内部的编织是惰性的）。
*)
Lemma swap_inner_nested {u v w e f : C} :
  tensor_assoc⁻¹ ∘ ((id[u] ⨂ swap_inner v w e f) ∘ to tensor_assoc)
    ≈ (to tensor_assoc ⨂ id[(w ⨂ f)%object])
        ∘ (swap_inner (u ⨂ v) w e f ∘ (tensor_assoc⁻¹ ⨂ id[(e ⨂ f)%object])).
Proof.
  unfold swap_inner.
  rewrite <- !comp_assoc.
  rewrite !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite pentagon_solved2.
  rewrite !to_assoc_nat_cons.
  rewrite !bimap_id_id.
  rewrite pentagon_from_solved_cons.
  reflexivity.
Qed.

Lemma swap_inner_nested_cons {u v w e f z : C}
      (k : z ~> ((u ⨂ (v ⨂ w)) ⨂ (e ⨂ f))%object) :
  tensor_assoc⁻¹
    ∘ ((id[u] ⨂ swap_inner v w e f) ∘ (to tensor_assoc ∘ k))
    ≈ (to tensor_assoc ⨂ id[(w ⨂ f)%object])
        ∘ (swap_inner (u ⨂ v) w e f
             ∘ ((tensor_assoc⁻¹ ⨂ id[(e ⨂ f)%object]) ∘ k)).
Proof.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  apply swap_inner_nested.
Qed.

(* [swap_inner_nested] solved for the merged interchange. / [swap_inner_nested] 解决了合并交换的问题。 *)
Lemma swap_inner_unnest {u v w e f : C} :
  swap_inner (u ⨂ v) w e f
    ≈ (tensor_assoc⁻¹ ⨂ id[(w ⨂ f)%object])
        ∘ (tensor_assoc⁻¹
             ∘ ((id[u] ⨂ swap_inner v w e f)
                  ∘ (to tensor_assoc
                       ∘ (to tensor_assoc ⨂ id[(e ⨂ f)%object])))).
Proof.
  rewrite swap_inner_nested_cons.
  rewrite (bimap_cancel_right_cons tensor_assoc).
  rewrite (bimap_cancel_right tensor_assoc).
  rewrite id_right.
  reflexivity.
Qed.

(*
   * The second nesting law: merging the second tensorand of the first
   pair.  Again pure pentagon bookkeeping around [hexagon_b]. 

   --------
   * 第二嵌套定律：合并第一对的第二个张量。再次围绕 [hexagon_b] 进行纯五边形记账。
*)
Lemma swap_inner_nested2 {u v w e f : C} :
  swap_inner u v e (w ⨂ f)
    ∘ (to tensor_assoc ∘ swap_inner (u ⨂ v) w e f)
    ≈ (id[(u ⨂ e)%object] ⨂ to tensor_assoc)
        ∘ (swap_inner u (v ⨂ w) e f ∘ (to tensor_assoc ⨂ id[(e ⨂ f)%object])).
Proof.
  unfold swap_inner.
  rewrite <- !comp_assoc.
  rewrite (cancel_to_from_cons tensor_assoc).
  rewrite !to_assoc_nat_id2_cons.
  rewrite hexagon_b.
  rewrite !bimap_comp_id_right.
  rewrite !bimap_id_split_cons.
  rewrite (bimap_id_fuse_cons (to tensor_assoc ⨂ id[f]) (tensor_assoc⁻¹)).
  rewrite <- pentagon_from_solved.
  rewrite !bimap_id_split_cons.
  rewrite pentagon_solved2_cons.
  rewrite (bimap_cancel_right tensor_assoc).
  rewrite id_right.
  rewrite from_assoc_nat_id2_cons.
  comp_left.
  rewrite !bimap_id_fuse_cons.
  rewrite !comp_assoc.
  comp_right.
  comp_right.
  bimap_left.
  rewrite <- !comp_assoc.
  rewrite pentagon_cons.
  comp_left.
  rewrite <- to_assoc_nat_cons.
  rewrite bimap_id_id.
  comp_left.
  rewrite pentagon_solved_cons.
  comp_left.
  comp_left.
  rewrite <- to_assoc_nat_cons.
  rewrite (cancel_to_from_cons tensor_assoc).
  reflexivity.
Qed.

Lemma swap_inner_nested2_cons {u v w e f z : C}
      (k : z ~> (((u ⨂ v) ⨂ w) ⨂ (e ⨂ f))%object) :
  swap_inner u v e (w ⨂ f)
    ∘ (to tensor_assoc ∘ (swap_inner (u ⨂ v) w e f ∘ k))
    ≈ (id[(u ⨂ e)%object] ⨂ to tensor_assoc)
        ∘ (swap_inner u (v ⨂ w) e f
             ∘ ((to tensor_assoc ⨂ id[(e ⨂ f)%object]) ∘ k)).
Proof.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  apply swap_inner_nested2.
Qed.

(*
   * The core coherence behind associativity: interchanging with a merged
   leading pair equals interchanging with a merged middle pair. 

   --------
   * 结合律背后的核心一致性：与合并的前一对交换等于与合并的中间一对交换。
*)
Lemma swap_inner_core {b c d e f : C} :
  to tensor_assoc
    ∘ ((@braid C _ b (c ⨂ e)%object ⨂ id[(d ⨂ f)%object])
         ∘ ((to tensor_assoc ⨂ id[(d ⨂ f)%object])
              ∘ swap_inner (b ⨂ c) d e f))
    ≈ (id[(c ⨂ e)%object] ⨂ to tensor_assoc)
        ∘ (swap_inner c (b ⨂ d) e f
             ∘ ((to tensor_assoc ⨂ id[(e ⨂ f)%object])
                  ∘ (((@braid C _ b c ⨂ id[d]) ⨂ id[(e ⨂ f)%object])))).
Proof.
  rewrite hexagon_a_solved.
  rewrite !bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (bimap_cancel_right_cons tensor_assoc).
  rewrite pentagon_solved_cons.
  rewrite <- to_assoc_nat_cons.
  rewrite pentagon_solved3_cons.
  rewrite (swap_inner_nat1 braid).
  rewrite !comp_assoc.
  rewrite swap_inner_unfold.
  rewrite <- !comp_assoc.
  rewrite swap_inner_nested2_cons.
  reflexivity.
Qed.

(* Left side of the associativity hexagon, reduced to nested form. / 结合性六边形的左侧，简化为嵌套形式。 *)
Lemma swap_inner_assoc_l {a b c d e f : C} :
  swap_inner a b (c ⨂ e) (d ⨂ f)
    ∘ ((id[(a ⨂ b)%object] ⨂ swap_inner c d e f) ∘ to tensor_assoc)
    ≈ tensor_assoc⁻¹
        ∘ ((id[a]
              ⨂ (to tensor_assoc
                   ∘ ((@braid C _ b (c ⨂ e)%object ⨂ id[(d ⨂ f)%object])
                        ∘ ((to tensor_assoc ⨂ id[(d ⨂ f)%object])
                             ∘ (swap_inner (b ⨂ c) d e f
                                  ∘ (tensor_assoc⁻¹ ⨂ id[(e ⨂ f)%object]))))))
             ∘ (to tensor_assoc ∘ (to tensor_assoc ⨂ id[(e ⨂ f)%object]))).
Proof.
  unfold swap_inner at 1.
  rewrite <- !comp_assoc.
  rewrite to_assoc_nat_id2_cons.
  rewrite <- pentagon_a.
  rewrite !bimap_id_fuse_cons.
  rewrite <- !comp_assoc.
  rewrite swap_inner_nested.
  reflexivity.
Qed.

(* Right side of the associativity hexagon, reduced to nested form. / 结合性六边形的右侧，简化为嵌套形式。 *)
Lemma swap_inner_assoc_r {a b c d e f : C} :
  (to tensor_assoc ⨂ to tensor_assoc)
    ∘ (swap_inner (a ⨂ c) (b ⨂ d) e f
         ∘ (swap_inner a b c d ⨂ id[(e ⨂ f)%object]))
    ≈ tensor_assoc⁻¹
        ∘ ((id[a]
              ⨂ ((id[(c ⨂ e)%object] ⨂ to tensor_assoc)
                   ∘ (swap_inner c (b ⨂ d) e f
                        ∘ ((to tensor_assoc ⨂ id[(e ⨂ f)%object])
                             ∘ (((@braid C _ b c ⨂ id[d]) ⨂ id[(e ⨂ f)%object])
                                  ∘ (tensor_assoc⁻¹ ⨂ id[(e ⨂ f)%object]))))))
             ∘ (to tensor_assoc ∘ (to tensor_assoc ⨂ id[(e ⨂ f)%object]))).
Proof.
  rewrite swap_inner_unnest.
  rewrite <- !comp_assoc.
  rewrite (bimap_fuse_cons (to tensor_assoc) (to tensor_assoc) (tensor_assoc⁻¹)).
  rewrite iso_to_from.
  rewrite id_right.
  rewrite from_assoc_nat_id2_cons.
  rewrite (bimap_fuse_id_right (to tensor_assoc) (swap_inner a b c d)).
  unfold swap_inner at 2.
  rewrite <- !comp_assoc.
  rewrite (cancel_to_from_cons tensor_assoc).
  rewrite !bimap_comp_id_right.
  rewrite <- !to_assoc_nat_cons.
  rewrite !bimap_id_fuse_cons.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(*
   * Associativity of the interchange — the associativity hexagon for the
   squaring functor's monoidal structure. 

   --------
   * 交换的结合性——平方函子单体结构的结合六边形。
*)
Theorem swap_inner_assoc {a b c d e f : C} :
  swap_inner a b (c ⨂ e) (d ⨂ f)
    ∘ ((id[(a ⨂ b)%object] ⨂ swap_inner c d e f) ∘ to tensor_assoc)
    ≈ (to tensor_assoc ⨂ to tensor_assoc)
        ∘ (swap_inner (a ⨂ c) (b ⨂ d) e f
             ∘ (swap_inner a b c d ⨂ id[(e ⨂ f)%object])).
Proof.
  rewrite swap_inner_assoc_l.
  rewrite swap_inner_assoc_r.
  comp_left.
  rewrite !comp_assoc.
  comp_right.
  comp_right.
  bimap_left.
  comp_right.
  rewrite <- !comp_assoc.
  apply swap_inner_core.
Qed.

(*
   * The associativity hexagon, inverted: [swap_inner_assoc] with every
   factor replaced by its inverse (the inverse of an interchange being
   the interchange with the middle slots swapped, by [swap_inner_invol]).
   Both sides are two-sided inverses of [swap_inner_assoc]'s left-hand
   side, so they agree by [comp_inverse_unique]. 

   --------
   * 结合性六边形，倒置：[swap_inner_assoc]，每个因子都被其逆元素替换（互换的逆元素是交换中间槽的互换，即[swap_inner_invol]）。两边都是[swap_inner_assoc] 左边的双侧逆元，所以它们根据[comp_inverse_unique] 是相等的。
*)
Theorem swap_inner_assoc_inv {a b c d e f : C} :
  tensor_assoc⁻¹
    ∘ (id[(a ⨂ b)%object] ⨂ swap_inner c e d f)
    ∘ swap_inner a (c ⨂ e) b (d ⨂ f)
    ≈ (swap_inner a c b d ⨂ id[(e ⨂ f)%object])
        ∘ swap_inner (a ⨂ c) e (b ⨂ d) f
        ∘ (tensor_assoc⁻¹ ⨂ tensor_assoc⁻¹).
Proof.
  apply (comp_inverse_unique
           (swap_inner a b (c ⨂ e) (d ⨂ f)
              ∘ ((id[(a ⨂ b)%object] ⨂ swap_inner c d e f)
                   ∘ to tensor_assoc))).
  - (* The forward hexagon side against the inverted left side. / 前六边形边对着倒置的左边。 *)
    rewrite <- !comp_assoc.
    rewrite (cancel_to_from_cons tensor_assoc).
    rewrite bimap_id_fuse_cons.
    rewrite swap_inner_invol.
    rewrite bimap_id_id, id_left.
    apply swap_inner_invol.
  - (* The inverted right side against the forward hexagon side; here [swap_inner_assoc] itself discharges the composite. / 倒置的右侧对着前方的六边形侧；在这里 [swap_inner_assoc] 本身释放复合物。 *)
    rewrite swap_inner_assoc.
    rewrite <- !comp_assoc.
    rewrite bimap_fuse_cons.
    rewrite !iso_from_to.
    rewrite bimap_id_id, id_left.
    rewrite swap_inner_invol_cons.
    rewrite bimap_fuse_id_right.
    rewrite swap_inner_invol.
    apply bimap_id_id.
Qed.

(* * *** Unit coherence of the interchange / * *** 交换的一致性单位 *)

(* The unit coherence, left form: conjugating [swap_inner I I x y] by the canonical unit isomorphisms is the left unitor. / 单位相干性，左形式：通过规范单位同构对 [swap_inner I I x y] 进行结合是左单位子。 *)
Lemma swap_inner_unit_left2 {x y : C} :
  (unit_left ⨂ unit_left) ∘ swap_inner I I x y
    ∘ (unit_left⁻¹ ⨂ id[(x ⨂ y)%object])
    ≈ @unit_left C _ (x ⨂ y).
Proof.
  unfold swap_inner.
  normal.
  rewrite braid_conjugate_left2.
  rewrite unit_identity_from.
  rewrite <- !comp_assoc.
  rewrite triangle_inverse_middle.
  assert (E : (id[I] ⨂ ((id[x] ⨂ (@unit_left C _ y)⁻¹) ∘ unit_left))
                ∘ (id[I] ⨂ (@unit_left C _ (x ⨂ y))⁻¹)
                ≈ id[I] ⨂ (id[x] ⨂ (@unit_left C _ y)⁻¹)).
  { rewrite <- bimap_comp_id_left.
    bimap_left.
    rewrite <- comp_assoc.
    rewrite iso_to_from.
    apply id_right. }
  rewrite E; clear E.
  rewrite <- from_tensor_assoc_natural.
  rewrite bimap_id_id.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_right.
  rewrite <- bimap_triangle_left.
  reflexivity.
Qed.

(* The diagonal special case [y := x]. / 对角特殊情况 [y := x]。 *)
Lemma swap_inner_unit_left {x : C} :
  (unit_left ⨂ unit_left) ∘ swap_inner I I x x
    ∘ (unit_left⁻¹ ⨂ id[(x ⨂ x)%object])
    ≈ @unit_left C _ (x ⨂ x).
Proof. exact swap_inner_unit_left2. Qed.

(* The unit coherence, right form, derived from the left form through the braid compatibility. / 单位一致性，正确的形式，通过编织兼容性从左侧形式导出。 *)
Lemma swap_inner_unit_right2 {x y : C} :
  (unit_right ⨂ unit_right) ∘ swap_inner x y I I
    ∘ (id[(x ⨂ y)%object] ⨂ unit_left⁻¹)
    ≈ @unit_right C _ (x ⨂ y).
Proof.
  rewrite <- (id_right (swap_inner x y I I)).
  rewrite <- (braid_invol (x := (x ⨂ y)%object) (y := (I ⨂ I)%object)).
  rewrite (comp_assoc (swap_inner x y I I)).
  rewrite swap_inner_braid.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.
  rewrite bimap_fuse_cons.
  rewrite !braid_unit_right.
  rewrite !comp_assoc.
  rewrite swap_inner_unit_left2.
  apply braid_unit_left.
Qed.

(* The diagonal special case [y := x]. / 对角特殊情况 [y := x]。 *)
Lemma swap_inner_unit_right {x : C} :
  (unit_right ⨂ unit_right) ∘ swap_inner x x I I
    ∘ (id[(x ⨂ x)%object] ⨂ unit_left⁻¹)
    ≈ @unit_right C _ (x ⨂ x).
Proof. exact swap_inner_unit_right2. Qed.

(*
 The unit coherences solved for the interchange composite, with the
 inverse unitor moved to the other side. 

 --------
 单位相干性为互换复合体求解，其中逆单位元移动到另一侧。
*)

Lemma swap_inner_unit_left2_solved {x y : C} :
  (unit_left ⨂ unit_left) ∘ swap_inner I I x y
    ≈ @unit_left C _ (x ⨂ y) ∘ (unit_left ⨂ id[(x ⨂ y)%object]).
Proof.
  rewrite <- (id_right ((unit_left ⨂ unit_left) ∘ swap_inner I I x y)).
  assert (E : ((@unit_left C _ I)⁻¹ ⨂ id[(x ⨂ y)%object])
                ∘ (unit_left ⨂ id[(x ⨂ y)%object])
                ≈ id[((I ⨂ I) ⨂ (x ⨂ y))%object]).
  { rewrite bimap_fuse_id_right.
    rewrite iso_from_to.
    apply bimap_id_id. }
  rewrite <- E; clear E.
  rewrite !comp_assoc.
  rewrite swap_inner_unit_left2.
  reflexivity.
Qed.

Lemma swap_inner_unit_right2_solved {x y : C} :
  (unit_right ⨂ unit_right) ∘ swap_inner x y I I
    ≈ @unit_right C _ (x ⨂ y) ∘ (id[(x ⨂ y)%object] ⨂ unit_left).
Proof.
  rewrite <- (id_right ((unit_right ⨂ unit_right) ∘ swap_inner x y I I)).
  assert (E : (id[(x ⨂ y)%object] ⨂ (@unit_left C _ I)⁻¹)
                ∘ (id[(x ⨂ y)%object] ⨂ unit_left)
                ≈ id[((x ⨂ y) ⨂ (I ⨂ I))%object]).
  { rewrite bimap_id_fuse.
    rewrite iso_from_to.
    apply bimap_id_id. }
  rewrite <- E; clear E.
  rewrite !comp_assoc.
  rewrite swap_inner_unit_right2.
  reflexivity.
Qed.

(*
 The unit coherences in the inverse orientation: the interchange
 applied AFTER the doubled inverse unitors is the inverse unitor of
 the tensor, decorated by the unit-object unitor.  These are the exact
 residuals of the counit laws of a tensor comonoid
 (Theory/Algebra/Comonoid/Tensor.v). 

 --------
 逆向排列中的单位相干性：在双重逆单元器之后应用的交换是张量的逆单元器，由单位对象单元器装饰。这些正是张量余单元的余单元律的精确残余（Theory/Algebra/Comonoid/Tensor.v）。
*)

Lemma swap_inner_from_unit_left2 {x y : C} :
  swap_inner I x I y ∘ (unit_left⁻¹ ⨂ unit_left⁻¹)
    ≈ (unit_left⁻¹ ⨂ id[(x ⨂ y)%object]) ∘ (@unit_left C _ (x ⨂ y))⁻¹.
Proof.
  apply (comp_inverse_unique ((unit_left ⨂ unit_left) ∘ swap_inner I I x y)).
  - rewrite <- !comp_assoc.
    rewrite swap_inner_invol_cons.
    rewrite <- bimap_comp.
    rewrite !iso_to_from.
    apply bimap_id_id.
  - rewrite <- !comp_assoc.
    rewrite swap_inner_unit_left2_solved.
    rewrite (cancel_from_to_cons unit_left).
    rewrite bimap_fuse_id_right.
    rewrite iso_from_to.
    apply bimap_id_id.
Qed.

Lemma swap_inner_from_unit_right2 {x y : C} :
  swap_inner x I y I ∘ (unit_right⁻¹ ⨂ unit_right⁻¹)
    ≈ (id[(x ⨂ y)%object] ⨂ unit_left⁻¹) ∘ (@unit_right C _ (x ⨂ y))⁻¹.
Proof.
  apply (comp_inverse_unique ((unit_right ⨂ unit_right) ∘ swap_inner x y I I)).
  - rewrite <- !comp_assoc.
    rewrite swap_inner_invol_cons.
    rewrite <- bimap_comp.
    rewrite !iso_to_from.
    apply bimap_id_id.
  - rewrite <- !comp_assoc.
    rewrite swap_inner_unit_right2_solved.
    rewrite (cancel_from_to_cons unit_right).
    rewrite bimap_id_fuse.
    rewrite iso_from_to.
    apply bimap_id_id.
Qed.

End Interchange.
