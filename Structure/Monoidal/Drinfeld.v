Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.

Generalizable All Variables.

(*
   * * The Drinfeld centre Z(C) of a monoidal category

   nLab: https://ncatlab.org/nlab/show/Drinfeld+center
   Wikipedia: https://en.wikipedia.org/wiki/Center_(category_theory)

   This is NOT the premonoidal centre already in the tree.
   Structure/Binoidal/Central.v and Structure/Premonoidal/Centre.v build
   the centre of a *premonoidal* category as the *wide subcategory* of
   *central morphisms* — same objects as the base, morphisms restricted to
   those that commute past the tensor.  The Drinfeld centre is a different
   construction on a *monoidal* category: its OBJECTS are pairs

   (z, a half-braiding on z),

   where a half-braiding is a natural family of isomorphisms
   [half_braid x : z ⨂ x ≅ x ⨂ z] coherent with the tensor (the hexagon
   [half_braid_tensor]), and its morphisms are the base morphisms that
   intertwine the two half-braidings.  Unlike the premonoidal centre — which
   is merely monoidal — the Drinfeld centre is *braided* monoidal, with the
   braiding at ((z, σ), (z', σ')) supplied by the half-braiding component
   [σ z' : z ⨂ z' → z' ⨂ z].  The forgetful functor Z(C) ⟶ C drops the
   half-braiding.

   Orientation matches Structure/Monoidal.v throughout: the associator is
   [tensor_assoc : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z)] (its [to] points to the
   right-nested bracketing), the unitors are [unit_left : I ⨂ x ≅ x] and
   [unit_right : x ⨂ I ≅ x].  The pentagon/associator-naturality shuffles
   and iso-cancellation "cons" lemmas of Structure/Monoidal/Braided/Proofs.v
   (all stated over a bare [Monoidal]) carry the coherence chases. 

   --------
   * * 单范畴的 Drinfeld 中心 Z(C)

   nLab: https://ncatlab.org/nlab/show/Drinfeld+center
   维基百科: https://en.wikipedia.org/wiki/Center_(category_theory)

   这不是树中已有的前单范畴中心。
   Structure/Binoidal/Central.v 和 Structure/Premonoidal/Centre.v 构建了
   *前单范畴* 的中心，作为 *中心态射* 的 *宽子范畴* — 对象与基础相同，态射限制为那些可穿过张量的态射。
   Drinfeld 中心是在 *单范畴* 上的另一种构造：它的对象是对

   (z, z 上的半编织)半编织是一类自然同构的族 [half_braid x : z ⨂ x ≅ x ⨂ z]，与张量相容（六边形 [half_braid_tensor] ），其态射是互相交织两个半编织的基础态射。与只是单范畴的预单范畴中心不同，Drinfeld 中心是*编织*单范畴，其中 ((z, σ), (z', σ')) 的编织由半编织分量 [σ z' : z ⨂ z' → z' ⨂ z] 提供。忘记函子 Z(C) ⟶ C 会舍弃半编织。方向与 Structure/Monoidal.v 完全匹配：结合子是 [tensor_assoc : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z)]（其 [to] 指向右嵌套括号），单位元是 [unit_left : I ⨂ x ≅ x] 和 [unit_right : x ⨂ I ≅ x]。Structure/Monoidal/Braided/Proofs.v 中的五边形/结合子自然性重排和同构消去“cons”引理（全部陈述在裸 [Monoidal] 上）承载了相干性追踪。
*)

Section Drinfeld.

Context {C : Category}.
Context `{M : @Monoidal C}.

(*
   * ** Half-braidings

   A half-braiding on an object [z] is a natural family of isomorphisms
   [β x : z ⨂ x ≅ x ⨂ z] satisfying the hexagon coherence with the tensor.
   (This is "half" a braiding: only the object [z] is braided past
   everything, and only the naturality/hexagon in the *other* variable is
   asked for.) 

   --------
   * ** 半编织

   对象 [z] 的半编织是一个自然同构族 [β x : z ⨂ x ≅ x ⨂ z]，
   满足与张量的六边形相容性。
   （这只是“半”编织：只有对象 [z] 在所有对象之间进行编织，
   并且只要求在*另一个*变量中的自然性/六边形条件。）
*)

Record HalfBraiding (z : C) := {
  half_braid (x : C) : z ⨂ x ≅ x ⨂ z;

  half_braid_natural {x y} (f : x ~> y) :
    to (half_braid y) ∘ (id[z] ⨂ f)
      << z ⨂ x ~~> y ⨂ z >>
    (f ⨂ id[z]) ∘ to (half_braid x);

  half_braid_tensor {x y} :
    to (half_braid (x ⨂ y))
      << z ⨂ (x ⨂ y) ~~> (x ⨂ y) ⨂ z >>
    tensor_assoc⁻¹
      ∘ (id[x] ⨂ to (half_braid y))
      ∘ to tensor_assoc
      ∘ (to (half_braid x) ⨂ id[y])
      ∘ tensor_assoc⁻¹
}.

Arguments half_braid {z} _ _.
Arguments half_braid_natural {z} _ {x y} _.
Arguments half_braid_tensor {z} _ {x y}.

(** A small helper: the tensor of two isomorphisms is an isomorphism. / 一个小帮手：两个同构的张量是同构。 *)

Program Definition iso_bimap {a b c d : C} (i : a ≅ b) (j : c ≅ d) :
  (a ⨂ c) ≅ (b ⨂ d) := {|
  to   := to i ⨂ to j;
  from := from i ⨂ from j
|}.
Next Obligation.
  rewrite <- bimap_comp.
  rewrite !iso_to_from.
  now rewrite bimap_id_id.
Qed.
Next Obligation.
  rewrite <- bimap_comp.
  rewrite !iso_from_to.
  now rewrite bimap_id_id.
Qed.

(*
   * ** The intertwining condition on morphisms

   A base morphism [f : z ~> z'] is a morphism of half-braided objects when
   it commutes with the two half-braidings against every object [x]. 

   --------
   * ** 关于态射的交织条件

   当一个基态射 [f : z ~> z'] 与每个对象 [x] 的两个半交错对换交换时，它就是半交错对象的态射。
*)

Definition half_braiding_morphism {z z' : C}
           (σ : HalfBraiding z) (σ' : HalfBraiding z') (f : z ~> z') : Type :=
  ∀ x, to (half_braid σ' x) ∘ (f ⨂ id[x])
         << z ⨂ x ~~> x ⨂ z' >>
       (id[x] ⨂ f) ∘ to (half_braid σ x).

Lemma half_braiding_morphism_id {z : C} (σ : HalfBraiding z) :
  half_braiding_morphism σ σ (id[z]).
Proof.
  intro x.
  rewrite !bimap_id_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Lemma half_braiding_morphism_comp {z z' z'' : C}
      {σ : HalfBraiding z} {σ' : HalfBraiding z'} {σ'' : HalfBraiding z''}
      {f : z' ~> z''} {g : z ~> z'} :
  half_braiding_morphism σ' σ'' f →
  half_braiding_morphism σ σ' g →
  half_braiding_morphism σ σ'' (f ∘ g).
Proof.
  intros pf pg x.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite pf.
  rewrite <- comp_assoc.
  rewrite pg.
  rewrite comp_assoc.
  rewrite bimap_comp_id_left.
  reflexivity.
Qed.

(* * ** The Drinfeld centre as a category / * ** 德里费尔德中心作为一个范畴 *)

Program Definition Drinfeld : Category := {|
  obj     := { z : C & HalfBraiding z };
  hom     := fun a b => { f : `1 a ~> `1 b
                            & half_braiding_morphism (`2 a) (`2 b) f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun a => (id[`1 a]; half_braiding_morphism_id (`2 a));
  compose := fun a b c f g =>
               (`1 f ∘ `1 g; half_braiding_morphism_comp (`2 f) (`2 g))
|}.

(** The forgetful functor to the base category, dropping the half-braiding. / 忘记函子到基类范畴，丢弃半编织。 *)

Program Definition Drinfeld_Forget : Drinfeld ⟶ C := {|
  fobj := fun a => `1 a;
  fmap := fun _ _ f => `1 f
|}.

(*
   * ** The half-braiding on the unit object

   On [I] the half-braiding is forced by the unitors: [I ⨂ x ≅ x ≅ x ⨂ I],
   i.e. [unit_right⁻¹ ∘ unit_left]. 

   --------
   * ** 关于单位对象的半编织

   在 [I] 上，半编织由单位子强制：[I ⨂ x ≅ x ≅ x ⨂ I]，即 [unit_right⁻¹ ∘ unit_left]。
*)

Definition hb_unit_iso (x : C) : (I ⨂ x) ≅ (x ⨂ I) :=
  iso_compose (iso_sym (@unit_right C M x)) (@unit_left C M x).

Lemma hb_unit_to (x : C) :
  to (hb_unit_iso x) ≈ unit_right⁻¹ ∘ unit_left.
Proof. reflexivity. Qed.

Lemma hb_unit_natural {x y} (f : x ~> y) :
  to (hb_unit_iso y) ∘ (id[I] ⨂ f)
    ≈ (f ⨂ id[I]) ∘ to (hb_unit_iso x).
Proof.
  rewrite !hb_unit_to.
  rewrite comp_assoc.
  rewrite from_unit_right_natural.
  rewrite <- !comp_assoc.
  rewrite <- to_unit_left_natural.
  reflexivity.
Qed.

(*
   * Triangle coherence in cons form, and the inverse right-unitor along the
   associator, which together collapse the unit hexagon. 

   --------
   * 在 cons 形式中的三角一致性，以及沿结合子的逆右单元子，这两者共同使单位六边形收敛。
*)

Lemma tri_cons {a b w} (k : w ~> ((a ⨂ I) ⨂ b)%object) :
  (id[a] ⨂ unit_left) ∘ (to tensor_assoc ∘ k) ≈ (unit_right ⨂ id[b]) ∘ k.
Proof.
  rewrite comp_assoc.
  rewrite <- triangle_identity.
  reflexivity.
Qed.

Lemma tri_rho_inv {a b} :
  tensor_assoc⁻¹ ∘ (id[a] ⨂ (@unit_right C M b)⁻¹)
    ≈ (@unit_right C M (a ⨂ b))⁻¹.
Proof.
  apply (iso_to_monic (@unit_right C M (a ⨂ b))).
  rewrite (iso_to_from (@unit_right C M (a ⨂ b))).
  rewrite bimap_triangle_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to tensor_assoc)).
  rewrite iso_to_from, id_left.
  rewrite <- bimap_comp.
  rewrite iso_to_from, id_left, bimap_id_id.
  reflexivity.
Qed.

Lemma hb_unit_hexagon {x y} :
  to (hb_unit_iso (x ⨂ y))
    ≈ tensor_assoc⁻¹
        ∘ (id[x] ⨂ to (hb_unit_iso y))
        ∘ to tensor_assoc
        ∘ (to (hb_unit_iso x) ⨂ id[y])
        ∘ tensor_assoc⁻¹.
Proof.
  rewrite !hb_unit_to.
  rewrite bimap_comp_id_left, bimap_comp_id_right.
  rewrite <- !comp_assoc.
  (* collapse the right end (λx ⨂ id) ∘ α' ==> λ(x⨂y) / 塌缩右端 (λx ⨂ id) ∘ α' ==> λ(x⨂y) *)
  rewrite <- bimap_triangle_left.
  (* middle triangle: (id ⨂ λy) ∘ (α ∘ ((ρ'x ⨂ id) ∘ λ(x⨂y))) / 中间三角形: (id ⨂ λy) ∘ (α ∘ ((ρ'x ⨂ id) ∘ λ(x⨂y))) *)
  rewrite tri_cons.
  (* cancel (ρx ⨂ id) ∘ (ρ'x ⨂ id) = id / 取消 (ρx ⨂ id) ∘ (ρ'x ⨂ id) = id *)
  rewrite (comp_assoc (unit_right ⨂ id[y])).
  rewrite <- bimap_comp.
  rewrite iso_to_from, id_left, bimap_id_id, id_left.
  (* collapse the left end α'(x,y,I) ∘ (id ⨂ ρ'y) ==> ρ'(x⨂y) / 塌缩左端 α'(x,y,I) ∘ (id ⨂ ρ'y) ==> ρ'(x⨂y) *)
  rewrite comp_assoc.
  rewrite tri_rho_inv.
  reflexivity.
Qed.

Definition hb_unit : HalfBraiding I := {|
  half_braid        := hb_unit_iso;
  half_braid_natural := @hb_unit_natural;
  half_braid_tensor  := @hb_unit_hexagon
|}.

(*
   * ** The half-braiding on a tensor product

   Given half-braidings [σ1] on [z1] and [σ2] on [z2], the object [z1 ⨂ z2]
   carries a half-braiding built by threading [σ1] and [σ2] through the
   associators:

   (z1⨂z2)⨂x →[α] z1⨂(z2⨂x) →[id⨂σ2] z1⨂(x⨂z2)
   →[α⁻¹] (z1⨂x)⨂z2 →[σ1⨂id] (x⨂z1)⨂z2 →[α] x⨂(z1⨂z2). 

   --------
   * ** 张量积上的半交换结构

   给定在  [z1] 上的半交换结构 [σ1] 和在  [z2] 上的半交换结构 [σ2]， 对象 [z1 ⨂ z2]  携带一个通过穿过结合子 [σ1] 和 [σ2] 构建的半交换结构：

   (z1⨂z2)⨂x → [α]  z1⨂(z2⨂x) → [id⨂σ2]  z1⨂(x⨂z2)
   → [α⁻¹]  (z1⨂x)⨂z2 → [σ1⨂id]  (x⨂z1)⨂z2 → [α]  x⨂(z1⨂z2).
*)

Section HBTensor.

Context {z1 z2 : C}.
Context (σ1 : HalfBraiding z1) (σ2 : HalfBraiding z2).

Definition hb_tensor_iso (x : C) : ((z1 ⨂ z2) ⨂ x) ≅ (x ⨂ (z1 ⨂ z2)) :=
  iso_compose (@tensor_assoc C M x z1 z2)
    (iso_compose (iso_bimap (half_braid σ1 x) iso_id)
      (iso_compose (iso_sym (@tensor_assoc C M z1 x z2))
        (iso_compose (iso_bimap iso_id (half_braid σ2 x))
          (@tensor_assoc C M z1 z2 x)))).

Lemma hb_tensor_iso_to (x : C) :
  to (hb_tensor_iso x)
    ≈ to tensor_assoc
        ∘ ((to (half_braid σ1 x) ⨂ id[z2])
             ∘ (tensor_assoc⁻¹
                  ∘ ((id[z1] ⨂ to (half_braid σ2 x))
                       ∘ to tensor_assoc))).
Proof. reflexivity. Qed.

Lemma hb_tensor_natural {x y} (f : x ~> y) :
  to (hb_tensor_iso y) ∘ (id[(z1 ⨂ z2)%object] ⨂ f)
    ≈ (f ⨂ id[(z1 ⨂ z2)%object]) ∘ to (hb_tensor_iso x).
Proof.
  rewrite !hb_tensor_iso_to.
  rewrite <- !comp_assoc.
  (* Step 1: slide (id[z1⨂z2] ⨂ f) past the bottom associator α(z1,z2,·). / 步骤 1：将 (id [z1⨂z2] ⨂ f) 滑过底部结合子 α(z1,z2,·)。 *)
  spose (to_tensor_assoc_natural (id[z1]) (id[z2]) f) as S1.
  rewrite bimap_id_id in S1.
  rewrite <- S1; clear S1.
  (* Step 2: fuse under z1, apply σ2 naturality, split again. / 步骤 2：在 z1 下融合，应用 σ2 的自然性，再次分裂。 *)
  rewrite bimap_id_fuse_cons.
  rewrite (half_braid_natural σ2 f).
  rewrite bimap_id_split_cons.
  (* Step 3: slide (id[z1] ⨂ (f ⨂ id[z2])) past α(z1,·,z2)⁻¹. / 步骤 3：将 (id [z1] ⨂ (f ⨂ id [z2])) 滑过 α(z1,·,z2)⁻¹。 *)
  rewrite <- from_assoc_nat_cons.
  (* Step 4: fuse over z2, apply σ1 naturality, split again. / 第4步：在 z2 上融合，应用 σ1 的自然性，再次分裂。 *)
  rewrite bimap_fuse_cons.
  rewrite id_left.
  rewrite (half_braid_natural σ1 f).
  rewrite bimap_comp_id_right.
  rewrite <- comp_assoc.
  (* Step 5: slide ((f ⨂ id[z1]) ⨂ id[z2]) past the top associator α(·,z1,z2). / 步骤5：将 ((f ⨂ id [z1] ) ⨂ id [z2] ) 滑过顶部结合子 α(·,z1,z2)。 *)
  rewrite <- to_assoc_nat_cons.
  rewrite bimap_id_id.
  reflexivity.
Qed.

(*
   * The hexagon [hb_tensor_hexagon] below is a pure monoidal-coherence
   identity: both sides transport the block [z1 ⨂ z2] past [a ⨂ b] using the
   two component hexagons [half_braid_tensor σ1] and [half_braid_tensor σ2],
   and they differ only in the ORDER of the four elementary half-braids
   (σ1 past a, σ1 past b, σ2 past a, σ2 past b).  After expanding both sides,
   the outer/inner associator scaffolding peels off by pentagon/associator
   shuffles until the discrepancy reduces to commuting the two *independent*
   strands "σ1 past a" and "σ2 past b" — the interchange [crux] below.  These
   private helpers carry that chase; they touch only associators and two
   opaque strands [P], [S], never the half-braidings themselves. 

   --------
   * 下方的六边形 [hb_tensor_hexagon] 是一个纯单体一致性恒等式：两边都使用两个组成六边形 [half_braid_tensor σ1] 和 [half_braid_tensor σ2] 将块 [z1 ⨂ z2] 移过 [a ⨂ b]，它们的区别仅在于四个基本半编织（σ1 经过 a、σ1 经过 b、σ2 经过 a、σ2 经过 b）的顺序。展开两边后，外层/内层结合子结构通过五边形/结合子重排剥离，直到差异缩减为使两条*独立*的线“σ1 经过 a”和“σ2 经过 b”交换——下方的换位 [crux]。这些私有辅助携带该追踪；它们仅接触结合子和两条不透明线 [P]、[S]，从不接触半编织本身。
*)

(* Pentagon, solved for [(id ⨂ α') ∘ α] around a strand — the inverse of the inner-peel move. / 五边形，围绕一股纺纱解决 [(id ⨂ α') ∘ α] — 内剥动作的逆操作。 *)
Lemma P1 (u v p q : C) :
  (id[u] ⨂ (@tensor_assoc C M v p q)⁻¹) ∘ to (@tensor_assoc C M u v (p ⨂ q))
    ≈ to (@tensor_assoc C M u (v ⨂ p) q)
        ∘ ((to (@tensor_assoc C M u v p) ⨂ id[q])
             ∘ (@tensor_assoc C M (u ⨂ v) p q)⁻¹).
Proof.
  symmetry.
  rewrite pentagon_solved3_cons.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(*
 A five-associator loop around a strand collapses to the identity (inverse
 pentagon), and its cons form threading a continuation [k]. 

 --------
 一个五关联环绕一条链会塌缩为单位元（逆五边形），并且它的 cons 形成穿线一个继续 [k]。
*)
Lemma assoc_loop (w x y v : C) :
  to (@tensor_assoc C M (w ⨂ x) y v)
    ∘ ((@tensor_assoc C M w x y)⁻¹ ⨂ id[v]
         ∘ ((@tensor_assoc C M w (x ⨂ y) v)⁻¹
              ∘ (id[w] ⨂ (@tensor_assoc C M x y v)⁻¹
                   ∘ to (@tensor_assoc C M w x (y ⨂ v))))) ≈ id.
Proof.
  transitivity (to (@tensor_assoc C M (w ⨂ x) y v)
                  ∘ (@tensor_assoc C M (w ⨂ x) y v)⁻¹).
  2: { rewrite iso_to_from; reflexivity. }
  f_equiv.
  rewrite !comp_assoc.
  rewrite inverse_pentagon_identity.
  rewrite <- comp_assoc.
  rewrite iso_from_to, id_right.
  reflexivity.
Qed.

Lemma assoc_loop_cons (w x y v u : C)
      (k : u ~> ((w ⨂ x) ⨂ (y ⨂ v))%object) :
  to (@tensor_assoc C M (w ⨂ x) y v)
    ∘ ((@tensor_assoc C M w x y)⁻¹ ⨂ id[v]
         ∘ ((@tensor_assoc C M w (x ⨂ y) v)⁻¹
              ∘ (id[w] ⨂ (@tensor_assoc C M x y v)⁻¹
                   ∘ (to (@tensor_assoc C M w x (y ⨂ v)) ∘ k)))) ≈ k.
Proof.
  rewrite (comp_assoc (id[w] ⨂ (@tensor_assoc C M x y v)⁻¹)).
  rewrite (comp_assoc (@tensor_assoc C M w (x ⨂ y) v)⁻¹).
  rewrite (comp_assoc ((@tensor_assoc C M w x y)⁻¹ ⨂ id[v])).
  rewrite (comp_assoc (to (@tensor_assoc C M (w ⨂ x) y v))).
  rewrite assoc_loop.
  rewrite id_left.
  reflexivity.
Qed.

(* [to i ∘ from i] cancellation in a single tensor slot, cons form. / [to i ∘ from i] 在单个张量槽中的消除，形式为 cons。 *)
Lemma bimap_id_tf_cons {h x y w : C} (i : x ≅ y) (kk : w ~> (h ⨂ y)%object) :
  (id[h] ⨂ to i) ∘ ((id[h] ⨂ i⁻¹) ∘ kk) ≈ kk.
Proof.
  rewrite comp_assoc, <- bimap_comp, iso_to_from, id_left, bimap_id_id, id_left.
  reflexivity.
Qed.

(*
 The independent-strand interchange.  [P] moves [z1] past [a] and [S] moves
 [z2] past [b]; since the two strands are disjoint, the two associator
 scaffolds agree.  Both sides are reduced to the common normal form
 [α ∘ (P ⨂ S) ∘ α] by sliding each strand out (associator naturality) and
 collapsing the residual pure-associator loop ([assoc_loop_cons] on the left,
 an inverse-pentagon cancellation on the right). 

 --------
 独立股交换。[P] 将 [z1] 移过 [a]，而 [S] 将 [z2] 移过 [b]；由于这两条股是互不相交的，两个结合子支架是一致的。通过将每条股滑出（结合子的自然性）并压缩剩余的纯结合子环（左侧的 [assoc_loop_cons]，右侧的逆五边形消去），双方都被化简为共同的规范形式 [α ∘ (P ⨂ S) ∘ α]。
*)
Lemma crux (a b : C) (P : z1 ⨂ a ~> a ⨂ z1) (S : z2 ⨂ b ~> b ⨂ z2)
      {u : C} (k : u ~> (((z1 ⨂ a) ⨂ z2) ⨂ b)%object) :
  to (@tensor_assoc C M a z1 (b ⨂ z2))
  ∘ (to (@tensor_assoc C M (a ⨂ z1) b z2)
     ∘ ((P ⨂ id[b]) ⨂ id[z2]
        ∘ ((@tensor_assoc C M z1 a b)⁻¹ ⨂ id[z2]
           ∘ ((@tensor_assoc C M z1 (a ⨂ b) z2)⁻¹
              ∘ (id[z1] ⨂ (@tensor_assoc C M a b z2)⁻¹
                 ∘ (id[z1] ⨂ (id[a] ⨂ S)
                    ∘ (to (@tensor_assoc C M z1 a (z2 ⨂ b))
                       ∘ (to (@tensor_assoc C M (z1 ⨂ a) z2 b) ∘ k))))))))
  ≈ id[a] ⨂ (id[z1] ⨂ S)
    ∘ (id[a] ⨂ to (@tensor_assoc C M z1 z2 b)
       ∘ (to (@tensor_assoc C M a (z1 ⨂ z2) b)
          ∘ (to (@tensor_assoc C M a z1 z2) ⨂ id[b]
             ∘ ((P ⨂ id[z2]) ⨂ id[b] ∘ k)))).
Proof.
  transitivity (to (@tensor_assoc C M a z1 (b ⨂ z2))
                  ∘ ((P ⨂ S)
                       ∘ (to (@tensor_assoc C M (z1 ⨂ a) z2 b) ∘ k))).
  - rewrite <- to_assoc_nat_id2_cons.
    rewrite <- to_assoc_nat_cons.
    rewrite assoc_loop_cons.
    rewrite bimap_id_id.
    rewrite bimap_fuse_cons.
    rewrite id_left, id_right.
    reflexivity.
  - symmetry.
    rewrite pentagon_solved3_cons.
    rewrite (bimap_id_tf_cons (@tensor_assoc C M z1 z2 b)).
    rewrite <- to_assoc_nat_cons.
    rewrite <- to_assoc_nat_id2_cons.
    rewrite bimap_id_id.
    rewrite bimap_fuse_cons.
    rewrite id_left, id_right.
    reflexivity.
Qed.

Lemma hb_tensor_hexagon {a b} :
  to (hb_tensor_iso (a ⨂ b))
    ≈ tensor_assoc⁻¹
        ∘ (id[a] ⨂ to (hb_tensor_iso b))
        ∘ to tensor_assoc
        ∘ (to (hb_tensor_iso a) ⨂ id[b])
        ∘ tensor_assoc⁻¹.
Proof.
  rewrite !hb_tensor_iso_to.
  rewrite (half_braid_tensor σ1), (half_braid_tensor σ2).
  rewrite !bimap_comp_id_right, !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  (* Peel the outer associator scaffold (pentagon + associator naturality). / 剥离外部联合体支架（五边形 + 联合体自然性）。 *)
  rewrite pentagon_solved_cons.
  rewrite <- to_assoc_nat_cons.
  rewrite pentagon_solved3_cons.
  (* Peel the inner associator scaffold. / 剥离内部连接支架。 *)
  rewrite P1.
  rewrite to_assoc_nat_cons.
  rewrite pentagon_solved2_cons.
  (* The remaining discrepancy is the independent-strand interchange. / 剩下的差异是独立链交换。 *)
  rewrite crux.
  reflexivity.
Qed.

Definition hb_tensor : HalfBraiding (z1 ⨂ z2) := {|
  half_braid        := hb_tensor_iso;
  half_braid_natural := @hb_tensor_natural;
  half_braid_tensor  := @hb_tensor_hexagon
|}.

End HBTensor.

(** The record-level unfolding of the tensor half-braiding. / 张量半编结的记录级展开。 *)

Lemma hb_tensor_to {z1 z2} (σ1 : HalfBraiding z1) (σ2 : HalfBraiding z2)
      (x : C) :
  to (half_braid (hb_tensor σ1 σ2) x)
    ≈ to tensor_assoc
        ∘ ((to (half_braid σ1 x) ⨂ id[z2])
             ∘ (tensor_assoc⁻¹
                  ∘ ((id[z1] ⨂ to (half_braid σ2 x))
                       ∘ to tensor_assoc))).
Proof. exact (hb_tensor_iso_to σ1 σ2 x). Qed.

(*
   * ** Lifting a base isomorphism to the centre

   A base isomorphism whose forward component intertwines the half-braidings
   lifts to an isomorphism of the centre; the inverse intertwines them by the
   lemma below, and the two inverse laws are the underlying base equations. 

   --------
   * ** 提升基对象同构到中心

   一个基对象同构，其正向分量交织半编结
   可提升为中心的同构；根据下面的引理，其逆向交织它们，
   并且这两个逆向律是基本基方程。
*)

Lemma half_braiding_morphism_iso_from {z z' : C}
      (σ : HalfBraiding z) (σ' : HalfBraiding z') (i : z ≅ z') :
  half_braiding_morphism σ σ' (to i) →
  half_braiding_morphism σ' σ (from i).
Proof.
  intros H x.
  spose (H x) as Hx.
  symmetry.
  rewrite <- (id_right (bimap (id[x]) (from i) ∘ to (half_braid σ' x))).
  rewrite <- (bimap_cancel_right (iso_sym i)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (half_braid σ' x))).
  rewrite Hx.
  rewrite <- !comp_assoc.
  rewrite bimap_id_cancel_cons.
  reflexivity.
Qed.

Definition Drinfeld_lift_iso {A B : Drinfeld}
           (i : `1 A ≅ `1 B)
           (ci : half_braiding_morphism (`2 A) (`2 B) (to i)) : A ≅[Drinfeld] B :=
  @Build_Isomorphism Drinfeld A B
    (to i; ci)
    (from i; half_braiding_morphism_iso_from (`2 A) (`2 B) i ci)
    (iso_to_from i)
    (iso_from_to i).

(* * ** Intertwining of the structural isomorphisms with the half-braidings / * ** 结构同构与半缠绕的交织 *)

(* Splitting a [bimap] whose one component is a composite, in cons position. / 分割一个 [bimap]，其一个组成部分是复合体，在 cons 位置。 *)
Lemma bimap_split_right_cons {a b c d e w : C}
      (p : a ~> b) (u : c ~> d) (v : e ~> c) (k : w ~> (a ⨂ e)%object) :
  bimap p (u ∘ v) ∘ k ≈ bimap p u ∘ (bimap id[a] v ∘ k).
Proof.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  reflexivity.
Qed.

Lemma bimap_split_left_cons {a b c d e w : C}
      (u : c ~> d) (v : e ~> c) (p : a ~> b) (k : w ~> (e ⨂ a)%object) :
  bimap (u ∘ v) p ∘ k ≈ bimap u p ∘ (bimap v id[a] ∘ k).
Proof.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  reflexivity.
Qed.

Lemma hb_tensor_bimap_morphism
      {z1 z1' z2 z2' : C}
      {σ1 : HalfBraiding z1} {σ1' : HalfBraiding z1'}
      {σ2 : HalfBraiding z2} {σ2' : HalfBraiding z2'}
      {f : z1 ~> z1'} {g : z2 ~> z2'} :
  half_braiding_morphism σ1 σ1' f →
  half_braiding_morphism σ2 σ2' g →
  half_braiding_morphism (hb_tensor σ1 σ2) (hb_tensor σ1' σ2') (f ⨂ g).
Proof.
  intros pf pg x.
  rewrite !hb_tensor_to.
  rewrite <- !comp_assoc.
  (* Step 1: slide ((f ⨂ g) ⨂ id[x]) past the bottom associator. / 步骤 1：将 ((f ⨂ g) ⨂ id [x]) 滑过底部结合子。 *)
  spose (to_tensor_assoc_natural f g (id[x])) as S1.
  rewrite <- S1; clear S1.
  (* Step 2: fuse under z1, apply σ2 intertwining (pg), split. / 步骤2：在 z1 下融合，应用 σ2 交错作用（pg），分裂。 *)
  rewrite bimap_fuse_cons, id_left, (pg x), bimap_split_right_cons.
  (* Step 3: slide (f ⨂ (id[x] ⨂ g)) past the inverse associator. / 步骤 3：将 (f ⨂ (id [x] ⨂ g)) 滑过逆结合子。 *)
  rewrite <- from_assoc_nat_cons.
  (* Step 4: fuse over z2', apply σ1 intertwining (pf), split. / 第4步：在z2'上熔合，应用σ1交织（pf），分裂。 *)
  rewrite bimap_fuse_cons, id_left, (pf x), bimap_split_left_cons.
  (* Step 5: slide ((id[x] ⨂ f) ⨂ g) past the top associator. / 步骤 5：将 ((id [x] ⨂ f) ⨂ g) 滑过顶部结合子。 *)
  rewrite <- to_assoc_nat_cons.
  reflexivity.
Qed.

(*
   * The unit half-braiding read off its underlying record accessor, so the
   coherence rewrites below fire on [half_braid hb_unit] terms produced by
   [hb_tensor_to]. 

   --------
   * 该单元的半编织从其底层记录访问器读取，因此下面的相干重写会在由 [hb_tensor_to] 产生的 [half_braid hb_unit] 项上触发。
*)

Lemma hb_unit_field_to (x : C) :
  to (half_braid hb_unit x) ≈ unit_right⁻¹ ∘ unit_left.
Proof. exact (hb_unit_to x). Qed.

(*
   * Cons-form triangle and unitor-naturality helpers.  Each keeps the working
   term right-associated so the unit-compatibility chases below are a straight
   line of rewrites collapsing the associators one at a time. 

   --------
   * 构造函数三角形和单位子自然性辅助函数。每个辅助函数都保持工作项为右结合，因此下面的单位兼容性追踪是一条重写的直线，一次折叠一个结合子。
*)

Lemma tri_left_cons {a b w} (k : w ~> (I ⨂ (a ⨂ b))%object) :
  (unit_left ⨂ id[b]) ∘ (tensor_assoc⁻¹ ∘ k) ≈ unit_left ∘ k.
Proof. rewrite comp_assoc, <- bimap_triangle_left; reflexivity. Qed.

Lemma tri_right_cons {a b w} (k : w ~> ((a ⨂ b) ⨂ I)%object) :
  (id[a] ⨂ unit_right) ∘ (to tensor_assoc ∘ k) ≈ unit_right ∘ k.
Proof. rewrite comp_assoc, <- bimap_triangle_right; reflexivity. Qed.

Lemma tri_right_inv_cons {a b w} (k : w ~> (a ⨂ (b ⨂ I))%object) :
  unit_right ∘ (tensor_assoc⁻¹ ∘ k) ≈ (id[a] ⨂ unit_right) ∘ k.
Proof. rewrite comp_assoc, <- triangle_identity_right; reflexivity. Qed.

Lemma ul_nat_cons {a b w} (g : a ~> b) (k : w ~> (I ⨂ a)%object) :
  unit_left ∘ ((id[I] ⨂ g) ∘ k) ≈ g ∘ (unit_left ∘ k).
Proof. rewrite comp_assoc, <- to_unit_left_natural, <- comp_assoc; reflexivity. Qed.

Lemma ur_nat_cons {a b w} (g : a ~> b) (k : w ~> (a ⨂ I)%object) :
  unit_right ∘ ((g ⨂ id[I]) ∘ k) ≈ g ∘ (unit_right ∘ k).
Proof. rewrite comp_assoc, <- to_unit_right_natural, <- comp_assoc; reflexivity. Qed.

(*
   * Cons-form to-then-from cancellation for a single tensor slot; the library's
   [bimap_cancel_right_cons]/[bimap_id_cancel_cons] run from-then-to, and the
   [iso_sym]-conjugated forms do not match syntactically here. 

   --------
   * 单个张量槽的 Cons-form 从-然后-到 取消；库的 [bimap_cancel_right_cons] / [bimap_id_cancel_cons] 从-然后-到 运行，以及 [iso_sym] 共轭形式在这里在语法上不匹配。
*)

Lemma bimap_to_from_cancel_cons {h x y z : C} (i : x ≅ y)
      (k : z ~> (y ⨂ h)%object) :
  (to i ⨂ id[h]) ∘ ((i⁻¹ ⨂ id[h]) ∘ k) ≈ k.
Proof.
  rewrite comp_assoc, <- bimap_comp, iso_to_from, id_left, bimap_id_id, id_left.
  reflexivity.
Qed.

Lemma bimap_id_to_from_cancel_cons {h x y z : C} (i : x ≅ y)
      (k : z ~> (h ⨂ y)%object) :
  (id[h] ⨂ to i) ∘ ((id[h] ⨂ i⁻¹) ∘ k) ≈ k.
Proof.
  rewrite comp_assoc, <- bimap_comp, iso_to_from, id_left, bimap_id_id, id_left.
  reflexivity.
Qed.

(*
   * The left unitor is a morphism of half-braidings [hb_tensor hb_unit σ ⟶ σ].
   Expanding [hb_tensor_to] and the unit half-braiding, the chase collapses the
   outer triangle [(id ⨂ λ) ∘ α = ρ ⨂ id], cancels [ρ ∘ ρ⁻¹], folds the left
   unitor along [α⁻¹], slides [λ] past [σ] by naturality, and lands on the
   remaining triangle. 

   --------
   * 左单位元是半交换结构 [hb_tensor hb_unit σ ⟶ σ] 的一个态射。  
   展开 [hb_tensor_to] 和单位半交换结构后，推图将外部三角形 [(id ⨂ λ) ∘ α = ρ ⨂ id] 压缩，取消 [ρ ∘ ρ⁻¹]，沿着 [α⁻¹] 折叠左单位元，通过自然性将 [λ] 滑过 [σ]，并到达剩余的三角形。
*)

Lemma hb_left_unit_morphism {z : C} (σ : HalfBraiding z) :
  half_braiding_morphism (hb_tensor hb_unit σ) σ (to unit_left).
Proof.
  intro x.
  rewrite hb_tensor_to.
  rewrite hb_unit_field_to.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite tri_cons.
  rewrite (bimap_to_from_cancel_cons unit_right).
  rewrite tri_left_cons.
  rewrite ul_nat_cons.
  rewrite <- triangle_identity_left.
  reflexivity.
Qed.

(*
   * The right unitor is a morphism of half-braidings [hb_tensor σ hb_unit ⟶ σ],
   the mirror chase: collapse [(id ⨂ ρ) ∘ α = ρ], slide [ρ] past [σ], fold
   [ρ⁻¹] along [α⁻¹], cancel [ρ ∘ ρ⁻¹] on the right slot, and finish on the
   outer triangle [(id ⨂ λ) ∘ α = ρ ⨂ id]. 

   --------
   * 右单位元是半交织的一个态射 [hb_tensor σ hb_unit ⟶ σ]，镜像追踪：崩塌 [(id ⨂ ρ) ∘ α = ρ]，滑动 [ρ] 经过 [σ]，沿 [α⁻¹] 折叠 [ρ⁻¹]，在右槽取消 [ρ ∘ ρ⁻¹]，并在外三角形 [(id ⨂ λ) ∘ α = ρ ⨂ id] 完成。
*)

Lemma hb_right_unit_morphism {z : C} (σ : HalfBraiding z) :
  half_braiding_morphism (hb_tensor σ hb_unit) σ (to unit_right).
Proof.
  intro x.
  rewrite hb_tensor_to.
  rewrite hb_unit_field_to.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite tri_right_cons.
  rewrite ur_nat_cons.
  rewrite tri_right_inv_cons.
  rewrite (bimap_id_to_from_cancel_cons unit_right).
  rewrite <- triangle_identity.
  reflexivity.
Qed.

(*
   * Pentagon, solved for the mixed composite [(id ⨂ α⁻¹) ∘ α] that arises
   when the associator produced by sliding the [σd] strand meets the inverse
   associator framing the [σb] strand.  It is [pentagon_step] read across the
   inverses; proved here directly by cancelling the outer [α_{a⨂b,c,e}] (epic)
   and feeding the pentagon to the surviving [α ∘ α] run. 

   --------
   * 五边形，针对混合复合体 [(id ⨂ α⁻¹) ∘ α] 的求解，该复合体在由滑动 [σd] 链产生的结合子遇到框住 [σb] 链的逆结合子时形成。它是跨逆元素读取的 [pentagon_step]；通过直接消去外部 [α_{a⨂b,c,e}]（epic）并将五边形输入剩余的 [α ∘ α] 运行来证明。
*)

Lemma pentagon_helperB {a b c e : C} :
  (id[a] ⨂ (@tensor_assoc C M b c e)⁻¹) ∘ to (@tensor_assoc C M a b (c ⨂ e))
    ≈ to (@tensor_assoc C M a (b ⨂ c) e)
        ∘ ((to (@tensor_assoc C M a b c) ⨂ id[e])
             ∘ (@tensor_assoc C M (a ⨂ b) c e)⁻¹).
Proof.
  apply (iso_to_epic (@tensor_assoc C M (a ⨂ b) c e)).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  rewrite <- pentagon_a.
  rewrite bimap_id_cancel_cons.
  reflexivity.
Qed.

Lemma pentagon_helperB_cons {a b c e w : C}
      (k : w ~> ((a ⨂ b) ⨂ (c ⨂ e))%object) :
  (id[a] ⨂ (@tensor_assoc C M b c e)⁻¹) ∘ (to (@tensor_assoc C M a b (c ⨂ e)) ∘ k)
    ≈ to (@tensor_assoc C M a (b ⨂ c) e)
        ∘ ((to (@tensor_assoc C M a b c) ⨂ id[e])
             ∘ ((@tensor_assoc C M (a ⨂ b) c e)⁻¹ ∘ k)).
Proof.
  rewrite comp_assoc.
  rewrite pentagon_helperB.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(*
   * Associator naturality against a map in the first slot whose remaining two
   slots are a fused identity [id[b ⨂ c]], in cons position.  This slides the
   opaque [σa] strand [f ⨂ id[b⨂c]] past the top associator, re-splitting the
   fused identity into [(f ⨂ id[b]) ⨂ id[c]]. 

   --------
   * 在第一个槽位的映射下的结合子自然性，其余两个槽位为融合恒等 [id[b ⨂ c] ]，位于 cons 位置。这会将不透明的 [σa] 链 [f ⨂ id[b⨂c] ] 滑过顶部结合子，并将融合恒等重新拆分为 [(f ⨂ id[b] ) ⨂ id [c] ]。
*)

Lemma to_assoc_nat_bid_cons {a a' b c w : C} (f : a ~> a')
      (k : w ~> ((a ⨂ b) ⨂ c)%object) :
  (f ⨂ id[(b ⨂ c)%object]) ∘ (to tensor_assoc ∘ k)
    ≈ to tensor_assoc ∘ (((f ⨂ id[b]) ⨂ id[c]) ∘ k).
Proof.
  spose (to_tensor_assoc_natural f (id[b]) (id[c])) as X.
  rewrite bimap_id_id in X.
  rewrite comp_assoc.
  rewrite X.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(*
   * The base associator [α : (za ⨂ zb) ⨂ zd → za ⨂ (zb ⨂ zd)] is a morphism
   of half-braidings between the two bracketings of the tensor half-braiding.
   Pure monoidal coherence: the three half-braid components [σa], [σb], [σd]
   each occur once and are treated as opaque strands (no naturality needed on
   them); every other move is pentagon or associator-naturality.

   After expanding both tensor half-braids and re-associating, the [σa]/[σb]/
   [σd] strands sit in the "right-nested comb" normal form (a single pentagon
   at the bottom folds the last three associators).  The chase then slides
   each strand into its left-nested target position — [σd] and [σa] by plain
   associator naturality ([to_assoc_nat_id2_cons], [to_assoc_nat_bid_cons]),
   [σb] by naturality ([to_assoc_nat_cons]) after a [pentagon_helperB] step
   reframes its surrounding inverse associator — collapsing the intervening
   associator runs with [pentagon_solved2], one [α⁻¹ ∘ α] cancellation and a
   final pentagon, until both sides meet the same distributed comb. 

   --------
   * 基本结合子 [α : (za ⨂ zb) ⨂ zd → za ⨂ (zb ⨂ zd)] 是两个张量半络的括号化之间的半络态射。纯幺半结合性：三个半络分量 [σa]、[σb]、[σd] 每个只出现一次，并作为不透明的线处理（不需要对它们使用自然性）；其他所有操作都是五边形或结合子自然性。在展开两个张量半编织并重新结合后，[σa] / [σb] / [σd] 线保持在“右嵌套梳状”标准形式（底部的一个五边形折叠最后三个结合子）。然后追赶操作将每个线滑入其左嵌套目标位置—— [σd] 和 [σa] 通过普通结合子的自然性 ([to_assoc_nat_id2_cons], [to_assoc_nat_bid_cons])，[σb] 通过自然性 ([to_assoc_nat_cons]) 在一个 [pentagon_helperB] 步骤之后重新框定其周围的反向结合子——将中间结合子序列与 [pentagon_solved2]、一次 [α⁻¹ ∘ α] 抵消以及最后一个五边形折叠起来，直到两边达到相同的分布梳状。
*)

Lemma hb_assoc_morphism {za zb zd : C}
      (σa : HalfBraiding za) (σb : HalfBraiding zb) (σd : HalfBraiding zd) :
  half_braiding_morphism
    (hb_tensor (hb_tensor σa σb) σd)
    (hb_tensor σa (hb_tensor σb σd))
    (to tensor_assoc).
Proof.
  intro x.
  rewrite !hb_tensor_to.
  rewrite <- !comp_assoc.
  (*
 Distribute the inner tensor half-braid under [id[za] ⨂ -] and fold the
 three trailing associators of the LHS into the pentagon normal form. 

 --------
 在 [id[za] ⨂ -] 下分配内张量半编，并将 LHS 的三个尾随结合子折叠成五边形标准形式。
*)
  rewrite !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite pentagon_a.
  (* Slide the [σd] strand into left-nested position. / 将 [σd] 链条滑入左嵌套位置。 *)
  rewrite <- to_assoc_nat_id2_cons.
  (* Reframe the inverse associator around the [σb] strand. / 重新构架 [σb] 链上的逆关联器。 *)
  rewrite pentagon_helperB_cons.
  (* Slide the [σb] strand into left-nested position. / 将 [σb] 链条滑入左嵌套位置。 *)
  rewrite to_assoc_nat_cons.
  (* Collapse the associator run left of the [σb] strand. / 折叠 [σb] 链条左侧的关联器运行。 *)
  rewrite pentagon_solved2_cons.
  (* The surviving [α⁻¹ ∘ α] cancels. / 幸存的 [α⁻¹ ∘ α] 取消了。 *)
  rewrite (cancel_from_to_cons tensor_assoc).
  (* Slide the [σa] strand into left-nested position. / 将 [σa] 链条滑入左嵌套位置。 *)
  rewrite to_assoc_nat_bid_cons.
  (* Fold the two leading associators back through the pentagon. / 将前两个主要关联者折回穿过五边形。 *)
  rewrite <- pentagon_cons.
  (* Distribute the right-hand side's [β_{ab} ⨂ id[zd]] to meet the LHS comb. / 将右侧的 [β_{ab} ⨂ id[zd] ] 分配，以满足左侧的组合。 *)
  rewrite !bimap_comp_id_right.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(* * ** The tensor bifunctor on the centre / * ** 中心上的张量双函子 *)

Program Definition Drinfeld_Tensor : Drinfeld ∏ Drinfeld ⟶ Drinfeld := {|
  fobj := fun p =>
            ((`1 (fst p) ⨂ `1 (snd p))%object;
             hb_tensor (`2 (fst p)) (`2 (snd p)));
  fmap := fun p q fg =>
            (`1 (fst fg) ⨂ `1 (snd fg);
             hb_tensor_bimap_morphism (`2 (fst fg)) (`2 (snd fg)))
|}.
Next Obligation. proper; apply bimap_respects; assumption. Qed.
Next Obligation. apply bimap_comp. Qed.

(*
   * ** Z(C) is monoidal

   Unit, unitors and associator are inherited from C on the underlying
   objects; each is a centre morphism by the intertwining lemmas above, and
   every coherence field is an equation between underlying morphisms of C,
   discharged by C's own monoidal laws. 

   --------
   * ** Z(C) 是幺半群的

   单位、单位子同态和结合子由 C 在其底层对象上继承；每一个都是通过上述交错引理得到的中心态射，并且每一个一致性域都是 C 的底层态射之间的方程，由 C 自身的幺半群律解决。
*)

Definition Drinfeld_unit_left (A : Drinfeld) :
  Drinfeld_Tensor ((I; hb_unit), A) ≅[Drinfeld] A :=
  @Drinfeld_lift_iso (Drinfeld_Tensor ((I; hb_unit), A)) A
    (@unit_left C M (`1 A)) (hb_left_unit_morphism (`2 A)).

Definition Drinfeld_unit_right (A : Drinfeld) :
  Drinfeld_Tensor (A, (I; hb_unit)) ≅[Drinfeld] A :=
  @Drinfeld_lift_iso (Drinfeld_Tensor (A, (I; hb_unit))) A
    (@unit_right C M (`1 A)) (hb_right_unit_morphism (`2 A)).

Definition Drinfeld_tensor_assoc (A B D : Drinfeld) :
  Drinfeld_Tensor (Drinfeld_Tensor (A, B), D)
    ≅[Drinfeld] Drinfeld_Tensor (A, Drinfeld_Tensor (B, D)) :=
  @Drinfeld_lift_iso (Drinfeld_Tensor (Drinfeld_Tensor (A, B), D))
    (Drinfeld_Tensor (A, Drinfeld_Tensor (B, D)))
    (@tensor_assoc C M (`1 A) (`1 B) (`1 D))
    (hb_assoc_morphism (`2 A) (`2 B) (`2 D)).

Program Definition Drinfeld_Monoidal : @Monoidal Drinfeld := {|
  I            := (I; hb_unit);
  tensor       := Drinfeld_Tensor;
  unit_left    := Drinfeld_unit_left;
  unit_right   := Drinfeld_unit_right;
  tensor_assoc := Drinfeld_tensor_assoc
|}.
Next Obligation. apply to_unit_left_natural. Qed.
Next Obligation. apply from_unit_left_natural. Qed.
Next Obligation. apply to_unit_right_natural. Qed.
Next Obligation. apply from_unit_right_natural. Qed.
Next Obligation. apply to_tensor_assoc_natural. Qed.
Next Obligation. apply from_tensor_assoc_natural. Qed.
Next Obligation. apply triangle_identity. Qed.
Next Obligation. apply pentagon_identity. Qed.

(*
   * ** Z(C) is braided

   The braiding at ((z, σ), (z', σ')) is the half-braiding component
   [σ z' : z ⨂ z' → z' ⨂ z].  That this base morphism is a centre morphism —
   it intertwines the two tensor half-braidings [hb_tensor σ σ'] and
   [hb_tensor σ' σ] — is [hb_braid_morphism]: expand both tensor half-braids,
   fold the middle strands back into a single [half_braid σ (·⨂·)] so that the
   naturality of [σ] against the whole strand [σ' x] applies, then re-expand.
   The two hexagons and braiding naturality are then equations between
   underlying morphisms of C, discharged by the half-braiding laws. 

   --------
   * ** Z(C) 是有编织结构的

   在 ((z, σ), (z', σ')) 处的编织是半编织分量 [σ z' : z ⨂ z' → z' ⨂ z]。该基本态射是一个中心态射——它能够交织两个张量半编织 [hb_tensor σ σ'] 和 [hb_tensor σ' σ]——即 [hb_braid_morphism]：展开两个张量半编织，将中间线折叠回单个 [half_braid σ (·⨂·)]，使得 [σ] 对整个线 [σ' x] 的自然性适用，然后重新展开。两个六边形和编织自然性随后是 C 的基础态射之间的方程，通过半编织定律来处理。
*)

(* Naturality of a half-braiding in cons form. / 半编织在共轭形式中的自然性。 *)
Lemma hb_nat_cons {z : C} (σ : HalfBraiding z) {a b w : C} (f : a ~> b)
      (k : w ~> (z ⨂ a)%object) :
  to (half_braid σ b) ∘ ((id[z] ⨂ f) ∘ k)
    ≈ (f ⨂ id[z]) ∘ (to (half_braid σ a) ∘ k).
Proof.
  rewrite comp_assoc, (half_braid_natural σ f), <- comp_assoc.
  reflexivity.
Qed.

(*
 The braiding is a centre morphism: [σ z'] intertwines [hb_tensor σ σ'] and
 [hb_tensor σ' σ].  Both sides reduce to the common midpoint
 [α ∘ half_braid σ (x⨂z') ∘ (id ⨂ σ' x) ∘ α]; the left equality folds the
 [σ]-block by [half_braid_natural σ (σ' x)], the right one is a bare
 associator cancellation after expanding [half_braid σ (x⨂z')]. 

 --------
 编织是一个中心态射：[σ z'] 将 [hb_tensor σ σ'] 和 [hb_tensor σ' σ] 互相联系。两边都归约到公共中点 [α ∘ half_braid σ (x⨂z') ∘ (id ⨂ σ' x) ∘ α]；左边的等式通过 [half_braid_natural σ (σ' x)] 折叠 [σ] 块，右边的是在展开 [half_braid σ (x⨂z')] 后的一个纯结合子消去。
*)
Lemma hb_braid_morphism {z z' : C} (σ : HalfBraiding z) (σ' : HalfBraiding z') :
  half_braiding_morphism (hb_tensor σ σ') (hb_tensor σ' σ) (to (half_braid σ z')).
Proof.
  intro x.
  transitivity (to (@tensor_assoc C M x z' z)
                  ∘ (to (half_braid σ (x ⨂ z'))
                       ∘ ((id[z] ⨂ to (half_braid σ' x))
                            ∘ to (@tensor_assoc C M z z' x)))).
  - (* LHS ≈ midpoint / 左边 ≈ 中点 *)
    rewrite hb_tensor_to.
    symmetry.
    rewrite (hb_nat_cons σ (to (half_braid σ' x))).
    rewrite (half_braid_tensor σ).
    rewrite <- !comp_assoc.
    rewrite iso_from_to, id_right.
    reflexivity.
  - (* midpoint ≈ RHS / 中点 ≈ 右边 *)
    rewrite hb_tensor_to.
    rewrite (half_braid_tensor σ).
    rewrite <- !comp_assoc.
    rewrite (cancel_to_from_cons (@tensor_assoc C M x z' z)).
    reflexivity.
Qed.

Definition Drinfeld_braid (A B : Drinfeld) :
  Drinfeld_Tensor (A, B) ~{Drinfeld}~> Drinfeld_Tensor (B, A) :=
  (to (half_braid (`2 A) (`1 B)); hb_braid_morphism (`2 A) (`2 B)).

Program Definition Drinfeld_Braided : @BraidedMonoidal Drinfeld := {|
  braided_is_monoidal := Drinfeld_Monoidal;
  braid := fun A B => Drinfeld_braid A B
|}.
Next Obligation.
  (*
 braid naturality: intertwine g by its centre-morphism proof, then slide
 h past the σ-half-braid by its naturality. 

 --------
 编织自然性：通过其中心态射证明交错 g，然后通过其自然性将 h 滑过 σ 半编织。
*)
  rewrite <- !comp_assoc.
  rewrite <- (X2 z).
  rewrite <- (hb_nat_cons X3 h (g ⨂ id[z])).
  reflexivity.
Qed.
Next Obligation.
  (* first hexagon: expand [half_braid σa (zb⨂zd)] and cancel the two outer associators framing it. / 第一个六边形：展开 [half_braid σa (zb⨂zd)] 并取消框住它的两个外层结合子。 *)
  rewrite (half_braid_tensor X1).
  rewrite <- !comp_assoc.
  rewrite (cancel_to_from_cons (@tensor_assoc C M y z x)).
  rewrite iso_from_to, id_right.
  reflexivity.
Qed.
Next Obligation.
  (* second hexagon: the tensor half-braid is already expanded by [hb_tensor]; cancel the two outer inverse associators. / 第二个六边形：张量半编已经被 [hb_tensor] 展开；取消两个外部逆结合子。 *)
  rewrite <- !comp_assoc.
  rewrite (cancel_from_to_cons (@tensor_assoc C M z x y)).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

End Drinfeld.

(*
   * Export the base category [C] explicitly on the user-facing constructions,
   so downstream code can write [Drinfeld C], [Drinfeld_Monoidal C], etc.; the
   monoidal structure [M] stays implicit (inferred from context), mirroring
   [Centre C] of Structure/Binoidal/Central.v. 

   --------
   * 在面向用户的构造中显式导出基础类别 [C]，以便下游代码可以编写 [Drinfeld C]、[Drinfeld_Monoidal C] 等；单体结构 [M] 保持隐式（从上下文推断），类似于 Structure/Binoidal/Central.v 的 [Centre C]。
*)

Arguments Drinfeld C {M}.
Arguments Drinfeld_Forget C {M}.
Arguments Drinfeld_Monoidal C {M}.
Arguments Drinfeld_Braided C {M}.

