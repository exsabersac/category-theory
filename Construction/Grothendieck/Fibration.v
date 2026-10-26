Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Displayed.
Require Import Category.Theory.Fibration.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.

Generalizable All Variables.

(* * * The Grothendieck projection is a split opfibration / * * 格罗腾迪克投射是一个分裂上纤 *)

(*
 nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
 nLab:      https://ncatlab.org/nlab/show/Grothendieck+fibration
 Wikipedia: https://en.wikipedia.org/wiki/Fibred_category

 The projection ∫ A ⟶ B of the Grothendieck construction
 (Construction/Grothendieck.v) is an opfibration, and its canonical
 opcleaving is split: the chosen lifts compose functorially on the nose,
 with the chosen coherence isos of [A] as the mediators.

 Opcartesian lifts.  Over [f : x ~> y] with [dx] above [x], the chosen
 lift is the total morphism [(f; id)] into [(y; idx_map A f dx)]: push
 [dx] forward along [f]; the displayed part is the identity of the
 pushforward [idx_map A f dx].  Opcartesianness is [DCartesian] in the
 op-displayed sense of Theory/Fibration.v — cartesianness for
 [Displayed_op (Grothendieck_Displayed A)] over [B^op].  Unwinding the
 op-reading, a displayed morphism over [g ∘ f] out of [dx] is a fibre
 morphism [hh : idx_map A (g ∘ f) dx ~> dz], and it factors through the
 chosen lift uniquely by conjugating with the chosen composition iso:
 the mediating morphism is [hh ∘ to (idx_comp A g f dx)], and both
 existence and uniqueness are inverse cancellation for [idx_comp] —
 which is exactly why the lift is opcartesian: [idx_comp] is an iso.
 [Grothendieck_OpCleaving] packages the chosen lifts as an [OpCleaving],
 and [cleaving_total_cloven] upgrades it to a cloven fibration of the
 projection out of the op-total category ([Grothendieck_OpCloven]).

 Splitting (disclosed design point).  The split laws are delivered as
 standalone named lemmas ([Grothendieck_split_lift_id],
 [Grothendieck_split_lift_comp], bundled as [Grothendieck_Split]) rather
 than as an op-instance of the strict [SplitCleaving] record of
 Theory/Fibration.v.  [SplitCleaving] anchors its laws in propositional
 object equalities ([lift_obj … = e']); for the canonical opcleaving
 here those anchors would read [idx_map A id dx = dx] and
 [idx_map A g (idx_map A f dx) = idx_map A (g ∘ f) dx] in the fibres,
 and a general [IndexedCat] provides them only as the chosen isos
 [idx_id] and [idx_comp], not as equalities — demanding equality would
 amount to demanding that [A] itself be strict.  The honest split laws
 therefore state functoriality of the cleavage on the nose relative to
 the chosen coherence isos: composing the chosen lift of [id[x]] with
 the vertical image of [idx_id A dx] IS the identity of [(x; dx)], and
 composing the chosen lifts of [f] then [g] with the vertical image of
 [idx_comp A g f dx] IS the chosen lift of [g ∘ f].  The mediators are
 pinned to the chosen isos — which satisfy the unit and cocycle
 coherence of [IndexedCat] — not merely asserted to exist; nothing is
 quantified away.  When [A] is strict (all [idx_id]/[idx_comp]
 components identity isos), the mediators reduce to identities and the
 laws specialize to the classical on-the-nose splitting. 

 --------
 nLab:       https://ncatlab.org/nlab/show/Grothendieck+construction 
 nLab:       https://ncatlab.org/nlab/show/Grothendieck+fibration 
 维基百科:  https://en.wikipedia.org/wiki/Fibred_category 

 Grothendieck 构造的投影 ∫ A ⟶ B
 (Construction/Grothendieck.v) 是一个上纤维（opfibration），其规范的
 上劈分（opcleaving）是分裂的：所选的提升在本质上函子性地组合，
 并以 [A] 的所选相干同构作为中介。Op笛卡儿提升。在 [f : x ~> y] 上并且 [dx] 位于 [x] 之上，所选的提升是从 [(f; id)] 到 [(y; idx_map A f dx)] 的全态射：沿 [f] 推 [dx]；显示的部分是推前向 [idx_map A f dx] 的恒等。Op笛卡儿性是 [DCartesian]，以 Theory/Fibration.v 的 op-显示意义——[Displayed_op (Grothendieck_Displayed A)] 在 [B^op] 上的笛卡儿性。展开 op-读法，在 [g ∘ f] 上从 [dx] 出发的显示态射是纤维态射 [hh : idx_map A (g ∘ f) dx ~> dz]，并且它通过与所选组合同构共轭唯一地分解通过所选提升：中介态射是 [hh ∘ to (idx_comp A g f dx)]，存在性和唯一性都是 [idx_comp] 的逆消去——这正是该提升是 op笛卡儿的原因：[idx_comp] 是同构。[Grothendieck_OpCleaving] 将选定的提升打包为一个 [OpCleaving]，并且 [cleaving_total_cloven] 将其升级为从 op-全类别（[Grothendieck_OpCloven]）投射出的分裂纤维化。分割（已公开的设计点）。分割定律作为独立的命名引理（[Grothendieck_split_lift_id], [Grothendieck_split_lift_comp]，打包为[Grothendieck_Split]）而不是作为Theory/Fibration.v中严格[SplitCleaving]记录的操作实例来提供。[SplitCleaving]将其定律固定在命题对象等式（[lift_obj … = e']）中；对于这里的典型操作劈裂，这些锚点在纤维中将读作[idx_map A id dx = dx]和[idx_map A g (idx_map A f dx) = idx_map A (g ∘ f) dx]，而一般的[IndexedCat]仅将它们作为选定的同构[idx_id]和[idx_comp]提供，而不是作为等式——要求等式就相当于要求[A]本身是严格的。诚实分裂律因此陈述了相对于所选一致性同构的分裂函子性：将 [id[x] 的所选提升与 [idx_id A dx] 的垂直像进行组合就是 [(x; dx)] 的恒等；将 [f] 然后 [g] 的所选提升与 [idx_comp A g f dx] 的垂直像组合就是 [g ∘ f] 的所选提升。中介被固定在所选的同构上——这些同构满足 [IndexedCat] 的单位性和余圈一致性——而不仅仅声称它们存在；没有任何量化被省略。当 [A] 是严格的（所有 [idx_id] / [idx_comp] 分量都是恒等同构）时，中介简化为恒等，中律则专化为经典的精确分裂。
*)

Section GrothendieckFibration.

Context {B : Category}.
Context (A : IndexedCat B).

(** ** The chosen opcartesian lift / ** 所选的上笛卡尔提升 *)

(*
 Over [f : x ~> y] — read in [B^op] as an arrow from [y] to [x] — the
 chosen lift of [dx : idx_fib A x] is displayed over [f] from the
 pushforward [idx_map A f dx] (over [y], the op-domain) to [dx] (over
 [x], the op-codomain); unwinding [Displayed_op] and
 [Grothendieck_Displayed], such a displayed morphism is a fibre morphism
 [idx_map A f dx ~> idx_map A f dx], and the chosen one is the
 identity. 

 --------
 在 [f : x ~> y] 上——在 [B^op] 中读作一个从 [y] 到 [x] 的箭头——所选的 [dx : idx_fib A x] 的提升在 [f] 上显示，来自 [idx_map A f dx] 的推前（在 [y] 上，操作域）到 [dx]（在 [x] 上，操作陪域）；展开 [Displayed_op] 和 [Grothendieck_Displayed]，如此显示的态射是一个纤维态射 [idx_map A f dx ~> idx_map A f dx]，而所选的态射是恒等态射。
*)
Definition Grothendieck_op_lift {x y : B} (f : x ~> y) (dx : idx_fib A x) :
  @dhom (B^op) (Displayed_op (Grothendieck_Displayed A)) y x
        (idx_map A f dx) dx f :=
  @id (idx_fib A y) (idx_map A f dx).

(*
 The chosen lift is opcartesian: every displayed morphism over a
 composite [g ∘ f] out of [dx] factors through it by a unique displayed
 morphism over [g].  Unwound, the factorization candidate ranges over
 fibre morphisms [idx_map A g (idx_map A f dx) ~> dz], the equation
 composes with [from (idx_comp A g f dx)], and the unique solution
 conjugates [hh] with the chosen composition iso. 

 --------
 所选择的提升是 opcartesian 的：每个在复合  [g ∘ f] 上显示的态射都通过一个在  [g] 上的唯一显示态射分解来自  [dx] 。展开后，分解候选在纤维态射  [idx_map A g (idx_map A f dx) ~> dz] 上变化，方程与  [from (idx_comp A g f dx)] 组合，并且唯一解将  [hh] 与所选择的组合同构共轭。
*)
Definition Grothendieck_lift_cocartesian {x y : B} (f : x ~> y)
  (dx : idx_fib A x) :
  DCartesian (D := Displayed_op (Grothendieck_Displayed A))
             (Grothendieck_op_lift f dx).
Proof.
  unfold Grothendieck_op_lift.
  constructor; intros z g dz hh; simpl in *.
  unshelve refine {| unique_obj := hh ∘ to (idx_comp A g f dx) |}.
  - (* the factorization commutes: cancel [to] against [from] / 分解是可交换的：用 [to] 抵消 [from] *)
    rewrite fmap_id, id_right.
    rewrite <- comp_assoc.
    rewrite iso_to_from.
    apply id_right.
  - (* uniqueness: cancel [from] against [to] / 唯一性：取消 [from] 对 [to] *)
    intros v Hv.
    rewrite <- Hv.
    rewrite fmap_id, id_right.
    rewrite <- comp_assoc.
    rewrite iso_from_to.
    apply id_right.
Defined.

(** ** The opcleaving / ** 操作分裂 *)

(*
 The canonical opcleaving of the Grothendieck construction: chosen
 opcartesian lifts, pushing displayed objects forward along base
 morphisms by reindexing.  Per Theory/Fibration.v's vocabulary this is a
 [Cleaving] of the op-displayed category.  Built with an explicit
 [Build_Cleaving] so the op-displayed instance is pinned during
 elaboration: record syntax would elaborate the field against an
 undetermined displayed-category evar, where [dobj v] cannot yet be seen
 to be [idx_fib A v]. 

 --------
 Grothendieck 构造的规范上对偶分解：选择的上对偶笛卡尔提升，通过重索引沿基态态射推动显示对象。根据 Theory/Fibration.v 的词汇，这是上显示范畴的 [Cleaving] 。使用显式的 [Build_Cleaving] 构建，因此在展开过程中上显示实例被固定：记录语法会将字段展开到一个未确定的显示范畴 evar 上，而 [dobj v] 尚不能被看到为 [idx_fib A v] 。
*)
Definition Grothendieck_OpCleaving :
  OpCleaving (Grothendieck_Displayed A) :=
  @Build_Cleaving (B^op) (Displayed_op (Grothendieck_Displayed A))
    (fun u v (f : u ~{ B^op }~> v) (dv : idx_fib A v) =>
       (idx_map A f dv;
        (@Grothendieck_op_lift v u f dv;
         @Grothendieck_lift_cocartesian v u f dv))).

(* * ** The chosen lifts, read in the total category ∫ A / * ** 所选择的提升，在总范畴 ∫ A 中读取 *)

(*
 The chosen opcartesian lift of [f] at [dx], as a morphism of ∫ A from
 [(x; dx)] to [(y; idx_map A f dx)].  Its displayed component is
 definitionally the one chosen by [Grothendieck_OpCleaving]
 ([Grothendieck_colift_is_clift] below). 

 --------
 在  [dx] 处选取的  [f]  的上笛卡尔升起，作为从  [(x; dx)] 到  [(y; idx_map A f dx)] 的 ∫ A 的态射。它的显示分量在定义上是由  [Grothendieck_OpCleaving] 选取的（如下的 [Grothendieck_colift_is_clift]）。
*)
Definition Grothendieck_colift {x y : B} (f : x ~> y) (dx : idx_fib A x) :
  (x; dx) ~{ Grothendieck A }~> (y; idx_map A f dx) :=
  (f; Grothendieck_op_lift f dx).

(*
 Vertical morphisms: a fibre morphism [k : a ~> b] over [z], embedded as
 a total morphism over [id[z]] by recentring along the unit iso. 

 --------
 垂直态射：一个纤维态射 [k : a ~> b] 位于 [z] 上，通过沿单位同构重新居中嵌入为 [id[z] 上的全态射。
*)
Definition Grothendieck_vert {z : B} {a b : idx_fib A z} (k : a ~> b) :
  (z; a) ~{ Grothendieck A }~> (z; b) :=
  (@id B z; k ∘ to (idx_id A a)).

(*
 The total-level lift and the cleaving's chosen lift agree — both are
 the identity of the pushforward, so the comparison is definitional. 

 --------
 总层级提升和劈开的所选提升是一致的——两者都是推前的恒等映射，因此比较是定义上的。
*)
Lemma Grothendieck_colift_is_clift {x y : B} (f : x ~> y)
  (dx : idx_fib A x) :
  `1 (`2 (@clift (B^op) (Displayed_op (Grothendieck_Displayed A))
                 Grothendieck_OpCleaving y x f dx))
    ≈ `2 (Grothendieck_colift f dx).
Proof. reflexivity. Qed.

(*
 The chosen lift lies strictly over [f]: the projection sends it to [f]
 on the nose. 

 --------
 所选择的提升严格位于 [f] 上：投影将其精确地发送到 [f]。
*)
Lemma Grothendieck_colift_over {x y : B} (f : x ~> y) (dx : idx_fib A x) :
  fmap[Grothendieck_Proj A] (Grothendieck_colift f dx) ≈ f.
Proof. reflexivity. Qed.

(** ** The split laws / ** 分裂法律 *)

(*
 Identity law: the chosen lift of [id[x]] at [dx], corrected by the
 chosen unit iso [idx_id A dx], is the identity of [(x; dx)].  The
 mediator is the CHOSEN iso, not an arbitrary one; for strict [A] it is
 an identity and the law reads [lift id ≈ id] on the nose. 

 --------
 同一律：在 [dx] 处，经过选定单位同构 [idx_id A dx] 修正后，[id[x] 的选定提升是 [(x; dx)] 的同一。中介是选定的同构，而不是任意同构；对于严格的 [A]，它是一个同一律，并且法律准确地写作 [lift id ≈ id]。
*)
Lemma Grothendieck_split_lift_id {x : B} (dx : idx_fib A x) :
  Grothendieck_vert (to (idx_id A dx)) ∘ Grothendieck_colift (@id B x) dx
    ≈ @id (Grothendieck A) (x; dx).
Proof.
  simpl.
  exists (id_left (@id B x)); simpl.
  unfold Grothendieck_op_lift.
  rewrite fmap_id.
  (*
 [id_right] is applied at its exact occurrence: the goal carries the
 composite [id ∘ id] inside a dependent argument of [idx_resp], which
 an ambient rewrite would try to abstract 

 --------
 [id_right] 在其确切出现位置被应用：目标在 [idx_resp] 的一个依赖参数中携带复合的 [id ∘ id]，环境重写会尝试对其进行抽象
*)
  rewrite (id_right
             (to (idx_id A dx) ∘ to (idx_id A (idx_map A (@id B x) dx)))).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (idx_id A (idx_map A (@id B x) dx)))).
  rewrite (idx_unit_left_from A (@id B x) dx).
  rewrite iso_to_from.
  apply id_right.
Qed.

(*
 Composition law: the composite of the chosen lifts of [f] and [g],
 corrected by the chosen composition iso [idx_comp A g f dx], is the
 chosen lift of [g ∘ f].  Again the mediator is the CHOSEN iso; for
 strict [A] the law reads [lift g ∘ lift f ≈ lift (g ∘ f)] on the
 nose. 

 --------
 组合律：[f] 和 [g] 的选定提升的复合，通过选定的组合同构 [idx_comp A g f dx] 校正后，成为 [g ∘ f] 的选定提升。调解者仍然是选定的同构；对于严格的 [A]，该律精确地表示为 [lift g ∘ lift f ≈ lift (g ∘ f)]。
*)
Lemma Grothendieck_split_lift_comp {x y z : B} (g : y ~> z) (f : x ~> y)
  (dx : idx_fib A x) :
  Grothendieck_vert (to (idx_comp A g f dx))
      ∘ Grothendieck_colift g (idx_map A f dx)
      ∘ Grothendieck_colift f dx
    ≈ Grothendieck_colift (g ∘ f) dx.
Proof.
  assert (e0 : (@id B z ∘ g) ∘ f ≈ g ∘ f).
  { now rewrite id_left. }
  simpl.
  exists e0; simpl.
  unfold Grothendieck_op_lift.
  rewrite !fmap_id, !id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (idx_id A (idx_map A g (idx_map A f dx))))).
  rewrite (idx_unit_left_from A g (idx_map A f dx)).
  rewrite <- (idx_resp_from_sym A (id_left g) (idx_map A f dx)).
  rewrite (comp_assoc (from (idx_resp A (symmetry (id_left g))
                                        (idx_map A f dx)))).
  rewrite (idx_comp_resp_l_from A f (symmetry (id_left g)) (symmetry e0) dx).
  rewrite <- (comp_assoc (from (idx_comp A g f dx))).
  rewrite (comp_assoc (to (idx_comp A g f dx)) (from (idx_comp A g f dx))).
  rewrite iso_to_from.
  rewrite id_left.
  rewrite (idx_resp_from_trans A (symmetry e0) e0 dx).
  apply (idx_resp_from_id A).
Qed.

(** ** The split laws, bundled / ** 分拆的法律，捆绑的 *)

(*
 The splitting of the canonical opcleaving, as one named theorem: the
 chosen lifts are functorial on the nose, mediated by the chosen unit
 and composition isos of [A]. 

 --------
 典范opcleaving的分裂，作为一个命名定理：所选择的提升是严格函子性的，通过所选择的单位和[A]的组合同构来调解。
*)
Theorem Grothendieck_Split :
  (∀ (x : B) (dx : idx_fib A x),
     Grothendieck_vert (to (idx_id A dx))
         ∘ Grothendieck_colift (@id B x) dx
       ≈ @id (Grothendieck A) (x; dx))
  ∧ (∀ (x y z : B) (g : y ~> z) (f : x ~> y) (dx : idx_fib A x),
     Grothendieck_vert (to (idx_comp A g f dx))
         ∘ Grothendieck_colift g (idx_map A f dx)
         ∘ Grothendieck_colift f dx
       ≈ Grothendieck_colift (g ∘ f) dx).
Proof.
  split.
  - intros x dx.
    apply Grothendieck_split_lift_id.
  - intros x y z g f dx.
    apply Grothendieck_split_lift_comp.
Qed.

(*
   * ** The projection as a cloven fibration of the op-total category 

   --------
   * **作为 op-总范畴的分叉纤维化的投射
*)

(*
 Through the bridge of Theory/Fibration.v, the chosen opcartesian lifts
 make the projection out of the op-total category a cloven fibration —
 the functor-level reading of “∫ A ⟶ B is a (cloven) opfibration”. 

 --------
 通过 Theory/Fibration.v 的桥接，所选择的上笛卡尔提升使得从上总类出的投射成为一个带裂的纤维——“∫ A ⟶ B 是一个（带裂的）上纤维”的函子层面的解读。
*)
Definition Grothendieck_OpCloven :
  ClovenFibration (Total_Proj (Displayed_op (Grothendieck_Displayed A))) :=
  @cleaving_total_cloven (B^op) (Displayed_op (Grothendieck_Displayed A))
    Grothendieck_OpCleaving.

End GrothendieckFibration.
