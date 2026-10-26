Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Generalizable All Variables.

(*
   * * Categories enriched over 2 are exactly preorders.

   Regard the walking arrow [_2] as the poset of truth values
   {TwoX < TwoY} with its cartesian monoidal structure [Two_Monoidal]
   (tensor := meet, unit := the top TwoY).  A category enriched over
   this monoidal category assigns to every pair of objects a truth
   value [ehom x y : TwoObj], read as the proposition “x ≤ y” (true
   when [ehom x y = TwoY], equivalently when there is an arrow
   [TwoY ~> ehom x y] in [_2]).

   - [eid : TwoY ~> (x ⟿ x)] forces [ehom x x = TwoY]: REFLEXIVITY.
   - [ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z)], with the tensor
   the meet, forces [ehom y z = TwoY → ehom x y = TwoY →
   ehom x z = TwoY]: TRANSITIVITY.
   - The three enrichment laws are equations between parallel arrows
   of the thin category [_2], hence hold automatically.

   Conversely a (decidable) preorder yields an enrichment by letting
   [ehom x y] be the truth value of “x ≤ y”.  Enriched functors
   between such enrichments are exactly the monotone maps.

   This mirrors [Category_is_Enriched_over_Set] in
   Construction/Enriched.v, which recovers ordinary categories by
   enriching over [Sets]. 

   --------
   * * 以 2 为基础的范畴恰好是预序。  

   将行走箭头  [_2]  看作真值的偏序集 {TwoX < TwoY}，并赋予其笛卡尔单体结构  [Two_Monoidal]  
   （张量 := 交，单位 := 顶元 TwoY）。在这个单体范畴上丰富的范畴，会为每一对对象分配一个真值  [ehom x y : TwoObj] ，可理解为命题“x ≤ y”（当  [ehom x y = TwoY] 时为真，等价于在  [_2] 中存在箭头  [TwoY ~> ehom x y] ）。  

   -  [eid : TwoY ~> (x ⟿ x)] 强制  [ehom x x = TwoY] ：自反性。  
   -  [ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z)]，使用交作为张量，强制 [ehom y z = TwoY → ehom x y = TwoY → ehom x z = TwoY]：传递性。  
   - 三条丰富律是在薄范畴 [_2] 中平行箭头之间的方程，因此自动成立。相反，一个（可判定的）前序通过让 [ehom x y] 成为“x ≤ y”的真值来产生一个增强。此类增强之间的增强函子正好是单调映射。

   这与 Construction/Enriched.v 中的 [Category_is_Enriched_over_Set] 相呼应，该文件通过在 [Sets] 上增强来恢复普通范畴。
*)

(*
 In 2, an object receiving an arrow from the top is itself the top. 

 --------
 在2中，从顶部接收箭头的对象本身就是顶部。
*)
Lemma two_from_top {z : TwoObj} : TwoHom TwoY z → z = TwoY.
Proof.
  destruct z; intro f.
  - destruct (TwoHom_Y_X_absurd f).
  - reflexivity.
Qed.

(* The bottom TwoX has an arrow into every object of 2. / 底部的 TwoX 对 2 的每个对象都有一个箭头。 *)
Definition two_bot (z : TwoObj) : TwoHom TwoX z :=
  match z with
  | TwoX => TwoIdX
  | TwoY => TwoXY
  end.

(*
   * A small, self-contained notion of (decidable) preorder.  We keep it
   local and lightweight instead of pulling in stdlib order-theoretic
   typeclasses.  The relation is [Type]-valued; decidability is part of
   the data because building the enrichment requires computing, for
   each pair of carrier elements, an object of [_2] — a truth value —
   from the relation.  Direction (a) below supplies decidability
   automatically, since equality of [TwoObj] is decidable. 

   --------
   * 一个小型的、自包含的（可判定的）预序概念。我们保持其本地化和轻量化，而不是引入标准库的序理论类型类。该关系的取值为  [Type] ；可判定性是数据的一部分，因为构建此增强结构需要为每一对载体元素从关系中计算一个  [_2]  — 一个真值对象。下面方向 (a) 自动提供可判定性，因为  [TwoObj] 的相等性是可判定的。
*)

Record TwoPreorder := {
  tpre_carrier : Type;
  tpre_le : tpre_carrier → tpre_carrier → Type;
  tpre_refl x : tpre_le x x;
  tpre_trans x y z : tpre_le y z → tpre_le x y → tpre_le x z;
  tpre_dec x y : tpre_le x y + (tpre_le x y → False)
}.

(*
   * (a) Every category enriched over 2 gives a preorder on its objects:
   x ≤ y iff the hom truth value is the top. 

   --------
   * (a) 每个在 2 上丰富的范畴都在其对象上给出了一个前序关系：
   当且仅当 Hom 的真值是顶时，x ≤ y。
*)

Definition TwoPreorder_of_Enriched (E : @Enriched _2 Two_Monoidal) :
  TwoPreorder.
Proof.
  unshelve refine {|
    tpre_carrier := @eobj _ _ E;
    tpre_le x y := @ehom _ _ E x y = TwoY
  |}.
  - (* reflexivity, from eid : TwoY ~> (x ⟿ x) / 自反性，来自 eid：TwoY ~> (x ⟿ x) *)
    intro x.
    exact (two_from_top (@eid _ _ E x)).
  - (* transitivity, from ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z) / 传递性, 来自 ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z) *)
    intros x y z Hyz Hxy.
    apply two_from_top.
    pose proof (@ecompose _ _ E x y z) as f.
    simpl in f.
    rewrite Hyz, Hxy in f.
    exact f.
  - (* decidability, since TwoObj has decidable equality / 可判定性，因为 TwoObj 具有可判等性 *)
    intros x y.
    destruct (@ehom _ _ E x y).
    + right; intro H; discriminate H.
    + left; reflexivity.
Defined.

(*
   * (b) Every preorder gives a category enriched over 2, with hom
   truth values computed by the decision procedure. 

   --------
   * (b) 每个前序都给出一个在 2 上增强的范畴，其同态真值由判定程序计算。
*)

Definition ehom_of_le (P : TwoPreorder) (x y : tpre_carrier P) : TwoObj :=
  match tpre_dec P x y with
  | Datatypes.inl _ => TwoY
  | Datatypes.inr _ => TwoX
  end.

Lemma ehom_of_le_complete {P : TwoPreorder} {x y : tpre_carrier P} :
  tpre_le P x y → ehom_of_le P x y = TwoY.
Proof.
  intro l; unfold ehom_of_le.
  destruct (tpre_dec P x y) as [_|n].
  - reflexivity.
  - destruct (n l).
Qed.

Lemma ehom_of_le_sound {P : TwoPreorder} {x y : tpre_carrier P} :
  TwoHom TwoY (ehom_of_le P x y) → tpre_le P x y.
Proof.
  unfold ehom_of_le.
  destruct (tpre_dec P x y) as [l|n]; intro f.
  - exact l.
  - destruct (TwoHom_Y_X_absurd f).
Qed.

Lemma ehom_of_le_empty {P : TwoPreorder} {x y : tpre_carrier P} :
  (tpre_le P x y → False) → ehom_of_le P x y = TwoX.
Proof.
  intro n; unfold ehom_of_le.
  destruct (tpre_dec P x y) as [l|_].
  - destruct (n l).
  - reflexivity.
Qed.

Definition Enriched_of_TwoPreorder (P : TwoPreorder) :
  @Enriched _2 Two_Monoidal.
Proof.
  unshelve refine
    (@Build_Enriched _2 Two_Monoidal
       (tpre_carrier P) (ehom_of_le P) _ _ _ _ _).
  - (* eid : TwoY ~> (x ⟿ x), from reflexivity / eid : TwoY ~> (x ⟿ x)，来自自反性 *)
    intro x.
    rewrite (ehom_of_le_complete (tpre_refl P x)).
    exact TwoIdY.
  - (* ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z), from transitivity; when either factor is the bottom, so is the meet, and the bottom maps into everything / 分解：(y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z)，来自传递性；当任一因子是底时，交集也是底，并且底映射到所有事物 *)
    intros x y z; simpl.
    destruct (tpre_dec P y z) as [lyz|nyz];
    destruct (tpre_dec P x y) as [lxy|nxy].
    + rewrite (ehom_of_le_complete lyz), (ehom_of_le_complete lxy),
        (ehom_of_le_complete (tpre_trans P x y z lyz lxy)).
      exact TwoIdY.
    + rewrite (ehom_of_le_empty nxy), (ehom_of_le_complete lyz).
      exact (two_bot _).
    + rewrite (ehom_of_le_empty nyz).
      exact (two_bot _).
    + rewrite (ehom_of_le_empty nyz).
      exact (two_bot _).
  - (* the three coherence laws hold by thinness of 2 / 三个相干律以2的微小性成立 *)
    intros; apply two_thin.
  - intros; apply two_thin.
  - intros; apply two_thin.
Defined.

(*
   * The promised correspondence: enrichments over 2 on one side,
   preorders on the other, with maps in both directions. 

   --------
   * 承诺的对应关系：一边是大于2的增广，另一边是前序关系，并且有双向映射。
*)

Theorem Enriched_Two_preorder : @Enriched _2 Two_Monoidal ↔ TwoPreorder.
Proof.
  split.
  - exact TwoPreorder_of_Enriched.
  - exact Enriched_of_TwoPreorder.
Defined.

(*
   * The morphism leg: enriched functors between the enrichments built
   from preorders are exactly the monotone maps. 

   --------
   * 形态 leg：从前序构造的丰富化之间的丰富化函子正是单调映射。
*)

Record MonotoneMap (P Q : TwoPreorder) := {
  mono_map : tpre_carrier P → tpre_carrier Q;
  mono_le x y : tpre_le P x y → tpre_le Q (mono_map x) (mono_map y)
}.

Arguments mono_map {P Q}.
Arguments mono_le {P Q}.

Theorem EnrichedFunctor_Two_monotone (P Q : TwoPreorder) :
  EnrichedFunctor _2
    (snd Enriched_Two_preorder P)
    (snd Enriched_Two_preorder Q)
    ↔ MonotoneMap P Q.
Proof.
  split; intro X.
  - (* an enriched functor is monotone: efmap at (x, y) is an arrow between the corresponding truth values / 一个增强函子是单调的：efmap 在 (x, y) 上是一个在相应真值之间的箭头 *)
    destruct X as [f fm _ _]; simpl in *.
    unshelve refine {| mono_map := f |}.
    intros x y l.
    apply ehom_of_le_sound.
    specialize (fm x y).
    rewrite (ehom_of_le_complete l) in fm.
    exact fm.
  - (* a monotone map is an enriched functor / 一个单调映射是一个增强函子 *)
    unshelve refine
      (@Build_EnrichedFunctor _2 Two_Monoidal
         (Enriched_of_TwoPreorder P) (Enriched_of_TwoPreorder Q)
         (mono_map X) _ _ _).
    + (* efmap, by cases on whether x ≤ y holds in P / efmap，按 x ≤ y 在 P 中是否成立分情况 *)
      intros x y; simpl.
      destruct (tpre_dec P x y) as [l|n].
      * rewrite (ehom_of_le_complete l),
          (ehom_of_le_complete (mono_le X x y l)).
        exact TwoIdY.
      * rewrite (ehom_of_le_empty n).
        exact (two_bot _).
    + (* preservation of eid and ecompose hold by thinness of 2 / 通过2的薄度保持eid和ecompose *)
      intros; apply two_thin.
    + intros; apply two_thin.
Defined.
