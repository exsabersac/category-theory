(**
* Probe for Structure/Limit/Diagrams.v (issue #420)

    Pins the measured boundaries of the category of diagrams and its limit
    functor: the two record-level walls that force identity and composition
    to be built componentwise, the hypothesis mismatch behind the colimit
    dual, and — as a compiled countermodel rather than an argument — why the
    comma category over Cat cannot carry the limit's arrow part.  Every
    refutation command below was stripped ONE AT A TIME in a copy of the
    whole file and compiled alone with its error read, so each refusal is
    of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   [W ◯ Id = W] is refused at [eq_refl] ("cannot unify
                     W ◯ Id[A] and W"): functor composition is not strictly
                     unital as a record; the object actions agree (control).
     N2 CONVERSION   [F ◯ (U ◯ W) = (F ◯ U) ◯ W] is refused at [eq_refl]:
                     nor strictly associative; object AND arrow actions
                     agree (controls).
     N3 TYPING       [nat_id] has type [ddiag X ◯ Id ⟹ ddiag X ◯ Id], not
                     [ddiag X ◯ Id ⟹ ddiag X] — the unit wall behind
                     [Did]'s componentwise identity (control).
     N4 TYPING       [nat_compose (dtau g) (dtau f ⊲ dW g)] lands at
                     [(ddiag Z ◯ dW f) ◯ dW g ⟹ ddiag X] where [DHom] wants
                     [ddiag Z ◯ (dW f ◯ dW g) ⟹ ddiag X] — the bracketing
                     wall behind [Dcomp] (control).
     N5 CONVERSION   [@Cocomplete C = @Complete (C^op)] is refused at
                     [eq_refl] ("cannot unify Cocomplete and Complete");
                     the two bridges round-trip at [eq_refl] (controls).
     N6 TYPING       the naive bridge [fun D G => L D G] is refused:
                     [G : D ⟶ C^op] where [D ⟶ C] is expected; the bridge
                     through [Opposite D] and [Opposite_Functor G] is the
                     control.

    Countermodel (positive, compiled): in [CommaDiagrams Sets] the two
    arrows [p420_f_id] and [p420_f_negb] on the one-object diagram constant
    at the two-element setoid share their functor components and differ
    only in their squares (the identity and the swap [negb_iso]);
    [p420_squares_forgotten] proves them equivalent in the comma setoid,
    [p420_id_not_negb] that the squares' components are not, and
    [p420_no_respectful_arrow_part] that no [Proper] assignment of arrows
    can return the square's component on both — so the issue's "comma form
    over Cat" cannot carry a limit functor's arrow part.

    Readbacks: the object and hom types of [Diagrams C], the object and
    arrow parts of [LimDiagrams] and [ColimDiagrams], the apex of the
    reindexed-and-pushed cone, and [CommaDiagrams_equiv].

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the
    binder names [G] and [L] of N5/N6, the six names the refuted
    declarations would introduce, and the instrument's absent name — so a
    renamed or removed constant breaks the build on a positive line rather
    than letting a refutation pass for the wrong reason.

--------
* 结构/极限/图表探测.v（问题 #420）

固定图的类别及其极限函子所测量的边界：强制身份和组合按组件构建的两个记录级别的壁垒、余极限对偶背后的假设不匹配，以及——作为一种已编译的反模型而非论证——为什么Cat上的逗号范畴无法承载极限的箭头部分。下面的每个反驳命令都是在整个文件的副本中一次剥离一个，并单独编译以读取其错误，因此每个拒绝的类型都如其标签所示。

编号：
     仪器      一个缺失的名称，被拒绝 —— 反驳关键词在此文件中。
                     N1 转换   [W ◯ Id = W] 在 [eq_refl] 被拒绝（"无法统一 W ◯ Id[A] 和 W"）：函子组合作为记录不是严格的幺元；对象操作一致（控制）。
                     N2 转换   [F ◯ (U ◯ W) = (F ◯ U) ◯ W] 在 [eq_refl] 被拒绝：也不是严格结合的；对象和箭头操作一致（控制）。
                     N3 类型       [nat_id] 的类型是 [ddiag X ◯ Id ⟹ ddiag X ◯ Id]，而不是 [ddiag X ◯ Id ⟹ ddiag X] —— 单位墙在 [Did] 的分量单位后面（控制）。
                     N4 类型       [nat_compose (dtau g) (dtau f ⊲ dW g)] 落在 [(ddiag Z ◯ dW f) ◯ dW g ⟹ ddiag X]，而 [DHom] 需要 [ddiag Z ◯ (dW f ◯ dW g) ⟹ ddiag X] —— 括号墙在 [Dcomp] 后面（控制）。
N5 转换  [@Cocomplete C = @Complete (C^op)] 在 [eq_refl] 被拒绝（“无法统一 Cocomplete 和 Complete”）；两座桥在 [eq_refl] 完成往返（控制）。N6 类型  朴素桥 [fun D G => L D G] 被拒绝：[G : D ⟶ C^op]，其中期望 [D ⟶ C]；通过 [Opposite D] 和 [Opposite_Functor G] 的桥是控制。

反例模型（正向，已编译）：在 [CommaDiagrams Sets] 中，在单对象图中指向两元素集合的两条箭头 [p420_f_id] 和 [p420_f_negb] 共享它们的函子组件，只在它们的方格（单位和交换 [negb_iso]）中不同；[p420_squares_forgotten] 证明它们在逗号集合中是等价的，[p420_id_not_negb] 证明方格的组件不是等价的，[p420_no_respectful_arrow_part] 证明没有任何 [Proper] 的箭头分配能同时返回方格的组件——所以该问题的“Cat 上的逗号形式”无法携带极限函子的箭头部分。

回读：[Diagrams C] 的对象和同态类型，[LimDiagrams] 和 [ColimDiagrams] 的对象和箭头部分，重新索引并推动的圆锥顶点，以及 [CommaDiagrams_equiv]。

守卫覆盖：每个常量，一个反驳中命名的名称，也在反驳命令之外被命名（最后的守卫块）——例外情况是在去掉注释的普通标识符标记下，为关键字本身、N5/N6 的绑定器名称 [G] 和 [L]、反驳声明可能引入的六个名称，以及器件缺失的名称——因此，重命名或删除的常量会在正向行中导致构建失败，而不是让反驳因错误原因通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.Limit.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Theory.Equivalence.Colimit.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Structure.Limit.Diagrams.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe420_absent_name.

(** ** A: functor composition is neither strictly unital nor associative / ** A：函子组合既不是严格单位元的，也不是结合的 *)

Section Bracketing.

Context {A B C D : Category}.

(* N1 CONVERSION: the unit law of [◯] is not an identity of records / N1 转换：[◯] 的单位法则不是记录的恒等式 *)
Fail Example p420_unit (W : A ⟶ B) : W ◯ Id[A] = W := eq_refl.

(* control: the object action agrees / 控制：对象动作一致 *)
Example p420_unit_fobj (W : A ⟶ B) : fobj[W ◯ Id[A]] = fobj[W] := eq_refl.

(* N2 CONVERSION: nor is associativity / N2 转换：结合性也不是 *)
Fail Example p420_assoc (F : C ⟶ D) (U : B ⟶ C) (W : A ⟶ B) :
  F ◯ (U ◯ W) = (F ◯ U) ◯ W := eq_refl.

(* controls: object and arrow actions agree / 控制：对象和箭头动作一致 *)
Example p420_assoc_fobj (F : C ⟶ D) (U : B ⟶ C) (W : A ⟶ B) :
  fobj[F ◯ (U ◯ W)] = fobj[(F ◯ U) ◯ W] := eq_refl.

Example p420_assoc_fmap (F : C ⟶ D) (U : B ⟶ C) (W : A ⟶ B) {x y : A} (f : x ~> y) :
  fmap[F ◯ (U ◯ W)] f = fmap[(F ◯ U) ◯ W] f := eq_refl.

End Bracketing.

(** ** B: why identity and composition of [Diagrams] are built componentwise / ** B: 为什么 [Diagrams] 的恒等式和组合是按组件构建的 *)

Section Componentwise.

Context {C : Category} {X Y Z : DObj C}.

(* N3 TYPING: the identity transformation lands at [ddiag X ◯ Id ⟹ ddiag X ◯ Id] / N3 输入：身份变换落在 [ddiag X ◯ Id ⟹ ddiag X ◯ Id] *)
Fail Definition p420_Did : DHom X X :=
  {| dW := Id[didx X]; dtau := nat_id |}.

(* control: the componentwise identity / 控制：分量相同的身份 *)
Check (Did X).

(* N4 TYPING: whiskering then composing lands at the other bracketing / N4 打字：先搅拌然后组合落在另一个括号上 *)
Fail Definition p420_Dcomp (f : DHom Y Z) (g : DHom X Y) : DHom X Z :=
  {| dW := dW f ◯ dW g; dtau := nat_compose (dtau g) (dtau f ⊲ (dW g)) |}.

(* control: the componentwise composite / 控制：分量复合 *)
Check (fun (f : DHom Y Z) (g : DHom X Y) => Dcomp f g).

End Componentwise.

(** ** C: the colimit dual's hypothesis / ** C：余极限对偶的假设 *)

Section Dual.

Context {C : Category}.

(* N5 CONVERSION: [Cocomplete C] is not [Complete (C^op)] by conversion / N5 转换：[Cocomplete C] 通过转换不是 [Complete (C^op)] *)
Fail Example p420_cocomplete (L : @Cocomplete C) :
  @Cocomplete C = @Complete (Opposite C) := eq_refl.

(* N6 TYPING: nor is the naive bridge well-typed / N6 输入：天真的桥也不是类型良好的 *)
Fail Definition p420_bridge (L : @Cocomplete C) : @Complete (Opposite C) :=
  fun D G => L D G.

(* controls: the bridges through [(F^op)^op = F], round-tripping at [eq_refl] / 控制：通过 [(F^op)^op = F] 的桥接，在 [eq_refl] 进行往返 *)
Check (@Complete_op_of_Cocomplete C).
Check (@cocomplete_roundtrip C).
Check (@complete_op_roundtrip C).

End Dual.

(** ** D: the comma form over Cat forgets the square — a concrete countermodel / ** D: Cat上的逗号形式忘记了方形——一个具体的反例 *)

Section Countermodel.

(* the one-object diagram in Sets constant at the two-element setoid / 集合中两元素集合的常数一对象图 *)
Definition p420_F : _1 ⟶ Sets := fobj[@Diagonal Sets _1] bool_setoid_object.

Definition p420_X : CommaDiagrams Sets := ((_1, ttt); p420_F).

Program Definition negb_mor : bool_setoid_object ~{Sets}~> bool_setoid_object :=
  {| morphism := negb |}.

Program Definition negb_iso : bool_setoid_object ≅[Sets] bool_setoid_object :=
  {| to := negb_mor; from := negb_mor |}.
Next Obligation.
  intros; simpl in *; repeat match goal with b : bool |- _ => destruct b end; reflexivity.
Qed.
Next Obligation.
  intros; simpl in *; repeat match goal with b : bool |- _ => destruct b end; reflexivity.
Qed.

(* two comma arrows X → X with the same shape functor and different squares / two comma arrows X → X with the same shape functor and different squares / 两个逗号箭头 X → X，具有相同的形状函子但不同的交换图 *)
Definition p420_square (i : bool_setoid_object ≅[Sets] bool_setoid_object) :
  p420_F ∘[Cat] Id[_1] ≈ fmap[@Diagonal Cat _1 Sets] ((@id _1 ttt)) ∘[Cat] p420_F.
Proof.
  exists (fun _ => i).
  intros a b h; simpl.
  intro x; symmetry; exact (iso_from_to i x).
Defined.

Definition p420_f_id : p420_X ~{CommaDiagrams Sets}~> p420_X :=
  ((Id[_1], (@id _1 ttt)); p420_square iso_id).

Definition p420_f_negb : p420_X ~{CommaDiagrams Sets}~> p420_X :=
  ((Id[_1], (@id _1 ttt)); p420_square negb_iso).

(* the comma setoid identifies them / 逗号集合同构识别它们 *)
Lemma p420_squares_forgotten : p420_f_id ≈ p420_f_negb.
Proof. split; reflexivity. Qed.

(* ... but their squares' components differ / ... 但是它们平方的分量不同 *)
Lemma p420_id_not_negb : (@id Sets bool_setoid_object ≈ negb_mor) → False.
Proof. intro H. specialize (H true). simpl in H. discriminate H. Qed.

(*
so no respectful assignment of arrows can read the square back: any
   [m] that sends the two arrows to their square components is refuted

--------
所以没有尊重箭头的赋值可以将平方读回：任何将两个箭头发送到它们的平方分量的 [m] 都被驳回
*)
Lemma p420_no_respectful_arrow_part
  (m : (p420_X ~{CommaDiagrams Sets}~> p420_X) →
       (bool_setoid_object ~{Sets}~> bool_setoid_object))
  (Hm : Proper (equiv ==> equiv) m)
  (H1 : m p420_f_id ≈ id) (H2 : m p420_f_negb ≈ negb_mor) : False.
Proof.
  apply p420_id_not_negb.
  rewrite <- H1, <- H2.
  apply Hm.
  exact p420_squares_forgotten.
Qed.

End Countermodel.

(** ** E: readbacks / ** E：复读 *)

Check (@Diagrams_obj).
Check (@Diagrams_hom).
Check (@LimDiagrams_fobj).
Check (@LimDiagrams_fmap).
Check (@dlim_cone_apex).
Check (@ColimDiagrams_fobj).
Check (@dcolim_is_colimit_apex).
Check (@CommaDiagrams_equiv).

(** ** Guard block / ** 防守格挡 *)

Check @DObj.
Check @didx.
Check @ddiag.
Check @DHom.
Check @dW.
Check @dtau.
Check @DHom_equiv.
Check @DHom_Setoid.
Check @Did.
Check @Dcomp.
Check @Dcomp_respects.
Check @Diagrams.
Check @dlim.
Check @dlim_is.
Check @dlim_cone.
Check @dlim_map.
Check @dlim_map_commutes.
Check @dlim_map_unique.
Check @LimDiagrams.
Check @Complete_op_of_Cocomplete.
Check @cocomplete_of_complete_op.
Check @ColimDiagrams.
Check @dcolim.
Check @CommaDiagrams.
Check @nat_id.
Check @nat_compose.
Check @Cocomplete.
Check @Complete.
Check @Opposite.
Check @Id.
Check @Compose.
Check @fobj.
Check @fmap.
Check @bool_setoid_object.
Check @Diagonal.
Check @Comma.
Check @_1.
Check @ttt.
