(** * 大小词汇：小、局部小，以及带 dom-cod 的箭头包装

    Mac Lane 固定 ZFC 加一个宇宙 [U]，当集合、函数或范畴落在 [U] 内时称为小
    （Categories for the Working Mathematician, 2nd ed., §I.6, printed pp. 22-24）。
    Awodey Definition 1.11 称范畴小当其对象 [C0] 与箭头 [C1] 都是集合，Definition 1.12
    称局部小当每个 [Hom(X,Y)] 是集合。Riehl Definition 1.1.6 以「一集合份量的箭头」说同样的话，
    Definition 1.1.7 对局部小同理。

    本库取不同基础路线，docs/SIZE.md 把两者完整并置。简短版：没有宇宙对象、没有成员关系、
    没有大小公理。[Class Category@{o h p}]（Theory/Category.v）是宇宙*多态*的，故每个范畴
    已携带各自三个层级，Mac Lane 的 [U] 所做的工作由 elaborator 的约束求解器完成。这正是
    自成员是宇宙不一致而非要用公理排除的悖论的原因（Instance/Cat.v）。

    本文件添加什么，以及为何不冗余。上述纪律被强制但曾*不可陈述*：此前文件树中任何地方
    都没有 `Small`、`IsSmall`、`LocallySmall` 的声明，故小性既不能作假设也不能作结论——
    只能在定义点通过实例化宇宙来选择。Theory/Lawvere/Sets.v 顺便记录后果（「库没有小性机制」）。
    下文谓词即那缺失的词汇。

    设计，以及使之成立的一件事。范畴相对一对层级是小的，当其对象与每个 hom-setoid 在那些
    层级有匹配副本。全部内容在严格约束 [uo < o] 与 [uh < h]：没有它们，对每个 [C] 都可把
    [obj[C]] 与 [hom] 自身交回以消解 [Small C]，谓词将空虚为真。有了它们，该消解是宇宙不一致——
    Test/Size.v 恰展示这一点，因演示需要拒绝方言，本文件避免之，使 [make todo] 扫描不见新命中。

    对象用 [=]，hom 用 [≈]。对象在本库无 setoid，故对象类型的双射是 Leibniz；与
    Instance/StrictCat.v 的处理一致。态射有 setoid，且 CLAUDE.md 的常设规则是从不在其上用 [=]，
    故 hom 半边是 setoid 同构。这不是风格选择：用 [=] 陈述 hom 往返也会被*拒绝*，因它拖入的
    [eq] 引理施加声明宇宙绑定无法提及的约束（[h <= eq_ind.u0]）。

    双边局面，按原样记录。库*提供*的比书中约定更强：[Class Category] 的 [homset] 字段
    （Theory/Category.v）给每个范畴固定层级 [h] 的 hom-setoid，故局部小性由构造成立，
    非局部小范畴不可表达。下文 [locally_small_ambient] 把它记为引理而非散文，使观察可检查。
    库*缺少*的是陈述该区分所需的谓词，这正是 [LocallySmall] 所提供。因此 [LocallySmall]
    以非严格 [uh <= h] 陈述，使环境实例存在；[Small] 以严格约束陈述，使之有内容。两种读法
    都是刻意的，都不是疏忽。

    书目仅按位置引用。撰写本文件时未查阅印刷正文；位置记录各定义在何处陈述，下文 Coq
    自立。归属依 issue jwiegley/category-theory#253 所供。 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.One.

Generalizable All Variables.

(* * ** A level-polymorphic 恒等 type 对象 （已译） *)

(*
   本节说明 Size 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive ObjEq@{u} {A : Type@{u}} : A → A → Type@{u} :=
  obj_refl : ∀ a : A, ObjEq a a.

Arguments obj_refl {A} a.


(** ** Local smallness *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class LocallySmall@{o h p uh up | h <= p, uh <= up, uh <= h}
      (C : Category@{o h p}) := {
  ls_hom     : ∀ (x y : C), Type@{uh};
  ls_setoid  : ∀ x y, Setoid@{uh up} (ls_hom x y);

  ls_to      : ∀ {x y}, ls_hom x y → (x ~> y);
  ls_from    : ∀ {x y}, (x ~> y) → ls_hom x y;

  (* Respectfulness is stated directly rather than through [Proper]: the
 relation spans both hom types, so [Proper] 实例 lands at
 max(h,uh) cannot be field constrained [Type@{uh}].（已译） *)
  ls_to_resp : ∀ {x y} (u v : ls_hom x y),
                 @Setoid.equiv _ (ls_setoid x y) u v → ls_to u ≈ ls_to v;

  (*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  ls_from_resp : ∀ {x y} (f g : x ~> y),
                 f ≈ g → @Setoid.equiv _ (ls_setoid x y) (ls_from f) (ls_from g);

  ls_to_from : ∀ {x y} (f : x ~> y), ls_to (ls_from f) ≈ f;
  ls_from_to : ∀ {x y} (u : ls_hom x y),
                 @Setoid.equiv _ (ls_setoid x y) (ls_from (ls_to u)) u
}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition locally_small_ambient@{o h p | h <= p} (C : Category@{o h p})
  : LocallySmall@{o h p h p} C :=
  @Build_LocallySmall@{o h p h p} C
    (fun x y => (x ~> y))
    (@homset C)
    (fun _ _ f => f)
    (fun _ _ f => f)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H)
    (fun x y f => reflexivity f)
    (fun x y u => reflexivity u).

(** ** Smallness *)

(** Awodey Definition 1.11 / Riehl Definition 1.1.6: 对象 arrows
 both sets. Here BOTH constraints strict, whole
 content 定义. （已译） *)
Class Small@{o h p uo uh up | h <= p, uh <= up, uo < o, uh < h}
      (C : Category@{o h p}) := {
  small_locally     :: LocallySmall@{o h p uh up} C;

  small_ob          : Type@{uo};
  small_ob_to       : small_ob → obj[C];
  small_ob_from     : obj[C] → small_ob;
  small_ob_to_from  : ∀ x, ObjEq (small_ob_to (small_ob_from x)) x;
  small_ob_from_to  : ∀ a, ObjEq (small_ob_from (small_ob_to a)) a
}.

(* * "Every small 范畴 is locally small" (Awodey, 注 after Definition
 1.12; Riehl, likewise). Here it is projection -- which is honest
 form, since smallness was DEFINED include hom condition.（已译） *)
Definition small_locally_small@{o h p uo uh up
    | h <= p, uh <= up, uo < o, uh < h}
  (C : Category@{o h p}) (S : Small@{o h p uo uh up} C)
  : LocallySmall@{o h p uh up} C := small_locally.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record SmallType@{w u} (A : Type@{u}) : Type@{max(w+1,u)} := {
  st_carrier : Type@{w};
  st_to      : st_carrier → A;
  st_from    : A → st_carrier;
  st_to_from : ∀ a : A, ObjEq@{u} (st_to (st_from a)) a;
  st_from_to : ∀ s : st_carrier, ObjEq@{w} (st_from (st_to s)) s
}.

Arguments st_carrier {A} _.
Arguments st_to {A} _ _.
Arguments st_from {A} _ _.
Arguments st_to_from {A} _ _.
Arguments st_from_to {A} _ _.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Definition True_setoid@{u p} (A : Type@{u}) : Setoid@{u p} A :=
  {| Setoid.equiv    := fun _ _ => True
   ; setoid_equiv    :=
       {| Equivalence_Reflexive  := fun _ => I
        ; Equivalence_Symmetric  := fun _ _ _ => I
        ; Equivalence_Transitive := fun _ _ _ _ _ => I |} |}.

(*
   本节说明hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition One_Small : Small _1 :=
  @Build_Small _1
    (@Build_LocallySmall _1
       (fun _ _ => poly_unit)
       (fun _ _ => True_setoid poly_unit)
       (fun _ _ _ => ttt)
       (fun _ _ _ => ttt)
       (fun _ _ _ _ _ => eq_refl)
       (fun _ _ _ _ _ => I)
       (fun _ _ f => match f with ttt => eq_refl end)
       (fun _ _ _ => I))
    poly_unit
    (fun _ => ttt)
    (fun _ => ttt)
    (fun x => match x with ttt => obj_refl ttt end)
    (fun a => match a with ttt => obj_refl ttt end).

(* 相关说明。 （已译） *)

(*
   本节说明 Size 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The unindexed packaging, as Riehl states it. *)
Record ArrowQuiver@{u} := {
  aq_ob      : Type@{u};
  aq_mor     : Type@{u};
  aq_dom     : aq_mor → aq_ob;
  aq_cod     : aq_mor → aq_ob;
  aq_id      : aq_ob → aq_mor;
  aq_dom_id  : ∀ x, ObjEq (aq_dom (aq_id x)) x;
  aq_cod_id  : ∀ x, ObjEq (aq_cod (aq_id x)) x
}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition TotalMor (C : Category) : Type :=
  { x : obj[C] & { y : obj[C] & x ~{C}~> y }}.

(*
   本节说明 Size 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ArrowQuiverOfCat (C : Category) : ArrowQuiver :=
  {| aq_ob     := obj[C]
   ; aq_mor    := TotalMor C
   ; aq_dom    := fun m => projT1 m
   ; aq_cod    := fun m => projT1 (projT2 m)
   ; aq_id     := fun x => existT _ x (existT _ x (@id C x))
   ; aq_dom_id := fun x => obj_refl x
   ; aq_cod_id := fun x => obj_refl x |}.

(** 本节：The two retraction laws, stated separately so file records this
 presentation they DEFINITIONAL rather than assumed -- point of
 giving both packagings. （已译） *)
Lemma arrow_quiver_dom_id (C : Category) (x : obj[C]) :
  ObjEq (aq_dom (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x.
Proof. exact (obj_refl x). Qed.

Lemma arrow_quiver_cod_id (C : Category) (x : obj[C]) :
  ObjEq (aq_cod (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x.
Proof. exact (obj_refl x). Qed.
