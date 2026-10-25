Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Chain.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cone.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Streams.
Require Import Category.Instance.Sets.InverseLimit.

Generalizable All Variables.
Open Scope category_scope.

(** * Refutation probe for Instance/Sets/InverseLimit.v / * 针对 Instance/Sets/InverseLimit.v 的反驳探针 *)

(*
Each refutation command below was verified by stripping its [Fail] in a
   copy of the WHOLE file and compiling that copy alone, then reading the
   error in full -- a preamble-plus-command scratch drops the enclosing
   [Section]'s [Context] and its local universe declarations and then
   refuses for a reason unrelated to the claim.  The four negatives are of
   THREE kinds, told apart by the error TEXT and not by label:

     CONVERSION  ends "cannot unify", no universe clause  (1, 2)
     TYPING      a plain has-type mismatch, neither of those  (3)
     FORMABILITY ends "universe inconsistency: Cannot enforce ..."  (4)

   Every constant a negative names is also named by a passing command
   outside every [Fail], so a rename breaks the probe rather than turning
   a guard vacuously green.

--------
下面的每个反驳命令都是通过在整个文件的副本中去掉其 [Fail]，然后仅编译该副本来验证的，并完整地读取错误——一个前导加命令的草稿会去掉包围的 [Section] 的 [Context] 及其本地宇宙声明，然后出于与声明无关的原因拒绝执行。这四个负命令分为三种类型，通过错误文本而非标签区分：

  CONVERSION  以“cannot unify”结尾，没有宇宙条款  (1, 2)
  TYPING      普通类型不匹配，不属于上述两种情况  (3)
  FORMABILITY 以“universe inconsistency: Cannot enforce ...”结尾  (4)

每个负命令所指的常量也都被每个 [Fail] 外的一个成功命令引用，因此重命名会破坏探测，而不会使守卫空洞地变为绿色。
*)

(** ** Instrument: a [Fail] that fails for a scope-free reason / ** 仪器：一个因无作用域原因失败的 [Fail] *)

Fail Check probe408_no_such_constant.

(** ** Guard block: every constant the negatives name, outside every Fail / ** 守卫块：每个常量的负名称，位于每个失败之外 *)

Check @tower_obj.
Check @Sets_limit_obj.
Check @cone_apex.
Check @tower_iso.
Check @Sets_tower_limit.
Check @Sets_tower_limit_iso_cone_limit.
Check @inverse_limit.
Check @Cochain.
Check @Chain.
Check @Omega.
Check @Diagonal.
Check @cochain_inverse_limit.
Check @stream_to_tower.
Check @StreamTower.
Check @tower_compat.
Check @tower_compat_all.
Check @tower_proj.

(** ** (1) CONVERSION: the two presentations are not one object / ** (1) 转换：这两个演示不是同一个对象 *)

(*
The tower object carries compatibility at the STEPS; [Sets_limit_obj]
   carries it at every arrow.  They are isomorphic ([tower_iso]) and not
   convertible.

--------
塔对象在STEPS上具有兼容性；[Sets_limit_obj]在每个箭头上都具有兼容性。它们是同构的（[tower_iso]），不可转换。
*)
Fail Definition neg_tower_is_limit_obj (F : Omega^op ⟶ Sets) :
  tower_obj F = Sets_limit_obj F := eq_refl.

(* The control: the isomorphism the file actually delivers. / 控制：文件实际提供的同构。 *)
Check (fun F : Omega^op ⟶ Sets => tower_iso F).

(** ** (2) CONVERSION: nor is the tower object the cone set / ** (2) 转换：塔对象也不是锥体集合 *)

Fail Definition neg_tower_is_cone_apex (F : Omega^op ⟶ Sets) :
  tower_obj F = cone_apex F := eq_refl.

Check (fun F : Omega^op ⟶ Sets => Sets_tower_limit_iso_cone_limit F).

(** ** (3) TYPING: the shape is [Omega^op], and a covariant diagram is not one / ** (3) 类型：形状是 [Omega^op]，协变图不是一个 *)

(* A plain has-type mismatch: no [cannot unify], no universe clause. / 平原存在类型不匹配：没有 [cannot unify]，也没有 universe 条款。 *)
Fail Definition neg_wrong_variance (X : obj[Sets]) : obj[Sets] :=
  inverse_limit (Diagonal Omega X).

(*
The control: the OPPOSITE shape is what [inverse_limit] consumes, and
   it is exactly the constant tower of the library file's section (G).

--------
控制：相反的形状是 [inverse_limit] 消耗的，它正好是库文件部分（G）的常量塔。
*)
Check (fun X : obj[Sets] => inverse_limit (Diagonal (Omega^op) X)).

(** ** (4) FORMABILITY: [Cochain]'s [Set] pin, and it is the donor's / ** (4) 成形性：[Cochain] 的 [Set] 引脚，并且它属于供体 *)

Section CochainPin.

Universes co ch.
Constraint Set < ch.

(*
[Cochain@{u u0}] is declared over [C : Category@{u0 Set Set}] -- hom AND
   proof pinned to the literal [Set] -- so it is refused at a [Sets] whose
   hom-and-proof level is declared strictly above [Set].

--------
[Cochain@{u u0}] 在 [C : Category@{u0 Set Set}] 上被声明 -- hom 和证明固定在字面值 [Set] 上 -- 因此在其 hom-and-proof 级别被声明严格高于 [Set] 的 [Sets] 处被拒绝。
*)
Fail Definition neg_cochain_above_Set
  (G : Sets@{ch co} ⟶ Sets@{ch co}) : Omega^op ⟶ Sets@{ch co} := Cochain G.

(*
Controls accepted at those very levels: the category itself, a functor
   both ways, [Omega], and -- the discriminating one -- [Chain], declared
   one line above [Cochain] in the same file and FREE of any [Set].

--------
在那些级别上接受的控制：类别本身、双向函子 [Omega]，以及——区分性的——[Chain]，在同一文件中在 [Cochain] 上方一行声明，并且不受任何 [Set] 的限制。
*)
Check Sets@{ch co}.
Check (Sets@{ch co} ⟶ Sets@{ch co}).
Check Omega@{ch co co}.
Check (fun (T : @Terminal (Opposite Sets@{ch co}))
           (G : Sets@{ch co} ⟶ Sets@{ch co}) => @Chain Sets@{ch co} T G).

End CochainPin.
