(**
* Boundary probe for the powerset order and its adjunctions (#382)

    This file exists for what an in-file [Fail] cannot do: survive a
    rename.  A negative written inside the module it guards is renamed in
    lockstep with the constant it names, and so stays green when that
    constant disappears; a negative written HERE breaks loudly.

    The [Require] list below is the UNION of the four target files' own
    lists, plus the four targets.  A short prefix is exactly what makes a
    probe pass for the wrong reason -- a missing coercion or notation can
    turn an intended unification mismatch into an "illegal application" --
    so the list is mirrored rather than trimmed.

    ** THE NEGATIVES, BY KIND

    Eight negatives plus one instrument check.  The kinds are told apart
    by the error TEXT, not by a label, and the labels below were CHANGED
    after reading those texts -- negatives 2 and 3 were drafted as
    "typing" and are not:

      FORMABILITY  ends in "universe inconsistency: Cannot enforce ...".
                   Negatives 2, 3, 4 and 5.  Within them the reported
                   bound separates two shapes: 2 and 3 are SORT
                   rejections, "has type Type while it is expected to
                   have type Prop (... Cannot enforce ... <= Prop)",
                   while 4 and 5 are LEVEL rejections between two
                   declared universes ("Cannot enforce X <= o because
                   o < X", "Cannot enforce Set = u").  The tail alone
                   does NOT separate the two shapes.
      CONVERSION   "cannot unify" between two inhabitants of ONE type.
                   Negatives 6, 7 and 8.
      TYPING       a plain "has type ... while it is expected to have
                   type ...", with NO "cannot unify" and NO universe
                   clause.  Negative 9.

    Each was stripped ONE AT A TIME and compiled alone, with its whole
    error read.  Every constant a negative names also appears in a
    command OUTSIDE any [Fail], including the donors -- a guard that
    names a constant only inside its own [Fail] is vacuous.

--------
* 幂集序及其伴随的边界探测 (#382)

这个文件的存在是为了实现文件内的 [Fail] 无法做到的事情：在重命名时仍然存活。写在它所保护的模块中的负数会随着它所命名的常量一起被重命名，因此当该常量消失时，它仍然保持绿色；而写在这里的负数则会大声出错。

下面的 [Require] 列表是四个目标文件自身列表的并集，再加上四个目标。一个简短的前缀恰恰会使探针因为错误的原因而通过——缺少强制转换或符号标记可能会将预期的统一不匹配转变为“非法应用”——因此该列表是镜像的，而不是裁剪的。

** 负面因素，按种类

八个阴性加一个仪器检查。这些类型是通过错误文本区分的，而不是通过标签，下面的标签是在阅读这些文本后更改的——阴性2和3起初被起草为“打字”，但不是：

可形成性（FORMABILITY）以“universe inconsistency: Cannot enforce ...”结尾。否定项2、3、4和5。在它们之中，报告的约束将两种形态分开：2和3是SORT拒绝，“具有类型Type，而期望具有类型Prop（... Cannot enforce ... <= Prop）”，而4和5是在两个已声明宇宙之间的LEVEL拒绝（“Cannot enforce X <= o because o < X”，“Cannot enforce Set = u”）。仅尾部不能分开两种形态。
转换（CONVERSION）在同一类型的两个元素之间出现“cannot unify”。否定项6、7和8。
类型（TYPING）只是一个简单的“具有类型...，而期望具有类型...”，没有“cannot unify”且没有宇宙条款。否定项9。

每个都被一次剥离并单独编译，读取其全部错误。每个常量的负名称也出现在任何 [Fail] 之外的命令中，包括捐赠者——一个仅在其自身 [Fail] 内命名常量的保护是无效的。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Closed.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Instance.FinSet.Powerset.

Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.Subobject.
Require Import Category.Instance.FinSet.Subsets.
Require Import Category.Instance.Top.Image.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Negative 1: the instrument / ** 负 1：仪器 *)

(*
If [Fail] were inert -- a missing scope, a stray [Set Silent] -- this
   would pass and every other negative below would be worthless.

--------
如果 [Fail] 是惰性的——一个缺失的范围，一个流落的 [Set Silent]——这将通过，而下面的每一个其他否定都将毫无意义。
*)
Fail Check probe382_no_such_constant_anywhere.

(* ------------------------------------------------------------------------ *)
(** ** Controls for the constants the negatives name / ** 控制常数否定的名称 *)

Check @subset_le.
Check @subset_le_preorder.
Check @Subsets.
Check @Subsets_Complete.
Check @Subsets_Cartesian.
Check @subset_meet.
Check @DirectImage.
Check @InverseImage.
Check @image_preimage_adjunction.
Check @image_preimage_galois.
Check @image_MonotoneFun.
Check @preimage_MonotoneFun.
Check @direct_image_not_meet_preserving.
Check @powerset_sng0.
Check @sub_image.
Check @sub_reindex_monotone.
Check @sub_image_is_Powerset_Prop_image.
Check @sub_reindex_is_Powerset_Prop_preimage.
Check @Powerset_obj.
Check @Powerset_Prop_obj.
Check @Powerset_Prop_image.
Check @Powerset_Prop_preimage.
Check @Powerset_subobject_of_subset.
Check @Powerset_subset_of_subobject.
Check @Powerset_Prop_fin_object.
Check @powerset_const0.
Check @powerset_sng1.
Check @Functor_of_monotone.
Check @MonotoneFun.
Check @Opens.
Check @OpenSet.
Check @Opens_preimage.
Check @open_preimage.
Check @open_union.
Check @IsOpen.
Check @nat_inf_point.
Check @nat_inf_no_left_adjoint.
Check @nat_inf_preimage_adjunction.
Check @NatInf_Top.
Check @Point_Top.
Check @TopSpace.
Check @internal_subseteq.
Check @finpow_subseteq.
Check @finpow_le.
Check @FinSubsets.
Check @FinSubsetsToSubsets.
Check @FinSubsetsToSubsets_Full.
Check @FinSubsetsToSubsets_Faithful.
Check @finpow_image.
Check @finpow_dual.
Check @finpow_preimage.
Check @apples.
Check @relation.
Check SetoidObject.
Check Sets.
Check @carrier.
Check @Complete.
Check @Cartesian.
Check @Full.
Check @Faithful.
Check @sub_le.
Check @sub_reindex.
Check @HasPullbacks.
Check @fin_pair.
Check @sub2_10.
Check @sub2_11.
Check @apple0.
Check @finpow_map.
Check @finpow_subseteq_iff.
Check @image_ne_dual_at_apple0.
Check @Subsets_thin.
Check @Thin.
Check @GaloisConnection.
Check @Powerset_Prop_singleton_pred.
Check @nat_inf_right_adjoint.
Check @sub_image_is_Powerset_Prop_image.

(* ------------------------------------------------------------------------ *)
(**
** Negatives 2 and 3: FORMABILITY (sort) -- two Type-valued orders
       that are not [relation]s, hence out of reach of [Proset] and
       [GaloisConnection]

--------
** 负例 2 和 3：可成形性（类型）——两个类型值的顺序，它们不是 [relation]，因此无法接触 [Proset] 和 [GaloisConnection]
*)

(*
THE POSITIVE CONTROL FIRST.  Inclusion of Prop-valued subsets IS a
   [relation], which is exactly why Instance/Powerset.v can put a
   [Proset] on it.

--------
首先是阳性对照。包含 Prop 值子集是一个 [relation]，这正是 Instance/Powerset.v 可以在其上放置 [Proset] 的原因。
*)
Definition probe_prop_le@{o} (X : SetoidObject@{o o}) :
  relation (carrier (Powerset_Prop_obj@{o} X)) :=
  fun S T => ∀ x, S x → T x.

(*
NEGATIVE 2.  Instance/Sets/Powerset.v's PROOF-RELEVANT carrier has
   [Type@{o}]-valued members, so inclusion between two of its subsets is
   [Type]-valued and is not a [relation] at all.  This is why the order
   is put on the truncated carrier and not on this one.

--------
否定 2。Instance/Sets/Powerset.v 的 PROOF-RELEVANT 载体具有 [Type@{o}] 值的成员，因此其两个子集之间的包含关系为 [Type] 值，并且根本不是 [relation]。这就是为什么顺序被放在截断的载体上而不是这个载体上的原因。
*)
Fail Definition probe_type_le@{o so} (X : SetoidObject@{o o}) :
  relation (carrier (Powerset_obj@{o so} X)) :=
  fun S T => ∀ x, S x → T x.

(*
NEGATIVE 3.  The same wall one level up, and the reason
   [nat_inf_no_left_adjoint] quantifies over [Adjunction] rather than
   over [GaloisConnection]: the homs of [Opens X] are [Type]-valued.

--------
负 3。同一堵墙在上一级，以及原因 [nat_inf_no_left_adjoint] 量化 [Adjunction] 而不是 [GaloisConnection]：[Opens X] 的同态是 [Type] 值的。
*)
Fail Definition probe_opens_le (X : TopSpace) : relation (OpenSet X) :=
  fun U V => ∀ x : X, `1 U x → `1 V x.

(* ... and the control that the SAME expression IS the hom of [Opens X]. / ...以及 SAME 表达式 是 [Opens X] 的同源的控制。 *)
Definition probe_opens_hom (X : TopSpace) (U V : OpenSet X) : Type :=
  U ~{Opens X}~> V.

(* ------------------------------------------------------------------------ *)
(** ** Negatives 4 and 5: FORMABILITY (level) / ** 缺点 4 和 5：成型性（水平） *)

(*
NEGATIVE 4.  The GENERAL right adjoint of [Opens_preimage] is the
   interior of a predicate: the union of all opens contained in it.  That
   union is indexed by [OpenSet X], which sits one universe ABOVE the
   points, while [open_union] indexes only at the points' level.  This is
   why Instance/Top/Image.v delivers the right adjoint at its witness and
   not in general.

--------
负四。[Opens_preimage] 的一般右陪集是一个谓词的内部：包含在其中的所有开集的并集。这个并集由 [OpenSet X] 索引，[OpenSet X] 位于点的上一个宇宙，而 [open_union] 仅在点的级别进行索引。这就是为什么 Instance/Top/Image.v 在其实例中提供右陪集，而不是泛化地提供。
*)
Fail Definition probe_interior@{o} (X : TopSpace@{o}) (P : X → Type@{o}) :
  X → Type@{o} :=
  fun x => { V : OpenSet X & prod (∀ y : X, `1 V y → P y) (`1 V x) }.

(*
The control: at a SMALL index the very same union does form, so the
   rejection is about the index's universe and not about the shape.

--------
控制：在一个小索引下，相同的联合确实会形成，所以拒绝的是索引的范围，而不是形状。
*)
Definition probe_small_union@{o} (X : TopSpace@{o}) (I : Type@{o})
  (U : I → (X → Type@{o})) (HU : ∀ i, IsOpen X (U i)) :
  IsOpen X (fun x => { i : I & U i x }) := open_union X I U HU.

(*
NEGATIVE 5.  The [Set] level of the RAPL route, made visible: this
   file's [Subsets_Complete] is available at hom level [Set] and nowhere
   else, so the ascription below is refused.

   RECORDED CORRECTION TO THE ATTRIBUTION.  An earlier revision said the
   [Set] came from the DONOR: "[Subsets_Complete] goes through
   [Proset_Limit] and hence through Instance/Discrete.v's unannotated
   [DiscreteCat_Functor], which fixes the shape at
   [DiscreteCat@{u Set Set}]".  That donor was annotated in place at
   Instance/Discrete.v in the PR "algebraic carriers are sets"
   (2026-09-17) and fixes nothing now.  The refusal below SURVIVES that
   repair unchanged, because the [Set] it fires on is written into
   Instance/Powerset.v's own statement -- [Subsets_Complete] is declared
   at [@Complete (Subsets@{o Set} X)] -- which is a choice that file makes
   and has not re-measured.  [IsALimit] still identifies the shape's
   hom-and-proof universe with the ambient's; that part is unchanged.

--------
负数5。RAPL路径的[Set]级别，可见：本文件的[Subsets_Complete]仅在hom级别[Set]可用，其他地方不可用，因此拒绝以下归属。

对归因的记录更正。之前的修订稿称 [Set] 来自捐赠者：“[Subsets_Complete] 通过 [Proset_Limit]，因此通过 Instance/Discrete.v 中未注释的 [DiscreteCat_Functor]，这在 [DiscreteCat@{u Set Set}] 处固定了形状”。该捐赠者已在 PR “代数承载是集合” (2026-09-17) 中在 Instance/Discrete.v 就地注释，现在不再修复任何内容。下面的拒绝意见在该修复之后仍然存在，因为它触发的 [Set] 已写入 Instance/Powerset.v 自己的语句中——[Subsets_Complete] 在 [@Complete (Subsets@{o Set} X)] 处声明——这是该文件所做的选择，且未重新测量。[IsALimit] 仍然将形状的同态及证明宇宙与环境宇宙联系起来；这一部分保持不变。
*)
Fail Definition probe_complete_free@{o u + | Set < u +}
  (X : SetoidObject@{o o}) : @Complete (Subsets@{o u} X) :=
  Subsets_Complete.

(* The control at [Set], which is what Instance/Powerset.v states. / [Set] 的控制，这就是 Instance/Powerset.v 所说明的。 *)
Definition probe_complete_at_Set@{o +} (X : SetoidObject@{o o}) :
  @Complete (Subsets@{o Set} X) := Subsets_Complete.

(*
And the control that the CARTESIAN structure, which does NOT route
   through the discrete diagram, carries no such pin.

--------
而且笛卡尔结构的控制不通过离散图，它不带有这样的引脚。
*)
Definition probe_cartesian_free@{o u + | Set < u +}
  (X : SetoidObject@{o o}) : @Cartesian (Subsets@{o u} X) :=
  Subsets_Cartesian.

(* ------------------------------------------------------------------------ *)
(** ** Negatives 6, 7 and 8: CONVERSION / ** 否定项6、7和8：转换 *)

(*
NEGATIVE 6.  The direct image does not preserve meets, so the two
   sides are not the same term -- and they are not merely
   non-convertible, they are provably distinct, which is
   Instance/Powerset.v's [direct_image_not_meet_preserving].

--------
否定 6。直接像不保留交集，因此两边不是相同的项——它们不仅仅是不可互换的，它们是可证明不同的，这是 Instance/Powerset.v 中的 [direct_image_not_meet_preserving]。
*)
Fail Example probe_image_meet@{o so} :
  Powerset_Prop_image@{o} powerset_const0@{o so}
      (subset_meet powerset_sng0@{o} powerset_sng1@{o})
    = subset_meet
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng0@{o})
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o})
  := eq_refl.

(*
The control: the corresponding statement for the PREIMAGE, which does
   preserve meets, is not merely true but definitional -- substitution
   commutes with a universal quantifier on the nose.

--------
控制：对于保留交的前像的相应语句，不仅仅是正确的，而是定义性的——代入与全称量词严格交换。
*)
Example probe_preimage_meet@{o so +} :
  Powerset_Prop_preimage@{o} powerset_const0@{o so}
      (subset_meet powerset_sng0@{o} powerset_sng1@{o})
    = subset_meet
        (Powerset_Prop_preimage@{o} powerset_const0@{o so}
           powerset_sng0@{o})
        (Powerset_Prop_preimage@{o} powerset_const0@{o so}
           powerset_sng1@{o})
  → True.
Proof. intros _; exact I. Qed.

(*
NEGATIVE 7.  The monotone-map reading and the Galois reading of the
   direct image agree on OBJECTS but are not the same functor record:
   [Functor_of_monotone] is a [Program Definition] whose three law fields
   are its own opaque obligations, while [GaloisFunctor_l]'s are its own.
   The two [eq_refl] object Examples in Instance/Powerset.v are the
   controls that the difference touches neither data field.

--------
负 7。单调映射阅读与伽罗瓦阅读的直接像在对象上是一致的，但不是相同的函子记录：[Functor_of_monotone] 是一个 [Program Definition]，其三个律字段是它自身的不透明义务，而 [GaloisFunctor_l] 的字段是它自身的。Instance/Powerset.v 中的两个 [eq_refl] 对象示例是该差异未触及的控制数据字段。
*)
Fail Example probe_monotone_functor@{o so u}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  Functor_of_monotone (subset_le_preorder@{o} X)
    (subset_le_preorder@{o} Y) (image_MonotoneFun f)
  = DirectImage f := eq_refl.

Example probe_monotone_functor_obj@{o so u +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y)
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[Functor_of_monotone (subset_le_preorder@{o} X)
         (subset_le_preorder@{o} Y) (image_MonotoneFun f)] S
  = fobj[DirectImage f] S := eq_refl.

(*
NEGATIVE 8.  The subobject bridge holds at [≈] and not at [eq_refl]:
   the two truncated existentials are bracketed differently, one
   quantifying over image points and the other over elements of the
   domain.

--------
负数 8。子对象桥停在 [≈] 而不在 [eq_refl]：两个被截断的存在量词的括号方式不同，一个量化在图像点上，另一个量化在域的元素上。
*)
Fail Example probe_sub_image_bridge@{o so}
  (A B : SetoidObject@{o o}) (f : A ~{Sets@{o so}}~> B)
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so}
      (sub_image f (Powerset_subobject_of_subset@{o so} S))
  = Powerset_Prop_image@{o} f S := eq_refl.

(*
The control: the same comparison at [≈] is Instance/Powerset/
   Subobject.v's own lemma.

--------
控制：在 [≈] 上的相同比较是 Instance/Powerset/Subobject.v 自身的引理。
*)
Example probe_sub_image_bridge_equiv@{o so +}
  (A B : SetoidObject@{o o}) (f : A ~{Sets@{o so}}~> B)
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so}
      (sub_image f (Powerset_subobject_of_subset@{o so} S))
    ≈ Powerset_Prop_image@{o} f S
  := sub_image_is_Powerset_Prop_image f S.

(* ------------------------------------------------------------------------ *)
(** ** Positive checks that the headline artifacts exist and apply / ** 积极检查标题工件是否存在并应用 *)

Definition probe_adjunction_exists@{o so u u0 u1 +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  DirectImage f ⊣ InverseImage f := image_preimage_adjunction f.

Definition probe_no_left_adjoint_exists
  (L : Opens Point_Top ⟶ Opens NatInf_Top)
  (A : L ⊣ Opens_preimage nat_inf_point) : False :=
  nat_inf_no_left_adjoint L A.

Definition probe_right_adjoint_exists :
  Opens_preimage nat_inf_point ⊣ nat_inf_right_adjoint :=
  nat_inf_preimage_adjunction.

Definition probe_finset_full (n : nat) : Full (FinSubsetsToSubsets n) :=
  FinSubsetsToSubsets_Full n.

Definition probe_finset_faithful (n : nat) :
  Faithful (FinSubsetsToSubsets n) := FinSubsetsToSubsets_Faithful n.

Definition probe_reindex_monotone {C : Category} `{@HasPullbacks C}
  {x y : C} (f : y ~> x) (u v : SubObj x) :
  sub_le u v → sub_le (sub_reindex f u) (sub_reindex f v) :=
  sub_reindex_monotone f.

Example probe_internal_subseteq_computes :
  internal_subseteq 2 (fin_pair sub2_10 sub2_11) = fin_true := eq_refl.

Example probe_finpow_image_ne_dual :
  finpow_image apples apple0 = finpow_dual apples apple0 → False :=
  fun H => image_ne_dual_at_apple0 H.

Example probe_finpow_preimage_is_map (T : Fin.t (finpow 2)) :
  finpow_preimage apples T = finpow_map apples T := eq_refl.

Example probe_finpow_subseteq_iff (n : nat) (S T : Fin.t (finpow n)) :
  finpow_subseteq S T = true ↔ finpow_le S T := finpow_subseteq_iff n S T.

Example probe_sub_reindex_bridge@{o so +}
  (A B : SetoidObject@{o o}) (f : A ~{Sets@{o so}}~> B)
  (T : carrier (Powerset_Prop_obj@{o} B)) :
  Powerset_subset_of_subobject@{o so}
      (sub_reindex f (Powerset_subobject_of_subset@{o so} T))
    ≈ Powerset_Prop_preimage@{o} f T
  := sub_reindex_is_Powerset_Prop_preimage f T.

Example probe_subsets_thin (X : SetoidObject) : Thin (Subsets X) :=
  Subsets_thin X.

Example probe_open_preimage_obj {X Y : TopSpace} (g : Y ~{Top}~> X)
  (U : OpenSet X) : fobj[Opens_preimage g] U = open_preimage g U := eq_refl.

Example probe_galois_exists@{o so u +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  GaloisConnection (@subset_le@{o} X) (@subset_le@{o} Y) :=
  image_preimage_galois f.

Example probe_preimage_monotonefun@{o so +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  @MonotoneFun _ (@subset_le@{o} Y) _ (@subset_le@{o} X) :=
  preimage_MonotoneFun f.

Example probe_powerset_sng0_is_singleton@{o +} :
  powerset_sng0@{o}
    = Powerset_Prop_singleton_pred@{o}
        (X:=Powerset_Prop_fin_object@{o} 2) Fin.F1 := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Negative 9: TYPING -- the adjunction has a handedness / ** 负9：打字——附加具有方向性 *)

(*
Mac Lane's sentence is that the DIRECT image is LEFT adjoint to the
   inverse image.  The swapped reading is not a false equation, it is a
   different type, and the error says so with no "cannot unify" and no
   universe clause: a plain "has type ... while it is expected to have
   type ...".

--------
Mac Lane 的句子是直接像是逆像的左伴随。交换的理解并非错误的等式，它是另一种类型，并且错误指出这一点时没有“无法统一”也没有宇宙条款：只是简单地“具有类型...而预期具有类型...”.
*)
Fail Definition probe_wrong_handedness@{o so u u0 u1 +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  InverseImage f ⊣ DirectImage f := image_preimage_adjunction f.

(* The control at the correct handedness. / 控制在正确的手性上。 *)
Definition probe_right_handedness@{o so u u0 u1 +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  DirectImage f ⊣ InverseImage f := image_preimage_adjunction f.
