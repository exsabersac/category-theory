(**
* Probe for Structure/Equalizer/Coreflexive.v (issue #421)

    Pins the measured boundaries of coreflexive pairs and Manes' criterion:
    the notion is the op-dual of a reflexive pair field for field but not
    as a type, the class is neither the dual class nor [HasEqualizers] by
    conversion, the identity index that makes Mac Lane's pair coreflexive
    exists only at the FULL arrow family of Structure/Limit/FromProducts.v,
    and the Sets converse of Exercise 1(b) needs a properness hypothesis.
    Every refutation command below was stripped ONE AT A TIME in a copy of
    the whole file and compiled alone with its error read, so each refusal
    is of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   [CoreflexivePair f g = @ReflexivePair (C^op) y x f g]
                     is refused at [eq_refl] ("cannot unify"); the fields
                     convert ([p421_field_converts]) and the pair
                     round-trips both ways at [eq_refl] (controls).
     N2 CONVERSION   [HasCoreflexiveEqualizers C = HasReflexiveCoequalizers
                     (C^op)] is refused at [eq_refl]: the existential
                     bodies are [IsEqualizer] and [IsCoequalizer]; both
                     class directions are derivable (controls).
     N3 CONVERSION   [HasCoreflexiveEqualizers C = HasEqualizers C] is
                     refused at [eq_refl]; the inclusion from
                     [HasEqualizers] is an instance (control).
     N4 TYPING       at an abstract generating family, the projection at a
                     chosen index has codomain [F (idx_cod (idx_id x))],
                     not [F x]; it lands at its declared codomain
                     (control), and at the FULL index the tie to [x] is
                     definitional (control, and [p421_id_index] at
                     [eq_refl]).  TRAP, pinned positively: with [idx_cod]
                     left implicit the same ascription is ACCEPTED —
                     [p421_trap_gen_proj_at_x] names a DIFFERENT product,
                     the unifier having solved [?idx_cod (idx_id x) ≡ x]
                     with a constant family.
     N5 TYPING       the choice function carried by [diagonal_in_image]
                     is not a Sets morphism by itself: the record literal
                     is refused with "Cannot infer field proper_morphism";
                     [diagonal_section] with the properness hypothesis is
                     the control, and the IMAGE-level biconditional
                     [diagonal_in_image_iff_through_image] — proper in
                     both directions with no hypothesis, because the image
                     setoid compares codomain components only — is the
                     second control.

    Readbacks: [mc_limit_apex] and [mc_limit_leg] (Theorem 2's explicit
    limit read back through Manes' equalizer), the three identity-index
    [eq_refl]s, and the non-vacuity witness [Sets_Complete_via_Manes].

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the five names the refuted
    declarations would introduce, and the instrument's absent name — so a
    renamed or removed constant breaks the build on a positive line rather
    than letting a refutation pass for the wrong reason.

--------
* 探测结构/均衡器/核心反身.v（问题 #421）

固定核心自反对的测量边界和马内斯标准：
    该概念是场的自反对偶对的op-对偶，但不是作为类型，
    该类既不是对偶类，也不是通过转换得到的[HasEqualizers]，
    使得Mac Lane的对成为核心自反的恒等索引只存在于Structure/Limit/FromProducts.v的FULL箭头族中，
    并且Exercise 1(b)的集合逆命题需要一个适当性假设。
    下方的每个反驳命令都是在整个文件的副本中一次剥离一个，并单独编译以读取其错误，因此每个拒绝类型都与其标签所述类型一致。

编号：
     仪器      缺失的名称，被拒绝 — 反驳关键字在此文件中有效。N1 转换   [CoreflexivePair f g = @ReflexivePair (C^op) y x f g]
     在 [eq_refl] 被拒绝（"无法统一"）；字段
     转换 ([p421_field_converts]) 和该对
     在 [eq_refl] 双向往返（控制）。N2 转换   [HasCoreflexiveEqualizers C = HasReflexiveCoequalizers
     (C^op)] 在 [eq_refl] 被拒绝：存在体为 [IsEqualizer] 和 [IsCoequalizer]；两者
     类方向可推导（控制）。N3 转换   [HasCoreflexiveEqualizers C = HasEqualizers C]
     在 [eq_refl] 被拒绝；来自 [HasEqualizers] 的包含是一个实例（控制）。
N4 打字 在一个抽象生成族上，选定索引的投影的上域是 [F (idx_cod (idx_id x))]，而不是 [F x]；它落在声明的上域上（控制），在完整索引上，绑定到 [x] 是定义性的（控制，并且在 [eq_refl] 上为 [p421_id_index]）。陷阱，正向固定：当 [idx_cod] 保持隐式时，相同的赋值被接受——[p421_trap_gen_proj_at_x] 命名的是不同的乘积，统一器已经用一个常量族解决了 [?idx_cod (idx_id x) ≡ x]。
N5 打字       [diagonal_in_image] 所携带的选择函数本身不是集合态射：记录文字被拒绝，并提示“无法推断字段 proper_morphism”；在有适当性假设的情况下，[diagonal_section] 是控制，而 IMAGE 级双条件 [diagonal_in_image_iff_through_image] — 在没有假设的情况下在两个方向上都是适当的，因为像集合态只比较陪域分量 — 是第二个控制。

回传：[mc_limit_apex] 和 [mc_limit_leg]（定理 2 的显式极限通过 Manes 的均衡器回传），三个身份索引 [eq_refl]，以及非空性证明 [Sets_Complete_via_Manes]。

守卫覆盖：每个常量被反驳的名称也会在反驳命令之外被命名（末尾的守卫块）——例外情况是在去掉注释后的普通标识符标记下，例外为关键字本身、被反驳声明将引入的五个名称以及仪器缺失的名称——因此，被重命名或移除的常量会在正向行上导致构建失败，而不是因为错误的原因让反驳通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Structure.Equalizer.Coreflexive.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe421_absent_name.

(** ** A: the notion is the op-dual in its fields, not as a type / ** A: the notion is the op-dual in its fields, not as a type / ** A：这个概念在其领域中是op-对偶的，而不是作为一种类型 *)

Section OpDual.

Context {C : Category} {x y : C} (f g : x ~> y).

(*
control: a common left inverse in C IS a common section in C^op, field
   for field

--------
控制：在 C 中的常见左逆在 C^op 中是一个常见截面，域 对 域
*)
Example p421_field_converts (s : y ~> x) (H : s ∘ f ≈ id) :
  f ∘[C^op] s ≈ id := H.

(* controls: the pair repackages both ways and round-trips at [eq_refl] / 控件：该对在 [eq_refl] 上双向重新打包并进行往返传输 *)
Check (@corefl_op_round C x y f g).
Check (@op_corefl_round C x y f g).

(* N1 CONVERSION: the record types are distinct / N1 转换：记录类型是不同的 *)
Fail Example p421_pair_is_op :
  CoreflexivePair f g = @ReflexivePair (C^op) y x f g := eq_refl.

(*
N2 CONVERSION: so are the classes — the existential bodies are
   [IsEqualizer] and [IsCoequalizer]

--------
N2 转换：课程也是如此——存在的主体是 [IsEqualizer] 和 [IsCoequalizer]
*)
Fail Example p421_class_is_op :
  HasCoreflexiveEqualizers C = HasReflexiveCoequalizers (C^op) := eq_refl.

(* controls: both class directions are derivable / 控制：两个类方向都是可导的 *)
Check (@HasCoreflexiveEqualizers_of_op C).
Check (@op_HasReflexiveCoequalizers_of_Coreflexive C).

(* N3 CONVERSION: coreflexive equalizers are not all equalizers / N3 CONVERSION: coreflexive equalizers are not all equalizers / N3 转换：核心反身等化器并非所有等化器都是相等的 *)
Fail Example p421_class_is_HasEqualizers :
  HasCoreflexiveEqualizers C = HasEqualizers C := eq_refl.

(* control: the inclusion the other way is an instance / 控制：以相反方式包含是一个例子 *)
Check (fun H : @HasEqualizers C => @HasEqualizers_HasCoreflexiveEqualizers C H).

End OpDual.

(** ** B: the identity index lives in the FULL arrow family only / ** B：恒等指数仅存在于完整箭头家族中 *)

Section GenFamily.

Context {C : Category} (HP : HasIndexedProducts C).
Context {J : Category} (F : J ⟶ C).
Context {I : Type} {idx_dom idx_cod : I → J}
  {idx_arr : ∀ i : I, idx_dom i ~{J}~> idx_cod i}
  (Hgen : Generates idx_arr).
Context (idx_id : J → I).

(*
N4 TYPING: at an abstract generating family, the projection at a
   chosen index does not land in [F x] — its codomain is
   [idx_cod (idx_id x)], with no definitional tie to [x]

--------
N4 打字：在一个抽象生成族上，选定索引的投影不落在 [F x] —— 它的值域是 [idx_cod (idx_id x)]，与 [x] 没有定义上的联系
*)
Fail Definition p421_gen_proj_at_x (x : J) :
  @pe_gen_product C HP J F I idx_cod ~> F x :=
  @pe_gen_proj C HP J F I idx_cod (idx_id x).

(* control: at the declared codomain it lands / 控制：到达声明的值域 *)
Definition p421_gen_proj_at_cod (x : J) :
  @pe_gen_product C HP J F I idx_cod ~> F (idx_cod (idx_id x)) :=
  @pe_gen_proj C HP J F I idx_cod (idx_id x).

(*
TRAP, pinned positively: with [idx_cod] left implicit the SAME
   ascription is accepted — the unifier solves [?idx_cod (idx_id x) ≡ x]
   with a constant family, so this names a DIFFERENT product

--------
TRAP，正向固定：在 [idx_cod] 被隐式保留的情况下，接受相同的归属——统一器使用常量族解决 [?idx_cod (idx_id x) ≡ x]，因此这命名了一个不同的产品
*)
Definition p421_trap_gen_proj_at_x (x : J) :
  pe_gen_product HP F ~> F x := pe_gen_proj HP F (idx_id x).

(* control: at the full index the tie is definitional / 控制：在完整索引下，关系是定义性的 *)
Definition p421_full_proj_at_x (x : J) :
  pe_arrow_product HP F ~> F x :=
  pe_arrow_proj HP F (mk_arrow (@id J x)).

Check (@id_index_cod J).

(* readback: the identity index's codomain is [x] on the nose / 回读：身份索引的值域正是 [x] *)
Example p421_id_index (x : J) : aix_cod (mk_arrow (@id J x)) = x := eq_refl.

End GenFamily.

(** ** C: the Sets converse needs properness / ** C：集合的对话需要适当性 *)

Section SetsConverse.

Context {X Y : SetoidObject} (f g : X ~{Sets}~> Y).

(*
N5 TYPING: the choice function carried by [diagonal_in_image] is not by
   itself a Sets morphism — the [proper_morphism] field is missing

--------
N5 打字：由 [diagonal_in_image] 执行的选择函数本身不是一个集合态射——缺少 [proper_morphism] 字段
*)
Fail Definition p421_bare_section (D : diagonal_in_image f g) : Y ~{Sets}~> X :=
  {| morphism := fun b => `1 (D b) |}.

(* control: with the properness hypothesis it is / 控制：在适当性假设下是这样的 *)
Check (fun (D : diagonal_in_image f g)
           (Hp : ∀ b b' : Y, b ≈ b' → `1 (D b) ≈ `1 (D b')) =>
         diagonal_section f g D Hp).

(*
control: the IMAGE-level reading needs no such hypothesis in either
   direction — the image setoid compares codomain components only, so the
   bare choice function is proper there

--------
控制：在任一方向上，图像级别的读取都不需要这样的假设——图像等价集合只比较陪域组件，因此那里裸选函数是适当的
*)
Check (fun D : diagonal_in_image f g =>
         fst (diagonal_in_image_iff_through_image f g) D).
Check (fun (d : Y ~{Sets}~> Sets_Image (f △ g))
           (Hd : Sets_Image_mono (f △ g) ∘ d ≈ id △ id) =>
         snd (diagonal_in_image_iff_through_image f g) (d; Hd)).

End SetsConverse.

(** ** D: readbacks and non-vacuity / ** D：复述和非空性 *)

Check (@mc_limit_apex).
Check (@mc_limit_leg).
Check (@id_index_dom).
Check (@id_index_arr).
Check (@Sets_Complete_via_Manes).
Check (fun (C : Category) (HP : HasIndexedProducts C) (HE : HasCoreflexiveEqualizers C) =>
         Complete_from_coreflexive_equalizers HP HE).

(** ** Guard block / ** 防守格挡 *)

Check @CoreflexivePair.
Check @corefl_retract.
Check @corefl_retract_f.
Check @corefl_retract_g.
Check @HasCoreflexiveEqualizers.
Check @coreflexive_eq.
Check @common_retraction_coreflexive.
Check @HasEqualizers_HasCoreflexiveEqualizers.
Check @functor_preserves_coreflexive.
Check @CoreflexivePair_of_op.
Check @op_ReflexivePair_of_Coreflexive.
Check @corefl_op_round.
Check @op_corefl_round.
Check @HasCoreflexiveEqualizers_of_op.
Check @op_HasReflexiveCoequalizers_of_Coreflexive.
Check @pe_retract.
Check @pe_retract_proj.
Check @pe_retract_s.
Check @pe_retract_t.
Check @pe_coreflexive.
Check @mc_equalizer.
Check @mc_apex.
Check @mc_incl.
Check @mc_IsEqualizer.
Check @mc_cone.
Check @mc_limiting.
Check @mc_limit.
Check @Complete_from_coreflexive_equalizers.
Check @fork_diagonal_of_reflexive.
Check @reflexive_of_fork_diagonal.
Check @ReflexivePair_of_diagonal_factors.
Check @diagonal_factors_of_ReflexivePair.
Check @ReflexivePair_iff_diagonal_factors.
Check @diagonal_in_image.
Check @diagonal_in_image_of_reflexive.
Check @diagonal_section.
Check @reflexive_of_diagonal_in_image.
Check @diagonal_through_image.
Check @diagonal_in_image_of_through_image.
Check @through_image_of_diagonal_in_image.
Check @diagonal_in_image_iff_through_image.
Check @Sets_HasCoreflexiveEqualizers.
Check @ReflexivePair.
Check @HasReflexiveCoequalizers.
Check @HasEqualizers.
Check @pe_gen_product.
Check @pe_gen_proj.
Check @pe_arrow_product.
Check @pe_arrow_proj.
Check @mk_arrow.
Check @Generates.
Check @id.
Check @morphism.
