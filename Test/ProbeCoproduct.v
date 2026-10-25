(**
* Boundary probe: the coproduct roster of Mac Lane §III.3

    Companion to Structure/Biproduct/Cartesian.v,
    Instance/CMon/Coproduct.v, Instance/Ab/Coproduct.v,
    Instance/Mod/Coproduct.v, Instance/Top/Coproduct.v and
    Instance/Top/Wedge.v.  Those files make a number of STRICT claims —
    "by [eq_refl]", "supplied by [:=] with no tactic" — and a number of
    NEGATIVE ones: this does not return on the nose, that is not
    formable at those universes, the other is not statable at all.  The
    positives are guarded by the [Example]s in the files themselves.  This
    file guards the negatives: **if the [Fail] commands here stop failing,
    it breaks the build.**

    Both sides are pinned, in the manner of Test/ProbeQuiverConstructions.v.
    A [Fail] alone proves very little — it passes just as happily when the
    term is ill-typed for an unrelated reason, or when a name has been
    renamed out from under it.  So every negative is paired with a positive
    control that must SUCCEED and that NAMES THE SAME CONSTANTS, so that a
    rename or a refactor breaks the controls loudly rather than turning the
    [Fail]s vacuously green.  That claim was FALSE when this file was first
    written and an audit caught it: [RMod_inr], [bi_inl],
    [cartesian_biproduct] and [biproduct] were each named only inside a
    negative, and renaming any of them left the file compiling clean —
    the [Fail]s passing for "reference not found", which is the same
    failure mode this file records catching once already with
    [WedgeSum_Top].  Controls naming all four were added, and the repair
    was verified the only way that settles it: renaming [RMod_inr] or
    [bi_inl] now BREAKS the compile, where before it did not.

    The import list is the full one of the six
    target files, in their dependency order, for the same reason: a probe
    compiled against a short prefix of its target's imports can fail for
    want of a coercion rather than for the reason advertised.

    The instrument was checked before being trusted: wrapping [Fail] around
    a command that succeeds reports "The command has not failed!" and aborts
    compilation, so [Fail] here is not a no-op.  Every negative below was
    additionally STRIPPED of its [Fail] once and the resulting error read,
    to confirm the failure KIND; the kinds are recorded beside each probe
    and are of exactly two sorts, kept lexically apart:

      CONVERSION negatives ([Fail Definition … := eq_refl]), which report
      "cannot unify"; and FORMABILITY negatives ([Fail Check] /
      [Fail Definition] at a declared universe), which report a universe
      inconsistency or a typing error.

    A REAL FALSE PASS WAS CAUGHT WHILE WRITING THIS FILE and is recorded
    because the lesson is general: the wedge probe was first written
    against [WedgeSum_Top], a name that does not exist (the object is
    [WedgeSum], the space is [Wedge_Top]).  The [Fail] passed — for
    "reference not found", not for the advertised reason.  Stripping the
    [Fail] and reading the error is what caught it.

--------
* 边界探针：Mac Lane §III.3 的余积名册

结构/副产品/笛卡尔.v、实例/CMon/余积.v、实例/Ab/余积.v、实例/Mod/余积.v、实例/Top/余积.v 和实例/Top/楔.v 的配套文件。这些文件提出了许多严格的声明——“由 [eq_refl] 提供”、“由 [:=] 提供且没有策略”——以及一些否定的声明：这个不能直接返回，那在那些宇宙中无法形成，另一个根本无法声明。正面的声明由文件本身的 [Example] 保护。本文件保护否定的声明：**如果这里的 [Fail] 命令不再失败，将会破坏构建。**

双方都被固定，就像 Test/ProbeQuiverConstructions.v 中的方式一样。单独一个 [Fail] 证明的意义很小——当术语因无关原因类型错误，或者名称已被重命名时，它同样会顺利通过。因此，每一个负例都配有一个必须成功的正例控制，并且命名相同的常量，这样重命名或重构会大大破坏控制，而不是让 [Fail] 虚无地变为绿色。当这个文件最初被编写时，这个声明是错误的，并且一次审核发现了这个问题：[RMod_inr]、[bi_inl]、[cartesian_biproduct] 和 [biproduct] 每一个都只在否定语中被命名，重命名它们中的任何一个都会让文件可以顺利编译——[Fail] 被视为“未找到引用”，这与该文件已经记录的 [WedgeSum_Top] 捕获的失败模式相同。为四个控件添加了命名，并且通过唯一能解决问题的方式验证了修复：现在重新命名 [RMod_inr] 或 [bi_inl] 会导致编译失败，而之前不会。

导入列表是六个目标文件的完整列表，按其依赖顺序排列，原因相同：针对其目标导入的短前缀编译的探针可能会因缺少类型转换而失败，而不是因为所声明的原因。

该仪器在被信任之前进行了检查：将 [Fail] 包裹在一个成功的命令周围会报告“命令未失败！”并中止编译，所以这里的 [Fail] 不是空操作。下面的每个负测试还额外去掉了一次其 [Fail]，并读取生成的错误，以确认失败的类型；每个探测旁边记录了失败类型，并且只有两种类型，它们在词汇上保持区分：

CONVERSION 否定 ([Fail Definition … := eq_refl])，报告 “无法统一”；以及 FORMABILITY 否定 ([Fail Check] / [Fail Definition] 在已声明的宇宙中)，报告宇宙不一致或类型错误。

在编写此文件时捕获到一个真正的假通行证并被记录下来了，因为这个教训是通用的：楔形探针最初是针对 [WedgeSum_Top] 编写的，这是一个不存在的名称（实际对象是 [WedgeSum]，空间是 [Wedge_Top]）。[Fail] 通过了——是因为“未找到引用”，而不是广告中说明的原因。去掉 [Fail] 并读取错误信息才发现了它。
*)

Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.
Require Import Category.Structure.Biproduct.Cartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.CMon.Coproduct.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Coproduct.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.
Require Import Category.Instance.Top.Wedge.

Local Open Scope category_scope.

(** ** Positive controls, part 1: the strict claims hold / ** 阳性对照，第一部分：严格的声明成立 *)

(* The vocabulary bridge returns the biproduct's own data on the nose. / 词汇桥准确返回副产品自身的数据。 *)
Check (fun (C : Category) (Z : @ZeroObject C)
           (B : @HasBiproducts C Z) (x y : C) =>
         @biproduct_product_obj C Z B x y).
Check (fun (C : Category) (Z : @ZeroObject C)
           (B : @HasBiproducts C Z) (x y : C) =>
         @biproduct_prod_is_coprod C Z B x y).

(* At Ab, ten of the biproduct record's eleven fields are the CMon ones. / 在 Ab，副产品记录的十一格中有十格是 CMon 的。 *)
Check (fun M N : AbObject => (Ab_inl M N : M ~{Ab}~> Ab_product M N)).
Check (fun M N : AbObject => Ab_exl_inr M N).
Check (fun M N : AbObject => Ab_exr_inl M N).
Check (fun M N : AbObject => ab_zero_mor_is_cmon_zero_mor M N).

(*
At R-Mod the underlying arrow of an injection IS Ab's.  BOTH injections
   are named here: an audit found [RMod_inr] occurring ONLY inside
   NEGATIVE 8, so a rename would have made that [Fail] pass for "reference
   not found" while the header promised otherwise.

--------
在 R-Mod 中，注入的底层箭头是 Ab 的。这里列出了两个注入：审计发现 [RMod_inr] 仅出现在 NEGATIVE 8 内，因此重命名会让 [Fail] 被当作“未找到引用”，而标题却承诺了其他内容。
*)
Check (fun (R : RingObject) (M N : RModObject R) =>
         (eq_refl : rm_hom (RMod_inl M N) = Ab_inl M N)).
Check (fun (R : RingObject) (M N : RModObject R) =>
         (eq_refl : rm_hom (RMod_inr M N) = Ab_inr M N)).

(* The two topological coproducts exist and are what they say. / 这两个拓扑余积存在，并且正如它们所说的那样。 *)
Check (fun X Y : TopSpace => (Sum_Top X Y : TopSpace)).
Check (fun X Y : PointedTop => (Wedge_Top X Y : TopSpace)).
Check (fun X Y : PointedTop => (WedgeSum X Y : PointedTop)).
Check (fun X Y : PointedTop =>
         (eq_refl : wpoint X Y
                      = carrier (sum_carrier (ptop_space X)
                                             (ptop_space Y)))).

(** ** Conversion negatives / ** 转换否定 *)

Section RoundTripNegatives.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.
Context `{B : @HasBiproducts C Z}.

Let Cart : @Cartesian C := biproduct_Cartesian.

(*
Positive controls for this section: the OBJECT and both PROJECTIONS do
   come back on the nose, and both INJECTIONS come back up to [≈].

--------
本节的阳性对照：OBJECT 和两个 PROJECTIONS 确实完全返回，两个 INJECTIONS 都返回到 [≈]。
*)
Check (fun x y : C => @biproduct_roundtrip_obj C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_exl C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_exr C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_inl C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_inr C Z P B x y).

(*
And the four constants the NEGATIVES below name are named here too, so
   that a rename breaks this control rather than turning those [Fail]s
   vacuously green.  An audit found all four occurring only in negatives.

--------
下面提到的四个常量 NEGATIVES 在这里也有命名，这样重命名会破坏这个控制，而不是使那些 [Fail] 空泛地变成绿色。一次审计发现这四个常量只出现在否定中。
*)
Check (fun x y : C =>
         (bi_inl (@cartesian_biproduct C Z P Cart x y),
          bi_inr (@cartesian_biproduct C Z P Cart x y),
          bi_inl (biproduct x y),
          bi_inr (biproduct x y))).

(*
NEGATIVE 1 (conversion, "cannot unify").  Sending the derived cartesian
   structure back through Structure/Semiadditive.v's [cartesian_biproduct]
   does NOT return the original injections: the reconstruction defines them
   as the forks [id △ 0] and [0 △ id], which are the originals by product
   uniqueness and not by computation.

--------
负 1（转换，“无法统一”）。将派生的笛卡尔结构通过 Structure/Semiadditive.v 的 [cartesian_biproduct] 发送回去并不会返回原始的注入：重构将它们定义为叉 [id △ 0] 和 [0 △ id]，这些是通过积的唯一性得出的原始元，而不是通过计算得出的。
*)
Fail Definition neg_roundtrip_inl (x y : C) :
  bi_inl (@cartesian_biproduct C Z P Cart x y) = bi_inl (biproduct x y)
  := eq_refl.

(*
NEGATIVE 2 (conversion, "cannot unify").  A fortiori the whole record
   does not return: besides the injections, every law and both
   universal-property fields are rebuilt.

--------
负 2（转化，“无法统一”）。更何况整个记录都不会返回：除注入之外，每条法律以及两个通用属性字段都会被重建。
*)
Fail Definition neg_roundtrip_record (x y : C) :
  @cartesian_biproduct C Z P Cart x y = biproduct x y := eq_refl.

End RoundTripNegatives.

(*
NEGATIVE 3 (conversion, "cannot unify").  The wedge is not the disjoint
   union with a basepoint chosen: [Wedge_Top] carries the gluing relation
   in its setoid AND the respect-the-gluing clause in its topology, and
   [Sum_Top] carries neither.  The control immediately above this section
   shows the two share their POINT TYPE by [eq_refl], which is what makes
   this negative say something.

--------
负 3（转换，“无法统一”）。楔形不是与选定基点的析取并：[Wedge_Top] 在其集合等价类中携带粘合关系，并且在其拓扑中遵循尊重粘合的条款，而 [Sum_Top] 两者都不携带。本节上方的控制显示两者通过 [eq_refl] 共享它们的点类型，这就是使这个负数有意义的原因。
*)
Fail Definition neg_wedge_is_sum (X Y : PointedTop) :
  Wedge_Top X Y = Sum_Top (ptop_space X) (ptop_space Y) := eq_refl.

(** ** Formability negatives: the [Set] pin inherited from Instance/Ab.v / ** 可成形性负面：[Set] 引脚继承自 Instance/Ab.v *)

(*
Instance/Ab.v's [Ab_trivial] is declared with NO universe binders,
   at [AbObject@{Set Set Set}] — unlike Instance/CMon/Biproduct.v's
   [CMon_trivial@{o}], which is polymorphic.  That pin propagates through
   [Ab_Zero] to everything mentioning a zero morphism, hence to the
   biproduct records and to both derived structures, in Ab and (through
   [RMod_trivial], which uses [Ab_trivial]) in R-Mod.  The DONOR is
   Instance/Ab.v; nothing here repairs it, and it is not claimed
   unavoidable.

--------
Instance/Ab.v 的 [Ab_trivial] 被声明为没有宇宙绑定器，在 [AbObject@{Set Set Set}] 处 —— 与 Instance/CMon/Biproduct.v 的 [CMon_trivial@{o}] 不同，后者是多态的。这个标记通过 [Ab_Zero] 传播到所有提到零态射的地方，因此传播到直积记录和两个派生结构中，在 Ab 中，以及（通过 [RMod_trivial]，它使用 [Ab_trivial]）在 R-Mod 中。DONOR 是 Instance/Ab.v；这里没有任何内容可以修复它，也没有声称它是不可避免的。
*)

Section SetPin.

Universe ua.
Constraint Set < ua.

(* Controls: the direct-sum OBJECTS are free of the pin, on both sides. / 控制：直接求和对象在两侧都不受销钉限制。 *)
Check (fun M N : AbObject@{ua ua ua} => Ab_product M N).
Check (fun (R : RingObject@{ua ua ua}) (M N : RModObject R) =>
         RMod_product M N).

(*
NEGATIVE 4 (formability, universe inconsistency:
   "Cannot enforce Set = ua").

--------
负4（可成形性，宇宙不一致性：
   “无法强制执行 Set = ua”）。
*)
Fail Check (fun M N : AbObject@{ua ua ua} => Ab_Biproduct M N).

(*
NEGATIVE 5 (formability, universe inconsistency, same cause one layer
   up: [RMod_trivial] is built from [Ab_trivial]).

--------
负 5（可形成性，宇宙不一致，相同原因上一层：[RMod_trivial] 是由 [Ab_trivial] 构建的）。
*)
Fail Check (fun (R : RingObject@{ua ua ua}) (M N : RModObject R) =>
              RMod_Biproduct M N).

End SetPin.

(*
Controls for negatives 4 and 5 at the pinned level, so that the two
   constants are named by something that must succeed.

--------
在固定级别上控制负数4和5，以便这两个常量由必须成功的东西命名。
*)
Check (fun M N : AbObject => Ab_Biproduct M N).
Check (fun (R : RingObject) (M N : RModObject R) => RMod_Biproduct M N).

(** ** Formability negatives: hom and proof universes are identified / ** 可成形性缺点：同构和证明宇宙被识别 *)

(*
[Cartesian@{u u0}] takes a [Category@{u u0 u0}] — the hom and proof
   universes are IDENTIFIED, not merely bounded — so the bridge of
   Structure/Biproduct/Cartesian.v inherits that and cannot be stated over
   a category whose two levels have been declared apart.  The probe
   declares them SEPARATELY (with [Constraint uh < up]) rather than
   letting an unannotated definition minimize them together, which would
   read as an identification when it was only a bound.

   ATTRIBUTION: this is NOT introduced by [Cartesian], and negative 7
   shows it — the identification is already present at
   Structure/Terminal.v's [Terminal], upstream of everything here.  It is
   a shape of the [Structure/] hierarchy, inherited and not created.

--------
[Cartesian@{u u0}] 需要一个 [Category@{u u0 u0}]——同态和证明宇宙是被识别的，而不仅仅是有界的——所以 Structure/Biproduct/Cartesian.v 的桥接继承了这一点，不能在两个层次已经被声明为分开的范畴上陈述。探针是分别声明它们的（使用 [Constraint uh < up]），而不是让未标注的定义一起最小化它们，否则它会被读作一种识别，而它只是一个界。 归属：这不是由 [Cartesian] 引入的，负 7 显示了这一点——在 Structure/Terminal.v 的 [Terminal] 中，识别已经存在，早于这里的一切。它是 [Structure/] 层次结构的一种形态，是继承而非创建的。
*)

Section SeparatedLevels.

Universe uo uh up.
Constraint uh < up.

(*
Control: the category itself, and its hom-sets, are fine at these
   separated levels.

--------
控制：该类别本身及其同态集合在这些分离的层次上都是可以的。
*)
Check (fun (C : Category@{uo uh up}) (x y : obj[C]) => x ~{C}~> y).

(*
NEGATIVE 6 (formability, universe inconsistency:
   "Cannot enforce up = uh").

--------
负 6（成形性，宇宙不一致性：
   “无法强制执行 up = uh”）。
*)
Fail Check (fun C : Category@{uo uh up} => @Cartesian C).

(*
NEGATIVE 7 (formability, same, at the upstream donor — the attribution
   probe).

--------
负7（成形性，相同，在上游供体——归因探针处）。
*)
Fail Check (fun C : Category@{uo uh up} => @Terminal C).

End SeparatedLevels.

(*
Controls for negatives 6 and 7: both classes are of course formable
   when the two levels are not forced apart.

--------
对于负数6和7的控制：当然，当两个层次不被分开时，这两类都是可形成的。
*)
Check (fun C : Category => @Cartesian C).
Check (fun C : Category => @Terminal C).

(** ** Formability negative: the ∃!-package does not transfer to R-Mod / ** 可成形性为负：∃!-package 无法转移到 R-Mod *)

(*
Instance/Ab/Coproduct.v hands [CMon_bi_is_coproduct] straight over,
   because [AbHom A B] IS [CMonHom A B].  Instance/Mod/Coproduct.v cannot:
   [RModHom] is a record wrapping an [AbHom], so the ∃! ranges over a
   different type and the package has to be rebuilt — which is why that
   file's two universal properties are tactic proofs citing the CMon
   originals rather than [:=].

--------
Instance/Ab/Coproduct.v 将 [CMon_bi_is_coproduct] 直接交给， 因为 [AbHom A B] 是 [CMonHom A B]。 Instance/Mod/Coproduct.v 不能： [RModHom] 是一个封装 [AbHom] 的记录，所以 ∃! 范围涉及不同类型，并且该包必须重新构建——这就是为什么该文件的两个泛性质是引用 CMon 原始内容的策略证明，而不是 [:=]。
*)

(* Control: at Ab the transfer is a term. / 控制：在 Ab 中，转移是一个术语。 *)
Check (fun (M N P : AbObject) (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) =>
         (CMon_bi_is_coproduct M N P f g
            : ∃! h : Ab_product M N ~{Ab}~> P,
                (h ∘ Ab_inl M N ≈ f) ∧ (h ∘ Ab_inr M N ≈ g))).

(* Control naming the R-Mod side's own constants. / 控制命名 R-Mod 方自身的常量。 *)
Check (fun (R : RingObject) (M N P : RModObject R)
           (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) =>
         RMod_is_coproduct M N P f g).

(*
NEGATIVE 8 (formability, typing error: "The term f has type
   M ~{RMod R}~> P while it is expected to have type M ~{CMon}~> P").

--------
负 8（可塑性，输入错误：“该术语 f 的类型是 M ~{RMod R}~> P，而预期类型是 M ~{CMon}~> P”）。
*)
Fail Check (fun (R : RingObject) (M N P : RModObject R)
                (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) =>
              (CMon_bi_is_coproduct M N P f g
                 : ∃! h : RMod_product M N ~{RMod R}~> P,
                     (h ∘ RMod_inl M N ≈ f) ∧ (h ∘ RMod_inr M N ≈ g))).

(** ** Formability negative: a product topology does not fit / ** 可成形性为负：产品拓扑结构不匹配 *)

(*
Instance/Top/Coproduct.v's header says the COPRODUCT half of Mac Lane's
   roster is available in Top while the PRODUCT half is not, and that the
   obstruction is a universe wall rather than a gap in effort.  That is a
   claim about what can be WRITTEN, so it is compiled here rather than
   asserted.  The coproduct's openness predicate only APPLIES [IsOpen] to
   a restricted predicate and so stays at the space's own level; a product
   topology must quantify EXISTENTIALLY over opens of the two factors, and
   an open is a predicate on the carrier, so the quantifier lands one
   universe up.

--------
Instance/Top/Coproduct.v 的头文件说明 Mac Lane 的列表中的余积（COPRODUCT）部分在 Top 中是可用的，而积（PRODUCT）部分不可用，并且阻碍是一道宇宙墙而不是努力上的缺口。这是关于可以写出的内容的声明，所以它在此编译而不是断言。余积的开放谓词仅将 [IsOpen] 应用于受限谓词，因此保持在空间自身的层级；乘积拓扑必须对两个因子的开集进行存在量化，而开集是载体上的谓词，因此量化器落在一个更高的宇宙。
*)

Section ProductTopology.

Universe o.
Context (X Y : TopSpace@{o}).

Definition probe_prod_carrier : SetoidObject@{o o} := {|
  carrier := (carrier (top_carrier X) * carrier (top_carrier Y))%type;
  is_setoid := prod_setoid
|}.

(*
NEGATIVE 9 (formability, universe-level typing error: the body "has
   type Type@{o+1} while it is expected to have type Type@{o}").

--------
负 9（可形成性，宇宙级别类型错误：主体“的类型为 Type@{o+1}，而预期类型为 Type@{o}”）。
*)
Fail Definition probe_prod_open (W : probe_prod_carrier → Type@{o}) :
  Type@{o} :=
  ∀ p : probe_prod_carrier, W p →
    { U : carrier (top_carrier X) → Type@{o} &
    { V : carrier (top_carrier Y) → Type@{o} &
      (IsOpen X U ∧ IsOpen Y V ∧ U (fst p) ∧ V (snd p)
         ∧ (∀ q : probe_prod_carrier,
              U (fst q) → V (snd q) → W q))%type } }.

(*
Control: the very same body IS formable one universe up, so what the
   negative locates is the LEVEL and not the shape.

--------
控制：同一个身体可以形成一个宇宙，所以所定位的负面是层次而不是形状。
*)
Universe o2.
Constraint o < o2.

Definition probe_prod_open_up (W : probe_prod_carrier → Type@{o}) :
  Type@{o2} :=
  ∀ p : probe_prod_carrier, W p →
    { U : carrier (top_carrier X) → Type@{o} &
    { V : carrier (top_carrier Y) → Type@{o} &
      (IsOpen X U ∧ IsOpen Y V ∧ U (fst p) ∧ V (snd p)
         ∧ (∀ q : probe_prod_carrier,
              U (fst q) → V (snd q) → W q))%type } }.

(*
And a control at the coproduct's own predicate, which DOES fit — the
   contrast the header draws.

--------
以及在余积自身谓词上的一个控制，这正好适合——与标题所呈现的对比。
*)
Check (fun W : sum_carrier X Y → Type@{o} => (sum_open W : Type@{o})).

End ProductTopology.
