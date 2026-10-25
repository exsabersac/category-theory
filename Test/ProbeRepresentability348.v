(**
* Probe: boundaries of the pointwise-representability criterion

    Guards the strength claims of Adjunction/Representability.v and of
    the packaging equivalence added to Theory/Universal/Arrow.v, from
    OUTSIDE both files -- an in-file [Fail] renames in lockstep with the
    constant it guards and so cannot detect a rename.

    Two negatives, both CONVERSION, each with its cause exhibited by an
    adjacent control rather than described:

      1. [neg_ua_round] -- the packaging round trip does not return the
         [UniversalArrow] record.  Controls [ctl_obj]/[ctl_arrow] show
         BOTH derived projections do return on the nose, so what fails
         is exactly the rebuilt [arrow_initial] field.

      2. [neg_roundtrip_arrow] -- recovering the unit from a family of
         representations does not return it on the nose.  Control
         [ctl_residue] exhibits the offending term literally: the value
         is [fmap[G] id ∘ unit], so the obstruction is that residue and
         nothing else.

    The import list mirrors Adjunction/Representability.v's in full; a
    short prefix is what makes a probe pass vacuously, and a vacuity
    check cannot detect it.

--------
* 探讨：逐点可表示性标准的界限

从文件外部保护 Adjunction/Representability.v 的强度声明，以及添加到 Theory/Universal/Arrow.v 的打包等价 -- 文件内的 [Fail] 重命名会与它所保护的常量同步重命名，因此无法检测到重命名。

两个否定，都属于转换，每个否定的原因由相邻控制展示，而不是描述：

1. [neg_ua_round] —— 包装往返没有返回 [UniversalArrow] 记录。 控制 [ctl_obj]/[ctl_arrow] 显示两个派生投影都准确返回，因此失败的正是重建的 [arrow_initial] 字段。

2. [neg_roundtrip_arrow] —— 从一系列表示中恢复单元并不会精确返回它。控制 [ctl_residue] 字面上显示了有问题的项：该值是 [fmap[G] id ∘ unit]，所以障碍就是这个余数，别无其他。

导入列表完全反映了 Adjunction/Representability.v 的内容；一个简短的前缀可以使探针空洞地通过，而空洞性检查无法检测到它。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Functor.Representable.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Theory.Universal.Element.
Require Import Category.Adjunction.Representability.

Generalizable All Variables.

Section ProbePackaging.

Context {C : Category}.
Context {D : Category}.
Context {c : C}.
Context {F : D ⟶ C}.

(* INSTRUMENT CHECK: scope-free, and it must fail. / 仪器检查：范围自由，并且它必须失败。 *)
Fail Definition instrument_check : True = False := eq_refl.

(* CONTROL: both derived projections DO return on the nose. / 控制：两个派生投影都确确实实返回。 *)
Example ctl_obj (W : UniversalArrow c F) :
  @arrow_obj C D c F (ua_of_aua (aua_of_ua W)) = @arrow_obj C D c F W
  := eq_refl.

Example ctl_arrow (W : UniversalArrow c F) :
  @arrow C D c F (ua_of_aua (aua_of_ua W)) = @arrow C D c F W := eq_refl.

(* CONTROL: the other round trip returns the arrow on the nose. / 控制：另一次往返将箭头返回到鼻子上。 *)
Example ctl_aua_arrow {a : D} (W : AUniversalArrow c F a) :
  @universal_arrow C D c F a (aua_of_ua (ua_of_aua W))
    = @universal_arrow C D c F a W := eq_refl.

(*
NEGATIVE 1 (CONVERSION).  [ua_of_aua] rebuilds the comma category's
   [Initial] record from the UMP, so [arrow_initial] is a different term
   even though both projections above reduce.

--------
消极 1（转换）。[ua_of_aua] 从 UMP 重建逗号类别的 [Initial] 记录，因此 [arrow_initial] 是一个不同的术语，即使上述两个投射都会简化。
*)
Fail Definition neg_ua_round (W : UniversalArrow c F) :
  ua_of_aua (aua_of_ua W) = W := eq_refl.

End ProbePackaging.

Section ProbeResidue.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ C}.
Context (A : F ⊣ G).

(*
CONTROL: the residue is EXACTLY [fmap[G] id ∘ unit] -- exhibited, so
   the negative below is attributable to that term and to nothing else.

--------
控制：残差正好是 [fmap[G] id ∘ unit] -- 已展示，因此下面的负值归因于该项，别无其他。
*)
Example ctl_residue (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    = fmap[G] (id{D}) ∘ @unit D C F G A c := eq_refl.

(*
CONTROL: and it IS the unit up to [≈], so the negative is about
   conversion and not about the mathematics.

--------
控制：它确实是直到 [≈] 的单元，因此否定的是关于转换而不是关于数学。
*)
Example ctl_residue_equiv (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    ≈ @unit D C F G A c := representable_roundtrip_arrow A c.

(* CONTROL: the object half of the same round trip DOES return. / 控制：同一次往返的物体一半确实返回。 *)
Example ctl_roundtrip_obj (c : C) :
  fobj[left_adjoint_of_representable G (adj_representable A)] c = F c
  := eq_refl.

(* NEGATIVE 2 (CONVERSION): the arrow half does not. / 负2（转换）：箭头的一半不起作用。 *)
Fail Definition neg_roundtrip_arrow (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    = @unit D C F G A c := eq_refl.

End ProbeResidue.

(*
Names the negatives depend on must also appear OUTSIDE a [Fail], or a
   rename would leave this file compiling and the guard vacuously green.

--------
依赖的否定项的名称也必须出现在 [Fail] 外部，否则重命名会使该文件仍然可以编译，并且防护无意义地显示为绿色。
*)
Check @ua_of_aua.
Check @aua_of_ua.
Check @universal_of_representable.
Check @adj_representable.
Check @left_adjoint_of_representable.
Check @adjunction_iff_pointwise_representable.
Check @coadjunction_iff_pointwise_representable.
