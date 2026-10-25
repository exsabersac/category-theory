(**
* Probe: boundaries of the additive-adjunction results

    Guards the strength claims of Adjunction/Additive.v from OUTSIDE
    that file — an in-file [Fail] renames in lockstep with the constant
    it guards and so cannot detect a rename.

    That file's header MEASURES three equations as rejected at
    [eq_refl] and says plainly that nothing there would notice if a
    later change made one of them definitional.  This file closes that
    gap: each of the three is pinned as a CONVERSION negative, beside a
    control establishing the same equation holds at [≈], so the
    negatives are about conversion and not about the mathematics.

    The import list mirrors the target's in full; a short prefix is what
    makes a probe pass vacuously, and a vacuity check cannot detect it.

--------
* 探针：加法-伴随结果的边界

    从该文件外部保护 Adjunction/Additive.v 的强度声明 — 文件内部的 [Fail] 与它所保护的常量同步重命名，因此无法检测重命名。

    该文件的头部在 [eq_refl] 将三个方程测量为被拒绝，并明确说明，如果后来将其中一个方程设为定义的，它也不会察觉。该文件弥补了这一空白：三个方程都被固定为 CONVERSION 负面，同时一个控制验证在 [≈] 上同样成立，因此这些负面是关于转换的，而不是关于数学的。

    导入列表完全镜像目标文件；一个简短的前缀使探针形式上通过，而空白检查无法检测到它。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.
Require Import Category.Adjunction.Additive.

Generalizable All Variables.

Section ProbeTranspose.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (AU : @AdditiveFunctor C D AC AD U).

(* INSTRUMENT CHECK: scope-free, and it must fail. / 仪器检查：范围自由，并且它必须失败。 *)
Fail Definition instrument_check : True = False := eq_refl.

(* CONTROL: transpose additivity DOES hold at [≈]. / 控制：在 [≈] 上，转置加性确实成立。 *)
Example ctl_to_adj_padd {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj (padd f g) ≈ padd (to adj f) (to adj g)
  := @to_adj_padd C D AC AD F U A AU x y f g.

(*
NEGATIVE 1 (CONVERSION): and not on the nose.  [padd] is an abstract
   field of a class, so neither side reduces.

--------
负面 1（转换）：并不直接。[padd] 是一个类的抽象字段，因此双方都不会减少。
*)
Fail Definition neg_to_adj_padd {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj (padd f g) = padd (to adj f) (to adj g) := eq_refl.

(* CONTROL: Theorem 3's own field holds at [≈]. / 控制：定理3自身的字段存在于 [≈]。 *)
Example ctl_left_adjoint_fmap_padd {x y : D} (f g : x ~{D}~> y) :
  fmap[F] (padd f g) ≈ padd (fmap[F] f) (fmap[F] g)
  := @left_adjoint_fmap_padd C D AC AD F U A AU x y f g.

(* NEGATIVE 2 (CONVERSION): and not on the nose. / 负2（转换）：不要太直白。 *)
Fail Definition neg_left_adjoint_fmap_padd {x y : D} (f g : x ~{D}~> y) :
  fmap[F] (padd f g) = padd (fmap[F] f) (fmap[F] g) := eq_refl.

End ProbeTranspose.

Section ProbeBiproduct.

Context {C : Category}.
Context `{ZC : @ZeroObject C}.
Context {P : @Preadditive C}.

(*
CONTROL: the coproduct-diagonal factorization holds at [≈].  Note it
   needs only [Preadditive], not the full [AbEnriched] — the negation
   plays no part.

--------
控制：余积-对角分解在 [≈] 处成立。请注意，它只需要 [Preadditive]，而不需要完整的 [AbEnriched] — 否定并不发挥任何作用。
*)
Example ctl_padd_copair_diag {a c : C} (B : Biproduct a a) (f g : a ~> c) :
  bi_copair B f g ∘ bi_diag B ≈ padd f g
  := @padd_copair_diag C ZC P a c B f g.

(* NEGATIVE 3 (CONVERSION): and not on the nose. / 负三（转换）：不要太直白。 *)
Fail Definition neg_padd_copair_diag {a c : C}
  (B : Biproduct a a) (f g : a ~> c) :
  bi_copair B f g ∘ bi_diag B = padd f g := eq_refl.

End ProbeBiproduct.

(**
** The universe donors, pinned

    Adjunction/Additive.v measures that [u0 = u2] — the identification
    of the two categories' hom-and-proof universes — has AT LEAST THREE
    INDEPENDENT donors.  An earlier revision of that file attributed it
    to the [Adjunction] class alone and called the attribution
    DISCRIMINATING; it is not, because the control it cited removes all
    three donors at once.  These negatives guard the corrected reading:
    the levels are declared so that D's hom sits STRICTLY BELOW C's,
    which satisfies the bound [bh <= ah] while violating the equation,
    and then each donor is rejected ON ITS OWN while the cited control
    is accepted at those very levels.

--------
** 宇宙捐赠者，固定

附加/加法.v 测量表明 [u0 = u2] —— 两个类别的同态与证明宇宙的识别 —— 至少有三 个 独立的捐赠者。该文件的早期版本将其仅归因于 [Adjunction] 类，并称这种归因为区分性的；但事实并非如此，因为它引用的控制会同时移除这三位捐赠者。这些负面结果保证了修正后的读法：各级别被声明为 D 的同态 严格低于 C 的同态，这满足了 [bh <= ah] 的界限，同时违反了等式，然后每个捐赠者都会被单独拒绝，而所引用的控制在这些级别上被接受。
*)

Section ProbeUniverseDonors.

Universes ao ah bo bh.
Constraint bh < ah.

Context (Cu : Category@{ao ah ah}).
Context (Du : Category@{bo bh bh}).
Context (ZCu : @ZeroObject Cu) (ZDu : @ZeroObject Du).
Context (PCu : @Preadditive Cu) (PDu : @Preadditive Du).
Context (ACu : AbEnriched Cu) (ADu : AbEnriched Du).
Context (Gu : Du ⟶ Cu).

(*
CONTROL: the statement the withdrawn attribution cited IS formable
   at these levels — so the negatives below fire on the donors and not
   on the level declaration itself.

--------
控制：所引用的撤回归属声明可以在这些层级上形成——因此下面的否定作用于捐赠者，而不是作用于层级声明本身。
*)
Check (@fmap_padd_of_preserved_coproduct Cu Du ZCu ZDu PCu PDu Gu).

(* CONTROL: naming a hom of each category at these levels is fine. / CONTROL: naming a hom of each category at these levels is fine. / 控制：在这些水平上为每个类别命名一个同源物是可以的。 *)
Check (fun (x y : Cu) => x ~{Cu}~> y).
Check (fun (x y : Du) => x ~{Du}~> y).

(*
NEGATIVE 4 (FORMABILITY) — donor (i).  [AdditiveFunctor] alone, with
   ONE functor in the command and no adjunction anywhere: its binder
   reuses a single level for both categories while its own constraint
   block is empty.

--------
负 4（可形成性）— 供体 (i)。仅使用 [AdditiveFunctor]，在命令中有一个函数符，且没有任何附加：它的绑定器为两个类别重复使用一个层次，同时它自己的约束块为空。
*)
Fail Check (@AdditiveFunctor Du Cu ADu ACu Gu).

(* CONTROL: the functor we HAVE, D ⟶ C, is formable at these levels. / 控制：我们有的函子 D ⟶ C，可以在这些层次上形成。 *)
Check (Du ⟶ Cu).

(*
NEGATIVE 5 (FORMABILITY) — donor (ii).  Merely wanting a functor in
   the OTHER direction, with no adjunction anywhere: [Functor] forces
   source-hom below target-hom, so having both directions forces
   equality.  Written WITHOUT an explicit universe instance on purpose:
   [Functor]'s instance arity differs between Rocq 9.1 and the 8.x
   line, so a [Functor@{...}] spelling could make this [Fail] succeed
   on an ARITY error rather than the universe inconsistency — passing
   vacuously on two of the three supported toolchains, which no vacuity
   check would detect.

--------
负面 5（可形成性）——供体 (ii)。仅仅希望在另一个方向有一个函子，而在任何地方都没有附加：[Functor] 强制源同态低于目标同态，因此同时拥有两个方向会强制相等。为了刻意不写明显的宇宙实例：[Functor] 的实例元数在 Rocq 9.1 和 8.x 系列之间有所不同，因此 [Functor@{...}] 的拼写可能会在类型元数错误上使 [Fail] 成功，而不是宇宙不一致——在三种支持的工具链中有两种会虚假的通过，而没有任何虚假检查能检测到。
*)
Fail Check (Cu ⟶ Du).

(* NEGATIVE 6 (FORMABILITY) — donor (iii).  [Adjunction] itself. / 负 6（可成型性）——供体（iii）。[Adjunction] 本身。 *)
Fail Check (@Adjunction Cu Du).

End ProbeUniverseDonors.

(*
Names the negatives depend on must also be named OUTSIDE a [Fail],
   or a rename would leave this file compiling and the guard green.

--------
依赖于的负面名称也必须在 [Fail] 外部命名，否则重命名将导致此文件编译并且保护显示为绿色。
*)
Check @to_adj_padd.
Check @left_adjoint_fmap_padd.
Check @padd_copair_diag.
Check @left_adjoint_additive.
Check @right_adjoint_additive.
Check @adj_hom_ab_iso.
Check @left_adjoint_additive_of_biproducts.
Check @hom_ab.
Check @fmap_padd_of_preserved_coproduct.
Check @AdditiveFunctor.
Check @AbEnriched_op.
Check @Preadditive_op.
