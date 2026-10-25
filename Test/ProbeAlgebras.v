(*
Probe file for the monoid ring, the tensor algebra and the exterior
   algebra: Instance/Rng/MonoidRing.v, Instance/Rng/GroupRing.v,
   Instance/Rng/Algebras/Associative.v and Instance/Vect/TensorAlgebra.v.

   Convention: Test/ProbeFunnyPoly.v, Test/ProbeSquare.v,
   Test/ProbeFreeGroupoid.v, Test/ProbePolynomial.v.  Each NEGATIVE is a
   [Fail] guarding a strength claim made in one of those files, and each
   is paired with a POSITIVE CONTROL that must succeed, so that a rename
   or a definitional change breaks this file loudly instead of turning the
   [Fail]s vacuously green.

   PROBE HYGIENE.  The import list below is the union of the four target
   files' imports, in their order, because a short prefix is exactly what
   makes a probe pass for the wrong reason: a missing coercion turns a
   [Fail] green with an "Illegal application" that has nothing to do with
   the claim being guarded (the episode recorded in
   Test/ProbeFieldFrac.v).  Each negative below was stripped of its [Fail]
   during development and the resulting error inspected: negatives 1 and 2
   are genuine universe inconsistencies naming the declared level
   ("Cannot enforce Set = big"), and negatives 3 to 6 are genuine
   conversion failures.

--------
单子环、张量代数和外代数的探针文件：Instance/Rng/MonoidRing.v, Instance/Rng/GroupRing.v, Instance/Rng/Algebras/Associative.v 和 Instance/Vect/TensorAlgebra.v。

约定：Test/ProbeFunnyPoly.v、Test/ProbeSquare.v、Test/ProbeFreeGroupoid.v、Test/ProbePolynomial.v。每个 NEGATIVE 都是一个 [Fail]，用于保护这些文件中提出的一个强度声明，并且每个都配对一个必须成功的 POSITIVE CONTROL，这样重命名或定义更改会明显地破坏此文件，而不是使 [Fail] 空泛地变为绿色。

探针卫生。下面的导入列表是四个目标文件导入的并集，按它们的顺序排列，因为短前缀正是使探针由于错误原因通过的原因：缺少强制转换会使 [Fail] 出现“非法应用”而变为绿色，这与被保护的声明无关（记录在 Test/ProbeFieldFrac.v 中的事件）。在开发过程中，每个负样本都被剥离了 [Fail]，并对得到的错误进行了检查：负样本 1 和 2 是命名已声明级别的真实宇宙不一致性（“无法强制 Set = big”），而负样本 3 到 6 是真实的转换失败。
*)

Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Elements.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.GL.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.GroupRing.
Require Import Category.Instance.Vect.TensorAlgebra.

Monomorphic Universe big.
Monomorphic Constraint Set < big.

(**
* 1-2: the [Set] pin on the multiplicative-monoid forgetful functor

    Instance/Rng/MonoidRing.v's header states that [Rig_Forget_Mon] —
    hence the [Rng_Forget_Mon] built from it — is instantiable only at
    rigs whose carrier and [≈] live in [Set], and that the restriction is
    the DONOR'S rather than one introduced there.  Both halves are pinned
    here.  The instrument is sanity-checked first: the large instance of
    the integers is itself well formed, so the rejections below are about
    the functor and not about the ring.

--------
* 1-2：乘法幺半群遗忘函子上的 [Set] 引脚

Instance/Rng/MonoidRing.v 的标题声明 [Rig_Forget_Mon] ——因此由此构建的 [Rng_Forget_Mon] ——只在载体和 [≈] 位于 [Set] 的环上可实例化，并且该限制是捐赠者的，而不是在那里引入的。这里固定了两部分。仪器首先进行了理智检查：整数的大实例本身是良构的，因此下面的拒绝是关于函子，而不是关于环。
*)

(* instrument check *)
Check (Int_Rig@{big big big} : RigObject@{big big big}).
Check (Int_Ring@{big big big} : RingObject@{big big big}).

(* positive control: the donor applies at the Set-level instance / 阳性对照：供体在集合级实例上应用 *)
Check (Rig_Forget_Mon (Int_Rig@{Set Set Set})).
Check (Rng_Forget_Mon (Int_Ring@{Set Set Set})).

(* NEGATIVE 1: the donor itself does not reach one universe up / 消极1：捐赠者本身无法到达一个宇宙之上 *)
Fail Check (Rig_Forget_Mon (Int_Rig@{big big big})).

(* NEGATIVE 2: and neither does the ring-level functor built from it / 负 2：由它构建的环级函子也不行 *)
Fail Check (Rng_Forget_Mon (Int_Ring@{big big big})).

(**
* 3-4: preservation of zero and one by the monoid ring's extension is
      NOT definitional

    Instance/Rng/MonoidRing.v records that the extension's action on
    SCALARS and on GENERATORS holds by [eq_refl] while its preservation of
    ZERO and of ONE holds only up to [≈].  The reason is that the zero and
    the one of R[M] are scalars, so the fold returns the structure map's
    value there.  Both halves are pinned.

    The statements below are at a VARIABLE ring, deliberately: at a
    concrete structure map the same equations can close by computation,
    and the claim being guarded is about the general case.

--------
* 3-4：单子环扩展对零和一的保持 **不是定义性的**

Instance/Rng/MonoidRing.v 记录了扩展在**标量**和**生成元**上的作用是通过 [eq_refl] 保证的，而对零和一的保持仅在 [≈] 的范围内成立。原因是 R[M] 的零和一是标量，因此 fold 会返回结构映射在那里的值。两个部分都是固定的。

以下陈述是在一个**变量**环下的，有意为之：在具体的结构映射下，相同的方程可以通过计算来闭合，而受保护的断言是关于一般情况的。
*)

(*
Written as top-level lambdas rather than in a [Section]: a section
   variable [S : RingObject] has its universes fixed at the [Context]
   command, and a later mention of [Rng_Forget_Mon S] in the same section
   is then rejected by the very pin that negatives 1 and 2 guard.  That
   structural consequence is exactly what Instance/Rng/MonoidRing.v's
   header records, and it is why the evaluation development in that file
   is at top level too.

--------
写成顶层 lambda 而不是在 [Section]: 一个节中变量 [S : RingObject] 在 [Context] 命令时固定了它的宇宙，而在同一节中对 [Rng_Forget_Mon S] 的后续引用会被第 1 和第 2 个保护的针直接拒绝。这个结构性的结果正是 Instance/Rng/MonoidRing.v 的头部记录的内容，这也是该文件中的评估开发也是顶层的原因。
*)

(* positive controls: scalars and generators DO close by [eq_refl] / 阳性对照：标量和生成器由 [eq_refl] 关闭 *)
Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) =>
         eq_refl : rig_map (mring_extend phi psi Hcomm) (mr_scal (rig_zero R))
                     = rig_map phi (rig_zero R)).

Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) (m : carrier (mcar M)) =>
         eq_refl : rig_map (mring_extend phi psi Hcomm) (mr_gen m)
                     = mmap psi m).

(* NEGATIVE 3: preservation of zero is not definitional / 负三：零的保留不是定义性的 *)
Fail Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
                (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
                (Hcomm : MRComm phi psi) =>
              eq_refl
                : rig_map (mring_extend phi psi Hcomm)
                    (rig_zero (MonoidRing R M)) = rig_zero S).

(* NEGATIVE 4: nor is preservation of one / 负4：也不是对某一的保存 *)
Fail Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
                (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
                (Hcomm : MRComm phi psi) =>
              eq_refl
                : rig_map (mring_extend phi psi Hcomm)
                    (rig_one (MonoidRing R M)) = rig_one S).

(* ...and both DO hold up to [≈], which is what the file claims / ...并且两者都能够支持 [≈]，这正是该文件所声称的 *)
Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) =>
         rig_map_zero (mring_extend phi psi Hcomm)).

Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) =>
         rig_map_one (mring_extend phi psi Hcomm)).

(**
* 5-6: the same seam in the tensor algebra

    Instance/Vect/TensorAlgebra.v makes the identical claim for
    [tensor_extend], for the identical reason.

--------
* 5-6：张量代数中的相同缝隙

    Instance/Vect/TensorAlgebra.v 对 [tensor_extend] 做出了相同的声明，原因完全相同。
*)

Section TensorStrictness.

Context (K : CRng) (V : RModObject (`1 K)) (A : AAlgObject K).
Context (f : AAlgLinear V A).

(* positive controls *)
Check (fun v => eq_refl
        : rig_map (`1 (tensor_extend A f)) (tt_gen v) = alin_map f v).
Check (fun a => eq_refl
        : rig_map (`1 (tensor_extend A f)) (tt_scal a)
            = rig_map (aalg_unit A) a).

(* NEGATIVE 5: preservation of zero is not definitional / 负五：零的保留不是定义性的 *)
Fail Check (eq_refl
  : rig_map (`1 (tensor_extend A f)) (rig_zero (TensorRing V))
      = rig_zero (aalg_ring A)).

(* NEGATIVE 6: nor is preservation of one / 负 6：也不是保存其中的一个 *)
Fail Check (eq_refl
  : rig_map (`1 (tensor_extend A f)) (rig_one (TensorRing V))
      = rig_one (aalg_ring A)).

(* ...and both DO hold up to [≈] / ...并且两者都能承受 [≈] *)
Check (rig_map_zero (`1 (tensor_extend A f))).
Check (rig_map_one (`1 (tensor_extend A f))).

End TensorStrictness.

(**
* Positive controls for the strict claims that DID close

    These are the claims the three files make at [eq_refl]; restated here
    so that a change breaking any of them breaks this file too.

--------
* 对严格声明的积极控制确实已关闭

    这些是三个文件在 [eq_refl] 上提出的声明；在此重新表述
    以便任何破坏其中任何一项的更改也会破坏此文件。
*)

Check (fun (K : CRng) (V : RModObject (`1 K)) (t : TTerm V) =>
         eq_refl : rig_map (`1 (ext_proj V)) t = t).

Check (fun (K : CRng) (V : RMod (`1 K)) =>
         eq_refl : fobj[TensorFunctor K] V = TensorAlg V).

Check (fun (M : MonSets) =>
         eq_refl : fobj[MonoidRingFunctor] M = ZMonRing M).

Check (fun (G : Grp) =>
         eq_refl : fobj[GroupRingFunctor] G = GrpRing G).

Check (fun (G : Grp) (g : carrier (grp_setoid G)) =>
         eq_refl : `1 (grp_map (grp_ring_insert G) g)
                     = @mr_gen Int_Ring (Grp_MonSets G) g).
