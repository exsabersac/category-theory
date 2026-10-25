(**
* Probe for Construction/Reflective/Colimit.v (issue #434)

    Pins the measured boundaries of the reflected colimit with negatives
    of two kinds, kept lexically apart: TYPING (N1: the reflected colimit's
    apex is an object of the SUBCATEGORY, not the ambient apex — the
    inclusion does not create the colimit, the reflector computes a new
    one; N3: the cocone-level result is not an instance of
    [PreservesColimitCocone K (Incl C S)] — the transfer is by reflection,
    and the inclusion is not shown to preserve colimits; N4: nor is the
    reflected colimit a [CreatesColimit K (Incl C S)] — Riehl §4.6 ex xi's
    counterexample is scoped out, not contradicted) and CONVERSION (N2:
    [Cocomplete (Sub C S)] and [Cocomplete C] are different types; the
    theorem is a function between them, not a coercion).  The [eq_refl]
    readbacks are positive controls: the transparent counit isomorphism
    reduces to the counit (Construction/Reflective.v's own is [Qed], which
    Test/ProbeReflectiveLimit373.v already pins), the reflected apex and
    injections compute to the formula the issue asks for, and the
    hypothesis-free witness, instantiated here at the torsion-free
    reflection of abelian groups over the shape [Ordinal 2] (two objects
    and a non-identity arrow, so the leg condition is exercised), computes
    its apex — the instantiation lives in this probe rather than in the
    target so that Construction/ does not import Instance/Ab.  Each
    refutation was stripped one at a time in a copy of the whole file; the
    import list mirrors the target's, plus Structure/Limit/Creation.v for
    N4 and the three modules of the torsion-free witness.

--------
* 探针用于 Construction/Reflective/Colimit.v（问题 #434）

以两种类型的否定固定反射余极限的测量边界，并在词汇上区分：TYPING（N1：反射余极限的顶点是子范畴的对象，而不是环境顶点——包含并不会创建余极限，反射器会计算一个新的；N3：余锥级别的结果不是 [PreservesColimitCocone K (Incl C S)] 的实例——传递通过反射进行，且未展示包含保持余极限；N4：反射余极限也不是 [CreatesColimit K (Incl C S)]——Riehl §4.6 ex xi 的反例被限定范围，而不是被否定）以及 CONVERSION（N2：[Cocomplete (Sub C S)] 和 [Cocomplete C] 是不同类型；定理是在它们之间的函数，而不是强制转换）。
[eq_refl] 的读回是阳性对照：透明的余单位同构简化为余单位（Construction/Reflective.v 自身的是 [Qed]，Test/ProbeReflectiveLimit373.v 已经固定了它），反射顶点和注入计算得到问题所要求的公式，而且无假设的见证者，这里在形状为 [Ordinal 2]（两个对象和一个非同一箭头，因此腿条件被检验）的阿贝尔群的无挠反射中实例化，计算其顶点——实例化存在于此探针中，而不是目标中，以便 Construction/ 不导入 Instance/Ab。每个反驳都是在整个文件的副本中逐一剥离的；导入列表镜像目标的列表，并加上 Structure/Limit/Creation.v 用于 N4 以及无挠见证者的三个模块。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Colimit.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.TorsionFree.
Require Import Category.Construction.Reflective.Colimit.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe434_absent_name.

Section Probe.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context {J : Category}.
Context (K : J ⟶ Sub C S).
Context (L : Colimit (Incl C S ◯ K)).

(** ** A: TYPING — the reflected colimit lives in the subcategory / ** A：类型——反映的余极限存在于子范畴中 *)

(* control: the reflected apex is the reflector at the ambient apex / 控制：反射的顶点是环境顶点处的反射器 *)
Example p434_apex (HL : Colimit (Incl C S ◯ K)) :
  colimit_apex (reflective_colimit R K HL) = reflector R (colimit_apex HL)
  := eq_refl.

(*
N1 TYPING: it is not the ambient apex — the two live in different
   categories

--------
N1 打字：它不是环境顶点——两者属于不同的类别
*)
Fail Example p434_apex_is_ambient :
  colimit_apex (reflective_colimit R K L) = colimit_apex L := eq_refl.

(** ** B: CONVERSION — cocompleteness of the two categories / ** B: 转换 — 两个范畴的余完备性 *)

(* control: the theorem is a function between the two / 控制：该定理是两者之间的一个函数 *)
Check (reflective_Cocomplete R : @Cocomplete C → @Cocomplete (Sub C S)).

(* N2 CONVERSION: the two types are not the same type / N2 转换：这两种类型不是同一种类型 *)
Fail Example p434_cocomplete_same : @Cocomplete (Sub C S) = @Cocomplete C
  := eq_refl.

(**
** C: TYPING — reflection is neither preservation nor creation by the
       inclusion

--------
** C: 打字 — 反思既不是通过包含来保存也不是创造
*)

(* control: the cocone-level statement / 控制：椰壳水平的声明 *)
Check (reflective_colimit_cocone R K
         : ∀ N : Cocone (Incl C S ◯ K),
             IsColimitCocone N
             → IsColimitCocone (reflective_lift_cocone R K N)).

(* N3 TYPING: it does not ascribe to preservation by the inclusion / N3 输入：它并不归因于通过包含来保存 *)
Fail Check (reflective_colimit_cocone R K
              : PreservesColimitCocone K (Incl C S)).

(* N4 TYPING: nor does the reflected colimit ascribe to creation / N4 输入：反射余极限也不归因于创造 *)
Fail Check (reflective_colimit R K : CreatesColimit K (Incl C S)).

(** ** D: readbacks / ** D：复读 *)

(* the transparent counit isomorphism reduces to the counit / 透明余单位同构简化为余单位 *)
Example p434_rc_to (x : Sub C S) :
  to (rc_counit_iso R x)
    = @counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x
  := eq_refl.

(* the injections are the issue's formula, on the nose / 这些注射正是问题的公式，恰到好处 *)
Example p434_inj (x : J) :
  colimit_inj (colimit_is_acolimit (reflective_colimit R K L)) x
    = fmap[reflector R] (colimit_inj (colimit_is_acolimit L) x)
        ∘ rc_unit_hom R (K x) := eq_refl.

Example p434_lift_apex (N : Cocone (Incl C S ◯ K)) :
  vertex_obj[reflective_lift_cocone R K N] = reflector R vertex_obj[N]
  := eq_refl.

Example p434_lift_inj (N : Cocone (Incl C S ◯ K)) (x : J) :
  cocone_inj (reflective_lift_cocone R K N) x
    = fmap[reflector R] (cocone_inj N x) ∘ rc_unit_hom R (K x) := eq_refl.

Check (reflective_reflector_Cocontinuous R : CocontinuousFunctor (reflector R)).
Check (reflective_subcategory_cocomplete R).

End Probe.

(** ** The witness at a concrete reflection: torsion-free abelian groups / ** 具体反思中的见证：无挠阿贝尔群 *)

Definition p434_torsionfree_colimit
  (K : Ordinal 2 ⟶ Sub Ab TorsionFree_Sub) : Colimit K :=
  reflective_terminal_shape_colimit TorsionFree_Reflective
    (Ordinal_Succ_Terminal 1) K.

(* its apex is the reflector at the terminal index, on the nose / 它的顶点是位于前端索引上的反射器，在鼻部 *)
Example p434_torsionfree_apex (K : Ordinal 2 ⟶ Sub Ab TorsionFree_Sub) :
  colimit_apex (p434_torsionfree_colimit K)
    = TorsionFree_reflector (Incl Ab TorsionFree_Sub (K (ord_top 1)))
  := eq_refl.

(** ** Guard block / ** 防守格挡 *)

Check @reflective_colimit.
Check @reflective_colimit_cocone.
Check @reflective_lift_cocone.
Check @reflective_Cocomplete.
Check @reflective_subcategory_cocomplete.
Check @reflective_reflector_Cocontinuous.
Check @reflective_terminal_shape_colimit.
Check @terminal_Colimit.
Check @Ordinal_Succ_Terminal.
Check @rc_counit_iso.
Check @rc_unit_hom.
Check @reflective_diagram_iso.
Check @colimit_apex.
Check @colimit_inj.
Check @colimit_is_acolimit.
Check @cocone_inj.
Check @Cocomplete.
Check @Colimit.
Check @Cocone.
Check @IsColimitCocone.
Check @PreservesColimitCocone.
Check @CreatesColimit.
Check @CocontinuousFunctor.
Check @Incl.
Check @Sub.
Check @reflector.
Check @reflective_adj.
Check @counit.
Check @Reflective.
Check @Subcategory.
Check @TorsionFree_Sub.
Check @TorsionFree_Reflective.
Check @TorsionFree_reflector.
Check @Ordinal.
Check @ord_top.
