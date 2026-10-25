Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * Monic/epi duality, carried out through the opposite category / * 单态/上极对偶，通过对偶范畴实现 *)

(*
nLab: https://ncatlab.org/nlab/show/monomorphism
   nLab: https://ncatlab.org/nlab/show/epimorphism
   Book: Riehl, "Category Theory in Context", §1.2 (Lemma 1.2.11)

   Riehl's §1.2 states four facts about monos and epis -- closure under
   composition and cancellation, each in two variances -- and the point of the
   section is that only two of them need proving: the other two are their
   images under C ↦ C^op.  Theory/Morphisms.v proves all four directly, for a
   reason that is structural rather than stylistic, and this file supplies the
   dual route that file cannot.

   WHY NOT IN Theory/Morphisms.v.  Duality needs [Opposite], and
   Construction/Opposite.v requires Theory/Isomorphism.v, which requires
   Theory/Morphisms.v.  Adding the import there is therefore a cycle, and Rocq
   rejects it (the exact message depends on which .vo files are present -- a
   self-require complaint on a clean tree, an inconsistent-assumptions error
   against a stale Morphisms.vo -- but it is refused either way).
   Since the cancellation lemmas are consumed low in the tree (by
   Structure/Factorization/StrongEpi.v and Theory/Subobject.v), they have to
   live below the opposite category, and the dual derivation has to live above
   it.  Hence: direct proofs there, dual derivations here.

   WHAT DUALITY COSTS HERE.  [Monic] and [Epic] are two distinct records, not
   one notion read in two variances, so `@Epic (C^op) y x f` is not literally
   `@Monic C x y f` -- Rocq rejects the identity function between them.  What
   IS true is that their single fields have the same type on the nose, because
   `x ~{C^op}~> z` reduces to `z ~{C}~> x` and `g ∘[C^op] f` to `f ∘[C] g`.
   So each bridge below is one constructor application with no proof content,
   and the derivations that follow genuinely reuse the original argument
   rather than repeating it.

--------
nLab: https://ncatlab.org/nlab/show/monomorphism
nLab: https://ncatlab.org/nlab/show/epimorphism
书籍: Riehl，《上下文中的范畴论》，§1.2（引理 1.2.11）

Riehl 的 §1.2 陈述了关于单态（monos）和满态（epis）的四个事实——在两种变式下的复合封闭性和消除性——本节的重点是只需要证明其中两个：其他两个是它们在 C ↦ C^op 下的像。Theory/Morphisms.v 直接证明了这四个事实，原因是结构性的而非风格上的，而该文件提供了那个文件无法提供的对偶路径。

为什么不在 Theory/Morphisms.v 中。Duality 需要 [Opposite]，而 Construction/Opposite.v 需要 Theory/Isomorphism.v，而后者又需要 Theory/Morphisms.v。因此在那里添加导入会形成循环，Rocq 会拒绝它（具体信息取决于存在的 .vo 文件——在干净的目录上会有自我依赖的抱怨，对旧的 Morphisms.vo 则会报不一致假设错误——但无论哪种情况都会被拒绝）。由于消去引理在树的低处被使用（由 Structure/Factorization/StrongEpi.v 和 Theory/Subobject.v），它们必须位于对立范畴之下，而对偶推导必须位于它之上。因此：直接证明在这里，对偶推导在这里。

双重性在这里的代价。[Monic] 和 [Epic] 是两个不同的记录，而不是同一概念在两种变体中的体现，所以 `@Epic (C^op) y x f` 并不字面上等于 `@Monic C x y f` —— Rocq 拒绝它们之间的恒等函数。真正正确的是，它们的单个字段的类型完全相同，因为 `x ~{C^op}~> z` 约简为 `z ~{C}~> x`，`g ∘XPROTECT3X f` 约简为 `f ∘XPROTECT4X g`。因此，下面的每个桥都是一个没有证明内容的构造函数应用，而随后的推导则是真正重用原始论证，而不是重复它。
*)

(** ** The four bridges / ** 四座桥 *)

Definition Monic_of_op_Epic {C : Category} {x y : C} (f : x ~> y)
  (H : @Epic (C^op) y x f) : @Monic C x y f :=
  @Build_Monic C x y f (@epic (C^op) y x f H).

Definition op_Epic_of_Monic {C : Category} {x y : C} (f : x ~> y)
  (H : @Monic C x y f) : @Epic (C^op) y x f :=
  @Build_Epic (C^op) y x f (@monic C x y f H).

Definition Epic_of_op_Monic {C : Category} {x y : C} (f : x ~> y)
  (H : @Monic (C^op) y x f) : @Epic C x y f :=
  @Build_Epic C x y f (@monic (C^op) y x f H).

Definition op_Monic_of_Epic {C : Category} {x y : C} (f : x ~> y)
  (H : @Epic C x y f) : @Monic (C^op) y x f :=
  @Build_Monic (C^op) y x f (@epic C x y f H).

(** ** The dual derivations / ** 双重来源 *)

(*
[monic_cancel] obtained from [epic_cancel] with no second argument.  In
   C^op the composite f ∘ g becomes g ∘ f, so cancelling the LEFT factor there
   is cancelling the RIGHT factor here -- which is exactly why the two lemmas
   read as mirror images rather than as the same statement twice.

--------
[monic_cancel] 是从 [epic_cancel] 获得的，没有第二个参数。在 C^op 中，复合 f ∘ g 变为 g ∘ f，所以在那里的取消左因子就是在这里取消右因子——这正是为什么这两个引理读起来像镜像，而不是同一个陈述重复两次。
*)
Definition monic_cancel_op {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} : Monic (f ∘ g) → Monic g :=
  fun H => Monic_of_op_Epic g
             (@epic_cancel (C^op) z y x g f (op_Epic_of_Monic (f ∘ g) H)).

(* And [monic_compose] from [epi_compose], the same way. / 以及 [monic_compose] 从 [epi_compose]，以同样的方式。 *)
Definition monic_compose_op {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} : Monic f → Monic g → Monic (f ∘ g) :=
  fun Hf Hg =>
    Monic_of_op_Epic (f ∘ g)
      (@epi_compose (C^op) z y x g f
         (op_Epic_of_Monic g Hg) (op_Epic_of_Monic f Hf)).

(*
The derived forms prove the same statements as the direct ones.  Stating
   this is the honest way to keep both: nothing here silently replaces
   Theory/Morphisms.v's proofs, and if the two ever drifted apart these would
   stop typechecking.

--------
派生形式证明了与直接形式相同的命题。陈述这一点是保持两者的诚实方式：这里没有任何内容会悄悄替代 Theory/Morphisms.v 的证明，如果两者之间出现任何偏离，这些将会停止类型检查。
*)
Definition monic_cancel_agrees {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} :
  (Monic (f ∘ g) → Monic g) * (Monic (f ∘ g) → Monic g) :=
  (@monic_cancel C x y z f g, @monic_cancel_op C x y z f g).

Definition monic_compose_agrees {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} :
  (Monic f → Monic g → Monic (f ∘ g)) *
  (Monic f → Monic g → Monic (f ∘ g)) :=
  (@monic_compose C x y z f g, @monic_compose_op C x y z f g).

(** ** The wide subcategories of monos and of epis / ** monos 和 epis 的广泛子范畴 *)

(*
Riehl, CTiC, §1.2 (Exercise 1.2.ii): the monomorphisms of C form a wide
   subcategory -- wide because every identity is monic, a subcategory because
   monos compose.  Those are exactly [id_monic] and [monic_compose], so the
   record below has no proof content of its own; the point is that the two
   closure lemmas are precisely the subcategory axioms.

--------
Riehl, CTiC, §1.2（练习 1.2.ii）：C 的单态构成了一个广义子范畴——广义是因为每个同一射都是单射，子范畴是因为单射可复合。这些正好是 [id_monic] 和 [monic_compose]，因此下面的记录本身没有证明内容；重点是，这两个闭包引理恰好就是子范畴公理。
*)
Definition MonoSub (C : Category) : Subcategory C := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => Monic f;
  scomp := fun x y z _ _ _ f g Hf Hg => monic_compose Hf Hg;
  sid   := fun x _ => id_monic x
|}.

Definition MonoSub_Wide (C : Category) : Wide C (MonoSub C) :=
  fun _ => ttt.

(*
The dual, obtained through C^op rather than reproved: an epimorphism of C
   is a monomorphism of C^op, so [EpiSub] transports [MonoSub (C^op)] back
   along the bridges above rather than repeating the closure arguments.  Note
   the composition order flips in the opposite category, which is why the
   [scomp] field below feeds its two arguments in the other order.

--------
通过 C^op 而不是重新证明得到的对偶：C 的一个余满射在 C^op 中是单射，因此 [EpiSub] 沿着上面的桥将 [MonoSub (C^op)] 传回，而不是重复闭包论证。注意，在对立范畴中组合顺序会颠倒，这就是下面的 [scomp] 字段以相反的顺序输入其两个参数的原因。
*)
Definition EpiSub (C : Category) : Subcategory C.
Proof.
  unshelve refine {| sobj := fun _ => poly_unit
                   ; shom := fun x y _ _ f => Epic f |}.
  - (* closure under composition, from [monic_compose] read in C^op / 在 C^op 中从 [monic_compose] 读取的复合封闭性 *)
    intros x y z ox oy oz f g Hf Hg.
    exact (Epic_of_op_Monic (f ∘ g)
             (@monic_compose (C^op) z y x g f
                (op_Monic_of_Epic g Hg) (op_Monic_of_Epic f Hf))).
  - (* identities, from [id_monic] read in C^op / 恒等，从 [id_monic] 在 C^op 中读取 *)
    intros x ox.
    exact (Epic_of_op_Monic (@id C x) (@id_monic (C^op) x)).
Defined.

Definition EpiSub_Wide (C : Category) : Wide C (EpiSub C) :=
  fun _ => ttt.

(*
The inverse-pair rows of Mac Lane §II.1's dualization table (extended
   by §IV.3 Exercise 1): a left inverse in C is a right inverse in C^op
   and conversely — the composites are literally the same, only read
   through the opposite composition.  All four directions, mirroring the
   Monic/Epic quartet above; each law is the other side's law by
   conversion, so every obligation is an [exact].

--------
Mac Lane §II.1 的对偶化表的逆对行（由 §IV.3 练习 1 扩展）：在 C 中的左逆是 C^op 中的右逆，反之亦然——合成本质上相同，只是通过相反的组合来读取。四个方向都一样，反映了上面的单态/满态四重奏；每条定律都是另一边定律的转换，因此每个义务都是 [exact]。
*)

#[local] Obligation Tactic := idtac.

Program Definition op_Retraction_of_Section {C : Category} {x y : C}
  (f : x ~> y) (S : Section f) : @Retraction (C^op) y x f := {|
  retract := @section C x y f S
|}.
Next Obligation.
  intros; exact (@section_comp C x y f S).
Qed.

Program Definition Section_of_op_Retraction {C : Category} {x y : C}
  (f : x ~> y) (R : @Retraction (C^op) y x f) : Section f := {|
  section := @retract (C^op) y x f R
|}.
Next Obligation.
  intros; exact (@retract_comp (C^op) y x f R).
Qed.

Program Definition op_Section_of_Retraction {C : Category} {x y : C}
  (f : x ~> y) (R : Retraction f) : @Section (C^op) y x f := {|
  section := @retract C x y f R
|}.
Next Obligation.
  intros; exact (@retract_comp C x y f R).
Qed.

Program Definition Retraction_of_op_Section {C : Category} {x y : C}
  (f : x ~> y) (S : @Section (C^op) y x f) : Retraction f := {|
  retract := @section (C^op) y x f S
|}.
Next Obligation.
  intros; exact (@section_comp (C^op) y x f S).
Qed.
