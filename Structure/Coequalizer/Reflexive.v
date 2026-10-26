Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Coequalizer.

Generalizable All Variables.

(* * * Reflexive pairs and reflexive coequalizers / * * 自反对和自反余等化 *)

(*
 nLab:      https://ncatlab.org/nlab/show/reflexive+coequalizer
 Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

 A parallel pair f, g : x ~> y is *reflexive* when the two maps share a
 common section s : y ~> x, i.e.

 f ∘ s ≈ id   and   g ∘ s ≈ id.

 The name comes from the motivating example: when x is the total object
 of a relation on y with projections f and g — say a congruence being
 quotiented — a common section is precisely a reflexivity witness,
 embedding y into the relation along the diagonal.

 A *reflexive coequalizer* is a coequalizer of a reflexive pair.
 [HasReflexiveCoequalizers] packages a choice of elementary coequalizer
 (in the [IsCoequalizer] sense of [Structure/Coequalizer.v]) for every
 reflexive pair; it is the reflexive analogue of [HasCoequalizers], and
 a strictly weaker demand on the category.  Reflexive coequalizers are
 the workhorse of the theory of algebras: the canonical presentation of
 an algebra by free algebras is a reflexive pair, so categories of
 algebras are as cocomplete as their reflexive coequalizers allow
 (Linton, “Coequalizers in categories of algebras”, 1969).

 Being given by two equations with no quantification over the ambient
 category, reflexive pairs are preserved by arbitrary functors
 ([functor_preserves_reflexive]), just as split coequalizers are in
 [Structure/Coequalizer/Split.v] — although the *coequalizer* of a
 reflexive pair, unlike that of a split one, need not be preserved.

 Beck's contractible pairs, Structure/Coequalizer/Contractible.v
 (#480), are another equational condition on a parallel pair; the two
 are incomparable (Test/ProbeContractible480.v, in both directions). 

 --------
 nLab:       https://ncatlab.org/nlab/show/reflexive+coequalizer 
 Wikipedia:  https://en.wikipedia.org/wiki/Coequaliser 

 当一对平行映射 f, g : x ~> y 共享一个公共截面 s : y ~> x 时，这对映射被称为*自反*，即：

 f ∘ s ≈ id   且   g ∘ s ≈ id。

 这个名称来源于激励性例子：当 x 是 y 上某个关系的总对象且有投影 f 和 g 时——比如某个同余被取商——一个公共截面正是自反性的证据，将 y 沿对角线嵌入到该关系中。一个*自反余等化子*是一个自反对的余等化子。
 [HasReflexiveCoequalizers] 为每一个自反对封装了一个基本余等化子的选择（在 [IsCoequalizer] 的 [Structure/Coequalizer.v] 意义下）；它是 [HasCoequalizers] 的自反类比，并且对范畴的要求严格较弱。自反余等化子是代数理论的主力工具：通过自由代数给出代数的规范表达是一个自反对，因此代数范畴的余完备性取决于它们允许的自反余等化子（Linton，“代数范畴中的余等化子”，1969年）。由两个方程给出且没有对背景范畴进行量化，自反对偶对会被任意函子保持（[functor_preserves_reflexive]），就像分裂共等化器在[Structure/Coequalizer/Split.v]中一样——尽管自反对偶对的*共等化器*与分裂共等化器不同，不一定会被保持。

 Beck的可收缩对，Structure/Coequalizer/Contractible.v（#480），是对平行对的另一种方程条件；这两者是不可比的（Test/ProbeContractible480.v，在两个方向上）。
*)

(*
 The equational data: one map that both f and g retract. 

 --------
 方程数据：一个 f 和 g 都能够回缩的映射。
*)
Record ReflexivePair {C : Category} {x y : C} (f g : x ~> y) := {
  refl_section : y ~> x;                   (* the common section / 公共部分 *)
  refl_section_f : f ∘ refl_section ≈ id;  (* f retracts it / f 收回它 *)
  refl_section_g : g ∘ refl_section ≈ id   (* and so does g / g 也是如此 *)
}.

Arguments refl_section   {_ _ _ _ _} _.
Arguments refl_section_f {_ _ _ _ _} _.
Arguments refl_section_g {_ _ _ _ _} _.

(*
 A category has reflexive coequalizers when every reflexive pair
 carries an elementary coequalizer.  Compare [HasCoequalizers] in
 [Structure/Coequalizer.v], which asks the same of every parallel
 pair. 

 --------
 当每个自反对都具有基本的余等化子时，一个范畴就具有自反余等化子。比较  [HasCoequalizers] 在 [Structure/Coequalizer.v] 中，它对每个平行对提出了相同的要求。
*)
Class HasReflexiveCoequalizers (C : Category) := {
  reflexive_coeq {x y : C} (f g : x ~> y) :
    ReflexivePair f g → ∃ (q : C) (e : y ~> q), IsCoequalizer f g q e
}.

(** ** Recognizing reflexive pairs / ** 识别反身词对 *)

(*
 Exhibiting a common section in the style of [scoeq_t] from
 [Structure/Coequalizer/Split.v] — a single map split by both f and g —
 is exactly what it takes: the record is precisely this data. 

 --------
 展示 [Structure/Coequalizer/Split.v] 中 [scoeq_t] 风格的常见部分——一个被 f 和 g 同时分割的单一地图——正是所需的：记录正是这些数据。
*)
Lemma common_section_reflexive {C : Category} {x y : C} (f g : x ~> y)
  (s : y ~> x) (Hf : f ∘ s ≈ id) (Hg : g ∘ s ≈ id) :
  ReflexivePair f g.
Proof.
  exact {| refl_section   := s
         ; refl_section_f := Hf
         ; refl_section_g := Hg |}.
Defined.

(*
 When every parallel pair has a coequalizer, so in particular does
 every reflexive one. 

 --------
 当每个平行对都有一个共同余等化子时，特别是每个自反对也都有一个。
*)
#[export] Instance HasCoequalizers_HasReflexiveCoequalizers
  {C : Category} `{H : @HasCoequalizers C} : HasReflexiveCoequalizers C := {|
  reflexive_coeq := fun x y f g _ => @coeq C H x y f g
|}.

(* * ** Functors preserve reflexive pairs / * **函子保持自反对 *)

(*
 Push the common section through fmap; both retraction laws follow from
 the corresponding law in the source by functoriality.  The proof ends
 with [Defined] so that the transported section [fmap (refl_section R)]
 stays visible to conversion. 

 --------
 通过 fmap 推动公共部分；两个收缩律都来自源的相应律，通过函子性。证明以 [Defined] 结束，这样传递的部分 [fmap (refl_section R)] 对转换保持可见。
*)
Theorem functor_preserves_reflexive {C D : Category} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  ReflexivePair f g → ReflexivePair (fmap[F] f) (fmap[F] g).
Proof.
  intros R.
  unshelve refine {| refl_section := fmap[F] (refl_section R) |}.
  - (* fmap f ∘ fmap s ≈ id / fmap f ∘ fmap s ≈ id *)
    rewrite <- fmap_comp.
    rewrite (refl_section_f R).
    apply fmap_id.
  - (* fmap g ∘ fmap s ≈ id / fmap g ∘ fmap s ≈ id *)
    rewrite <- fmap_comp.
    rewrite (refl_section_g R).
    apply fmap_id.
Defined.
