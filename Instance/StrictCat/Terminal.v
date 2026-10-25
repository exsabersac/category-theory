Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(* * * 1 is the terminal object of StrictCat / * * 1 是 StrictCat 的终端对象 *)

(*
 nLab: https://ncatlab.org/nlab/show/terminal+category

 [Instance.One] shows that the terminal category [_1] is terminal in the
 *weak* category [Cat], where functors are compared up to natural
 isomorphism.  Here we show the stronger fact that [_1] is also terminal in
 [StrictCat], where functors are compared by strict equality
 ([Functor_StrictEq_Setoid]): any two functors [F G : C ⟶ 1] are equal on
 the nose, because both objects and morphisms of [1] are inhabitants of the
 contractible type [poly_unit].  The witness [one] is again the erasure
 functor [Erase].

 This instance is the prerequisite for exhibiting the funny tensor product
 as a *semicartesian* monoidal structure on [StrictCat], whose unit [_1] is
 the terminal object. 

 --------
 nLab:  https://ncatlab.org/nlab/show/terminal+category 

 [Instance.One] 显示末端范畴 [_1] 是 *弱* 范畴 [Cat] 中的末端对象，其中函子被比作自然同构。这里我们展示更强的事实：[_1] 在 [StrictCat] 中也是末端对象，其中函子按严格相等 [Functor_StrictEq_Setoid] 比较：任何两个函子 [F G : C ⟶ 1] 都完全相等，因为 [1] 的对象和态射都是可收缩类型 [poly_unit] 的元素。证人 [one] 再次是擦除函子 [Erase]。

 这个实例是将有趣的张量积展示为 [StrictCat] 上的*半笛卡尔*幺半群结构的前提，其单位 [_1] 是末端对象。
*)

(* [poly_unit] is contractible: any two inhabitants are equal. / [poly_unit] 是可收缩的：任何两个元素都是相等的。 *)
Lemma poly_unit_eq (u v : poly_unit) : u = v.
Proof. now destruct u, v. Qed.

(*
 1 is the terminal object of StrictCat, witnessed by the unique functor
 [Erase].  Uniqueness is strict: on objects both functors land in the
 contractible [poly_unit], and the transported morphism maps agree because
 the homs of [1] are likewise [poly_unit] under [Morphism_equality]. 

 --------
 1 是 StrictCat 的终对象，由唯一函子 [Erase] 体现。唯一性是严格的：在对象上两个函子都映射到可缩的 [poly_unit]，并且传递的态射映射一致，因为在 [1] 中的 Hom 也在 [Morphism_equality] 下是 [poly_unit]。
*)
#[export]
Program Instance StrictCat_Terminal : @Terminal StrictCat := {
  terminal_obj := _1;        (* the terminal category 1 / 终端类别 1 *)
  one := Erase               (* the unique functor ! : C ⟶ 1 / 唯一函子 ! : C ⟶ 1 *)
}.
Next Obligation.
  exists (fun c => poly_unit_eq (f c) (g c)).
  intros c c' h; simpl.
  apply poly_unit_eq.
Qed.
