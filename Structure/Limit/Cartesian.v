Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Instance.Two.Discrete.

Generalizable All Variables.

(*
   * * Binary products as limits of a discrete two-object diagram 

   --------
   * * 二元积作为离散的两个对象图的极限
*)

(*
 nLab:      https://ncatlab.org/nlab/show/product
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

 A binary product is the limit of a diagram of shape [Two_Discrete], the
 discrete category with two objects and only identity morphisms (see
 [Instance/Two/Discrete.v]). A functor F : Two_Discrete ⟶ C picks out an
 ordered pair of objects (F TwoDX, F TwoDY); a cone over F is an apex with
 two legs into those objects, and the limit cone is exactly the product
 F TwoDX × F TwoDY with its projections exl, exr as legs. The terminal-cone
 universal property of the limit coincides with the product UMP
 ([ump_products] in [Structure/Cartesian.v]); the empty discrete diagram
 gives the nullary product, the terminal object (see [Structure/Limit/
 Terminal.v]).

 This theorem records the equivalence in both directions: C has a limit for
 every two-object discrete diagram iff C is cartesian (has all binary
 products).

 (∀ F : Two_Discrete ⟶ C, Limit F)  ↔  Cartesian C

 Left to right: a chosen pair of objects is presented as [Pick_Two x y], the
 limit's apex becomes the product object, and the limit legs become exl/exr;
 the limit's mediating morphism becomes the pairing [fork]. Right to left:
 the product object is the cone apex and exl/exr are its legs, with [fork]
 supplying the unique factorization. 

 --------
 nLab: https://ncatlab.org/nlab/show/product
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

 二元积是形状为 [Two_Discrete] 的图的极限，即具有两个对象且只有恒等态射的离散范畴（参见 [Instance/Two/Discrete.v]）。函子 F : Two_Discrete ⟶ C 选出一对有序对象 (F TwoDX, F TwoDY)；F 上的锥是一个顶点及两条指向这些对象的腿，而极限锥恰好是积 F TwoDX × F TwoDY 及其投影 exl、exr 作为腿。极限的终锥泛性质与积的泛性质 (UMP) 相符合（参见 [ump_products] 在 [Structure/Cartesian.v]）；空的离散图给出零元积，即终对象（参见 [Structure/Limit/Terminal.v]）。该定理记录了双向等价：C 对每个两对象离散图都有极限当且仅当 C 是笛卡尔闭的（即具有所有二元积）。

 (∀ F : Two_Discrete ⟶ C, Limit F)  ↔  Cartesian C

 从左到右：选定的一对对象表示为 [Pick_Two x y]，极限的顶点成为积对象，极限的射线变为 exl/exr；极限的中介态射变为配对 [fork]。 从右到左：积对象是锥顶点，exl/exr 是它的射线，[fork] 提供唯一分解。
*)

Theorem Cartesian_Limit (C : Category) :
  (∀ F : Two_Discrete ⟶ C, Limit F) ↔ @Cartesian C.
Proof.
  split; intros.
  - construct.
    + exact (vertex_obj[X (Pick_Two X0 X1)]).
    + simpl.
      given (cone : Cone (Pick_Two y z)). {
        unshelve (refine {| vertex_obj := x |}); intros.
        unshelve econstructor.
        - destruct x0; simpl; auto.
        - intros. destruct x0, y0; cat;
          pose proof (TwoDHom_inv _ _ f0) as H; inv H.
      }
      destruct (@ump_limits _ _ _ (X (Pick_Two y z)) cone).
      apply unique_obj.
    + simpl.
      destruct (X (Pick_Two x y)).
      destruct limit_cone.
      simpl. change x with (fobj[Pick_Two x y] TwoDX).
      apply vertex_map.
    + simpl.
      destruct (X (Pick_Two x y)).
      destruct limit_cone.
      simpl. change y with (fobj[Pick_Two x y] TwoDY).
      apply vertex_map.
    + proper.
      apply uniqueness; simpl; intros.
      destruct x2; simpl.
      * rewrite H.
        destruct (ump_limits _).
        apply (unique_property TwoDX).
      * rewrite H0.
        destruct (ump_limits _).
        apply (unique_property TwoDY).
    + simpl.
      destruct (ump_limits _); simpl in *.
      split; intros.
      * split.
        ** rewrite H.
           apply (unique_property TwoDX).
        ** rewrite H.
           apply (unique_property TwoDY).
      * destruct H.
        symmetry.
        apply uniqueness; intros.
        destruct x0; auto.
  - construct.
    + construct; [ exact (product_obj (fobj[F] TwoDX) (fobj[F] TwoDY)) | construct ].
      * destruct x.
        ** apply exl.
        ** apply exr.
      * simpl.
        destruct x, y;
        pose proof (TwoDHom_inv _ _ f) as H; inv H.
        ** now rewrite fmap_id, id_left.
        ** now rewrite fmap_id, id_left.
    + unshelve eexists.
      * apply fork; destruct N; apply vertex_map.
      * intros.
        destruct x; simpl.
        ** now rewrite exl_fork.
        ** now rewrite exr_fork.
      * intros.
        simpl in *.
        rewrite <- !H.
        rewrite fork_comp.
        rewrite fork_exl_exr.
        cat.
Qed.
