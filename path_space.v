Require Import HoTT.
Require Import ED.polynomial.
Require Import ED.hit_structure.
Require Import ED.groupoid.

Definition lift_constr
           {P : polynomial} {A : Type}
           (f : poly_act P A -> A)
  : relation_morph (hom (lift_groupoid (path_groupoid A) P)) (hom (path_groupoid A)).
Proof.
  exists f.
  induction P ; simpl in *.
  - intros ? ? p.
    strip_truncations.
    exact (tr (ap f p)).
  - intros ? ? p.
    strip_truncations.
    exact (tr (ap f p)).
  - intros [x1 y1] [x2 y2] [p1 p2].
    pose (IHP1 (fun z => f(z, y1)) _ _ p1) as q1.
    pose (IHP2 (fun z => f(x2, z)) _ _ p2) as q2.
    exact (comp A (path_groupoid A) (f(x1, y1)) (f(x2,y1)) (f(x2, y2)) q1 q2).
  - intros x y p.
    specialize (IHP1 (f o inl)).
    specialize (IHP2 (f o inr)).
    simpl in *.
    destruct x as [x | x], y as [y | y].
    + exact (IHP1 _ _ p).
    + contradiction.
    + contradiction.
    + exact (IHP2 _ _ p).
Defined.

Global Instance constr_grpd
       {P : polynomial} {A : Type}
       (f : poly_act P A -> A)
  : is_grpd_morph (lift_constr f).
Proof.
  unshelve esplit.
  - induction P.
    + reflexivity.
    + reflexivity.
    + intros [x1 x2].
      specialize (IHP1 (fun z => f(z,x2)) x1).
      specialize (IHP2 (fun z => f(x1,z)) x2).
      cbn -[lift_constr] in *.
      admit.
    + intros [x | x].
      * exact (IHP1 _ x).
      * exact (IHP2 _ x).
  - intros.
    induction P.
    + strip_truncations.
      induction p.
      reflexivity.
    + strip_truncations.
      induction p.
      reflexivity.
    + admit.
    + destruct x as [x | x], y as [y | y] ; try contradiction.
      * exact (IHP1 _ x y p).
      * exact (IHP2 _ x y p).
  - intros.
    induction P.
    + strip_truncations.
      induction p, q.
      reflexivity.
    + strip_truncations.
      induction p, q.
      reflexivity.
    + admit.
    + destruct x as [x | x], y as [y | y], z as [z | z] ; try contradiction.
      * exact (IHP1 _ x y z p q).
      * exact (IHP2 _ x y z p q).
Admitted.

Lemma test2
      {A : Type}
      {B : A -> Type}
      {a b : A}
      (p : a = b)
      (x : B a)
  : transport (fun (z : A) => Trunc 0 (B z)) p (tr x)
    =
    tr (transport B p x).
Proof.
  induction p.
  reflexivity.
Defined.              

Lemma test
      {A B : Type}
      {f g : A -> B}
      {a₁ a₂ : A}
      (p : a₁ = a₂)
      (q : Trunc 0 (f a₁ = g a₁))
  : transport (fun (z : A) => Trunc 0 (f z = g z)) p q
    = (tr (ap f p^) · q · tr (ap g p)).
Proof.
  strip_truncations.
  rewrite (@test2 A).
  rewrite transport_paths_FlFr.
  hott_simpl.
Defined.  

Section path_algebra.
  Variable (Σ : hit_signature) (H : HIT Σ).

  Definition path_alg : Halg Σ H.
  Proof.
    unshelve esplit.
    - exact (path_groupoid H).
    - intros j u.
      apply tr.
      exact (hit_path j u).
    - intros i.
      unshelve esplit.
      + apply lift_constr.
        exact (hit_point i).
      + apply tr.
        apply constr_grpd.
    - intros j u ; simpl.
      rewrite test.
      hott_simpl.
      rewrite !ec.
      reflexivity.
  Defined.
End path_algebra.