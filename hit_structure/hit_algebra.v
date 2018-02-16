Require Import HoTT.
Require Import polynomial.
Require Import endpoints.
Require Import hit_code.
Require Import heterogeneous_equality.

Fixpoint fam_const_compute
          {P : polynomial}
          {A B : Type}
          (f : A -> B)
  : forall z, poly_map P f z = fam_const z (poly_dmap P f z)
  := match P with
     | poly_var => fun _ => idpath
     | poly_const _ => fun _ => idpath
     | poly_times P₁ P₂ =>
       fun z => path_prod' (fam_const_compute f _) (fam_const_compute f _)
     | poly_plus P₁ P₂ =>
       fun z =>
         match z with
         | inl z => ap inl (fam_const_compute f z)
         | inr z => ap inr (fam_const_compute f z)
         end
     end.

(* Algebras for a HIT signature. *)
Record hit_algebra (Σ : hit_signature) :=
  { H_T :> Type ;
    H_point : forall (i : sig_point_index Σ), poly_act (sig_point Σ i) H_T -> H_T ;
    H_path : forall (j : sig_path_index Σ) (u : poly_act (sig_path_param Σ j) H_T),
        endpoint_act H_point (sig_path_lhs Σ j) u
        =
        endpoint_act H_point (sig_path_rhs Σ j) u
  }.

Definition hit_is_algebra (Σ : hit_signature) (H : HIT Σ) : hit_algebra Σ
  := {|H_T := H ; H_point := hit_point ; H_path := hit_path|}.

Section hit_morphism.
  Variable (Σ : hit_signature)
           (A₁ A₂ : hit_algebra Σ).

  Definition preserves_point (f : A₁ -> A₂) : Type
    := forall (i : sig_point_index Σ) (x : poly_act (sig_point Σ i) A₁),
      f (H_point Σ A₁ i x) = H_point Σ A₂ i (poly_map (sig_point Σ i) f x).

  Definition preserves_path
             (f : A₁ -> A₂)
             (H : preserves_point f)
    : Type.
  Proof.
    refine (forall (j : sig_path_index Σ)
                   (u : poly_act (sig_path_param Σ j) A₁), _).
    refine (square (H_path Σ A₂ j (poly_map (sig_path_param Σ j) f u))
                   _
                   _
                   (ap f (H_path Σ A₁ j u))).
    - refine (endpoint_act_compute _ _ _ _ _ _).
      intros.
      symmetry.
      apply H.
    - refine (endpoint_act_compute _ _ _ _ _ _).
      intros.
      symmetry.
      apply H.
  Defined.
End hit_morphism.

Arguments preserves_point {Σ A₁ A₂} f.
Arguments preserves_path {Σ A₁ A₂} f H.

(* Algebras for a HIT signature. *)
Class hit_morphism
       {Σ : hit_signature}
       {A₁ A₂ : hit_algebra Σ}
       (f : A₁ -> A₂) :=
  { f_point : preserves_point f ;
    f_path : preserves_path f f_point
  }.