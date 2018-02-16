Require Import HoTT.
Require Import polynomial.
Require Import endpoints.
Require Import heterogeneous_equality.

(* A HIT signature is specified by point constructors and path constructors.

   Note: we are allowing an arbitrary family of poitn and path construcrors.
         We will restrict them later on in existence theorem.
 *)
Structure hit_signature :=
  {
    (* indexing for point constructors *)
    sig_point_index : Type ;

    (* the signatures for point constructors *)
    sig_point : sig_point_index -> polynomial ;

    (* indexing for path constructors *)
    sig_path_index : Type ;

    (* the parameters of each path constructor *)
    sig_path_param : sig_path_index -> polynomial ;

    (* the left and right endpoints of path constructors *)
    sig_path_lhs : forall i, endpoint sig_point (sig_path_param i) poly_var ;
    sig_path_rhs : forall i, endpoint sig_point (sig_path_param i) poly_var
  }.

(* A HIT signature has rank [n] if all of its endpoints do. *)
Definition hit_rank Σ n :=
  (forall (j : sig_path_index Σ), endpoint_rank (sig_point Σ) (sig_path_lhs Σ j) n) *
  (forall (j : sig_path_index Σ), endpoint_rank (sig_point Σ) (sig_path_rhs Σ j) n).

Section HIT_Definition.
  (* We define HIT for signature [Σ]. *)
  Variable (Σ : hit_signature).

  (* The type of a lift of the point constructor [c] over a family [F]. *)
  Definition point_over
             {H : Type} (* the carrier type *)
             (F : H -> Type)
             (c : forall i, poly_act (sig_point Σ i) H -> H) (* point constructors *)
             (p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
                              endpoint_act c (sig_path_rhs Σ j) u) (* path constructors *)
    := forall (i : sig_point_index Σ) (u : poly_act (sig_point Σ i) H),
      poly_fam (sig_point Σ i) F u -> F (c i u).

  (* The type of a lift of the path constructor [p] over a family [F]. *)
  Definition path_over
             {H : Type}
             {F : H -> Type}
             {c : forall i, poly_act (sig_point Σ i) H -> H} (* point constructors *)
             {p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
                              endpoint_act c (sig_path_rhs Σ j) u} (* path constructors *)
             (c' : point_over F c p)
    := forall (j : sig_path_index Σ)
              (x : poly_act (sig_path_param Σ j) H)
              (h : poly_fam (sig_path_param Σ j) F x),
      transport _ (p j x) (endpoint_dact c c' (sig_path_lhs Σ j) x h) =
      endpoint_dact c c' (sig_path_rhs Σ j) x h.

  Definition hit_path_beta_eq_square
             (H : Type) (* the carrier type *)
             (c : forall i, poly_act (sig_point Σ i) H -> H) (* point constructors *)
             (p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
                              endpoint_act c (sig_path_rhs Σ j) u) (* path constructors *)
             (E : (* the eliminator *)
                forall (F : H -> Type)
                       (c' : point_over F c p)
                       (p' : path_over c'),
                forall (x : H), F x)
             (point_beta : (* the point computation rule *)
                forall (F : H -> Type)
                       (c' : point_over F c p)
                       (p' : path_over c')
                       i (t : poly_act (sig_point Σ i) H),
                  E F c' p' (c i t) = c' i t (poly_dmap (sig_point Σ i) (E F c' p') t)) :
    Type.
  Proof.
    simple refine (forall (F : H -> Type)
                          (j : sig_path_index Σ)
                          (c' : point_over F c p)
                          (p' : path_over c')
                          (t : poly_act (sig_path_param Σ j) H), _).
    simple refine (square (p' j t (poly_dmap _ (E F c' p') t)) _ _ (apD (E F c' p') (p j t))).
    - apply (endpoint_dact_compute F c c' (sig_path_rhs Σ j) t).
      exact (point_beta F c' p').
    - apply (ap (transport F (p j t))).
      apply (endpoint_dact_compute F c c' (sig_path_lhs Σ j) t).
      exact (point_beta F c' p').
  Defined.

  Structure HIT :=
    {
      (* the carrier of the HIT *)
      hit_carrier :> Type ;

      (* the point constructor *)
      hit_point : forall i, poly_act (sig_point Σ i) hit_carrier -> hit_carrier ;

      (* path constructors *)
      hit_path : forall j u, endpoint_act hit_point (sig_path_lhs Σ j) u =
                             endpoint_act hit_point (sig_path_rhs Σ j) u ;

      (* the eliminator *)
      hit_ind :
        forall (F : hit_carrier -> Type)
               (c : point_over F hit_point hit_path)
               (p : path_over c)
               (x : hit_carrier),
          F x ;

      (* computation rule for points *)
      hit_point_beta :
        forall (F : hit_carrier -> Type)
               (c : point_over F hit_point hit_path)
               (p : path_over c)
               (i : sig_point_index Σ)
               (t : poly_act (sig_point Σ i) hit_carrier),
          hit_ind F c p (hit_point i t) =
          c i t (poly_dmap (sig_point Σ i) (hit_ind F c p) t) ;

      (* computation rule for paths *)
      hit_path_beta :
        hit_path_beta_eq_square hit_carrier hit_point hit_path hit_ind hit_point_beta
    }.
End HIT_Definition.

Arguments hit_point {_ _} _ _.
Arguments hit_path {_ _} _ _.
Arguments hit_ind {_ _} _ _ _ _.