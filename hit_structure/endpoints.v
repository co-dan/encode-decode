Require Import HoTT.
Require Import polynomial.

Section Endpoints.
  (* The definition of a HIT signature and a HIT for the signature. *)

  (* An endpoint is also called a "constructor term". It is used in
the HIT signature to describe the endpoints of path constructors. *)

  (* Endpoints are parameterized by a family of polynomials which will
be specialized to the point constructors in the definition of HITS.
   *)
  Variable (I : Type)
           (C : I -> polynomial).

  Inductive endpoint : polynomial -> polynomial -> Type :=
  | endpoint_var :
      forall {P : polynomial},
        endpoint P P
  | endpoint_const :
      forall {P : polynomial} {T : Type},
        T -> endpoint P (poly_const T)
  | endpoint_constr :
      forall {P : polynomial} (i : I),
        endpoint P (C i) -> endpoint P poly_var
  | endpoint_fst :
      forall {P Q R : polynomial},
        endpoint P (poly_times Q R) -> endpoint P Q
  | endpoint_snd :
      forall {P Q R : polynomial},
        endpoint P (poly_times Q R) -> endpoint P R
  | endpoint_pair :
      forall {P Q R : polynomial},
        endpoint P Q -> endpoint P R -> endpoint P (poly_times Q R)
  | endpoint_inl :
      forall {P Q R : polynomial},
        endpoint P Q -> endpoint P (poly_plus Q R)
  | endpoint_inr :
      forall {P Q R : polynomial},
        endpoint P R -> endpoint P (poly_plus Q R).

  (* Endpoint acting on data for point constructors. *)
  Fixpoint endpoint_act
           {P Q : polynomial}
           {X : Type}
           (c : forall (i : I), poly_act (C i) X -> X)
           (e : endpoint P Q) (* the endpoint *)
    : poly_act P X -> poly_act Q X
    := match e with
       | endpoint_var _ => idmap
       | endpoint_const _ _ t => fun _ => t
       | endpoint_constr _ i e => fun u => c i (endpoint_act c e u) 
       | endpoint_fst _ _ _ e => fun u => fst(endpoint_act c e u)
       | endpoint_snd _ _ _ e => fun u => snd(endpoint_act c e u)
       | endpoint_pair _ _ _ e1 e2 => fun u => (endpoint_act c e1 u, endpoint_act c e2 u)
       | endpoint_inl _ _ _ e => fun u => inl(endpoint_act c e u)
       | endpoint_inr _ _ _ e => fun u => inr(endpoint_act c e u)
       end.

  Fixpoint endpoint_act_compute
           {P Q : polynomial}
           {X Y : Type}
           (c : forall (i : I), poly_act (C i) X -> X)
           (c' : forall (i : I), poly_act (C i) Y -> Y)
           (e : endpoint P Q)
           (h : X -> Y)
           (H : forall i z, c' i (poly_map (C i) h z) = h(c i z))
    : forall (x : poly_act P X),
      endpoint_act c' e (poly_map P h x) = poly_map Q h (endpoint_act c e x)
    := match e with
       | endpoint_var _ =>
         fun _ => reflexivity _
       | endpoint_const _ _ t =>
         fun _ => reflexivity t
       | endpoint_constr _ i e =>
         fun x =>
           ap (c' i) (endpoint_act_compute c c' e h H x) @ H i _
       | endpoint_fst _ _ _ e =>
         fun x =>
           ap fst (endpoint_act_compute c c' e h H x)
       | endpoint_snd _ _ _ e =>
         fun x =>
           ap snd (endpoint_act_compute c c' e h H x)
       | endpoint_pair _ _ _ e₁ e₂ =>
         fun x => path_prod'
                    (endpoint_act_compute c c' e₁ h H x)
                    (endpoint_act_compute c c' e₂ h H x)
       | endpoint_inl _ _ _ e =>
         fun x =>
           ap inl (endpoint_act_compute c c' e h H x)
       | endpoint_inr _ _ _ e =>
         fun x =>
           ap inr (endpoint_act_compute c c' e h H x)
       end.

  Variable (A : Type)
           (F : A -> Type)
           (c : forall (i : I), poly_act (C i) A -> A)
           (f : forall (i : I) (u : poly_act (C i) A), poly_fam (C i) F u -> F (c i u)).

  (* The dependent action of an endpoint, this is used for
   "lifting" the path constructors in the elimination principle. *)
  Fixpoint endpoint_dact
           {P Q : polynomial}
           (e : endpoint P Q)
    : forall (x : poly_act P A), poly_fam P F x -> poly_fam Q F (endpoint_act c e x)
    := match e with
       | endpoint_var _ => fun _ h => h
       | endpoint_const _ _ t => fun _ _ => t
       | endpoint_constr _ i u => fun x h => f i (endpoint_act c u x) (endpoint_dact u x h)
       | endpoint_fst p p0 p1 e => fun x h => fst (@endpoint_dact p (poly_times p0 p1) e x h)
       | endpoint_snd p p0 p1 e => fun x h => snd (@endpoint_dact p (poly_times p0 p1) e x h)
       | endpoint_pair _ _ _ e1 e2 => fun x h => (endpoint_dact e1 x h, endpoint_dact e2 x h)
       | endpoint_inl p p0 _ e => fun x h => @endpoint_dact p p0 e x h
       | endpoint_inr p _ p1 e => fun x h => @endpoint_dact p p1 e x h
       end.

  (* If [h] commutes with constructors, then it commutes with all endpoints. *)
  Fixpoint endpoint_dact_compute
           {P Q : polynomial}
           (e : endpoint P Q)
    : forall (x : poly_act P A)
             (h : forall x, F x)
             (H : forall i u, h (c i u) = f i u (poly_dmap (C i) h u)),
      endpoint_dact e x (poly_dmap P h x) = poly_dmap Q h (endpoint_act c e x)
    := match e with
       | endpoint_var _ => fun _ _ _ => reflexivity _
       | endpoint_const _ _ t => fun _ _ _ => reflexivity t
       | endpoint_constr _ i e' =>
         fun x h H => let u := (endpoint_act c e' x) in
                      ap (f i u) (endpoint_dact_compute e' x h H) @ (H i u)^
       | endpoint_fst _ _ _ e' =>
         fun x h H =>
           ap fst (endpoint_dact_compute e' x h H)
       | endpoint_snd _ _ _ e' =>
         fun x h H =>
           ap snd (endpoint_dact_compute e' x h H)
       | endpoint_pair _ _ _ e1 e2 =>
         fun x h H =>
           path_prod'
             (endpoint_dact_compute e1 x h H)
             (endpoint_dact_compute e2 x h H)
       | endpoint_inl _ _ _ e' => endpoint_dact_compute e'
       | endpoint_inr _ _ _ e' => endpoint_dact_compute e'
       end.

  (* A general HIT might have an arbitrary number of endpoints and therefore an arbitrarily
   nested point constructors. Our construction of a HIT presumes that there is a bound to
   the nesting. We define here what it means for an endpoint to have such a bound. *)
  Inductive endpoint_rank : forall {P Q : polynomial}, endpoint P Q -> nat -> Type :=
  | rank_var :
      forall {P : polynomial} (n : nat),
        endpoint_rank (@endpoint_var P) n
  | rank_const :
      forall {P : polynomial} {T : Type} (t : T) (n : nat),
        endpoint_rank (@endpoint_const P _ t) n
  | rank_constr :
      forall {P : polynomial} (i : I) (n : nat) (e : endpoint P (C i)),
        endpoint_rank e n -> endpoint_rank (endpoint_constr i e) (S n)
  | rank_fst :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P (poly_times Q R)),
        endpoint_rank e n -> endpoint_rank (endpoint_fst e) n
  | rank_snd :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P (poly_times Q R)),
        endpoint_rank e n -> endpoint_rank (endpoint_snd e) n
  | rank_inl :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P Q),
        endpoint_rank e n -> endpoint_rank (@endpoint_inl _ _ R e) n
  | rank_inr :
      forall {P Q R : polynomial} (n : nat) (e : endpoint P R),
        endpoint_rank e n -> endpoint_rank (@endpoint_inr _ Q _ e) n.
End Endpoints.

Arguments endpoint {_} _ _ _.
Arguments endpoint_var {_ _} {_}.
Arguments endpoint_const {_ _} {_} {_} _.
Arguments endpoint_constr {_ _} {_} _ _ .
Arguments endpoint_fst {_ _} {_ _ _} _.
Arguments endpoint_snd {_ _} {_ _ _} _.
Arguments endpoint_pair {_ _} {_ _ _} _ _.
Arguments endpoint_inl {_ _} {_ _ _} _.
Arguments endpoint_inr {_ _} {_ _ _} _.

Arguments endpoint_act {I C P Q X} _ _ _.
Arguments endpoint_dact {I C A F} c _ {P Q} _ _ _.
Arguments endpoint_act_compute {_ _ _ _ _ _} _ _ _ _ _ _.
Arguments endpoint_dact_compute {_ _ _} _ _ _ {P Q} _ _ _ _.

Arguments endpoint_rank {_} _ {_ _} _ _.

Section endpoint_const.
  Variable (I : Type) (C : I -> polynomial)
           (A : Type) (B : Type)
           (c : forall i : I, poly_act (C i) A -> A).
  
  Definition endpoint_dact_nondep
             (f : forall i (u : poly_act (C i) A), poly_fam (C i) (fun _ => B) u -> B)
             {P Q : polynomial}
             (e : endpoint C P Q)
             (x : poly_act P A) (h : poly_fam P (fun _ => B) x)
    := @endpoint_dact I C A (fun _ => B) c f P Q e x h.

  Variable (f : forall i, poly_act (C i) B -> B).
  
  Definition endpoint_dact_rec
             {P Q : polynomial}
             (e : endpoint C P Q)
             (x : poly_act P A) (h : poly_fam P (fun _ => B) x)
    := @endpoint_dact I C A (fun _ => B) c (fun i _ u => f i (fam_const _ u)) P Q e x h.

  Fixpoint endpoint_dact_const
           {P Q : polynomial}
           (e : endpoint C P Q)
    : forall (x : poly_act P A) (h : poly_fam P (fun _ => B) x),
      fam_const _ (@endpoint_dact I C A _ c (fun i _ u => f i (fam_const _ u)) P Q e x h)
      =
      @endpoint_act I C P Q B f e (fam_const _ h)
    := match e with
       | endpoint_var _ => fun _ _ =>  reflexivity _
       | endpoint_const _ _ t => fun _ _ => reflexivity t
       | endpoint_constr _ i e =>
         fun x h =>
           ap (f i) (endpoint_dact_const e x h)
       | endpoint_fst _ _ _ e =>
         fun x h =>
           ap fst (endpoint_dact_const e x h)
       | endpoint_snd _ _ _ e =>
         fun x h =>
           ap snd (endpoint_dact_const e x h)
       | endpoint_pair _ _ _ e₁ e₂ =>
         fun x h =>
           path_prod' (endpoint_dact_const e₁ x h) (endpoint_dact_const e₂ x h)
       | endpoint_inl _ _ _ e =>
         fun x h =>
           ap inl (endpoint_dact_const e x h)
       | endpoint_inr _ _ _ e =>
         fun x h =>
           ap inr (endpoint_dact_const e x h)
       end.
End endpoint_const.

Arguments endpoint_dact_nondep {I C A B} c f {P Q}.
Arguments endpoint_dact_rec {I C A B} c f {P Q}.
Arguments endpoint_dact_const {I C A B} c f {P Q}.