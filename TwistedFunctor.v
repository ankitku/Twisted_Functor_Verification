(** * Formalization of the Semidirect Product *)

(** All definitions and proofs here are from the paper "How to Twist Pointers without Breaking Them" by Chauhan,Kurur,Yorgey.  *)

(** In this file, we will represent mathematical structures such as monoids, functors and semidirect products using type classes. Type classes are a recent addition to Coq, and make the code highly readable. They allow generic programming for a class of types, and present functions specific for those types.*)

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.Arith.
Require Import Datatypes.

Open Scope program_scope. 
Open Scope core_scope. 
Open Scope type_scope.
(* ################################################################# *)

(** * Monoid *)
(** First we define the monoid type class. It has the identity element "one" , and an append function "append". The class also contains specifications for identity and associativity laws. *)
Class Monoid (a : Type) :=
  {
    one : a;
    append : a -> a -> a;

    left_identity : forall x, append one x = x ;
    right_identity : forall x, append x one = x ;
    associativity : forall x y z, append x (append y z) = append (append x y) z
  }.

(** nat is an instance of monoid. And we need to prove that ! *)
Instance Mnat : Monoid nat.
Proof.
  split with 0 plus; intros; auto with arith.
Defined.

Notation " m1 ♢ m2 " := (append m1 m2)
  (at level 40, left associativity).

(** A commutative monoid is a monoid, with commutativity :) *)
Class Commutative_Monoid a `{Monoid a} :=
  {    
    commutativity : forall x y, x ♢ y = y ♢ x
  }.

Print  Commutative_Monoid.

(** * Functor*)
(** Similarly, we define a functor, using a function f to map elements from one type to another. We then define fmap and its identity and homomorphism. *)
Class Functor (f : Type -> Type) :=
  {
    fmap {a b : Type} : (a -> b) -> (f a) -> (f b);

    ftor_identity : forall a (x : f a), fmap id x = x;
    ftor_homomorphism : forall a b c (p : b -> c) (q : a -> b), fmap (p ∘ q) = (fmap p) ∘ (fmap q)
  }.

(** An applicative functor is a functor, along with pure and app_star functions. Properties of app_star, including Identity, composition and homomorphism are also defined. *)
Class Applicative_Functor f `{Functor (f : Type -> Type)} :=
  {
    pure {a : Type} : a -> f a;
    app_star {a b : Type} : f (a -> b) -> f a -> f b;

    appftor_identity : forall a (v : f a) , app_star (pure id) v = v;
    appftor_composition : forall a b c (u : f (b -> c)) (v : f (a -> b)) (w : f a), app_star (app_star (app_star (pure compose) u) v) w = app_star u (app_star v w); 
    appftor_homomorphism : forall a b (f : a -> b) (x : a), app_star (pure f) (pure x) = pure (f x)
  }.

Notation " fab <*> fa " := (app_star fab fa) (at level 40, left associativity).

(** Monoidal Functor is intuitively a type indexed monoid, in which the identity element is f applied on unit, and append takes 2 (different) types a and b, both of which are mapped to the same category by f, and then applied using mf_star  *)
Class Monoidal_Functor f `{Functor (f : Type -> Type)} :=
  {
    mf_unit : f unit;
    mf_star {a b : Type} : f a -> f b -> f (a * b);

    mf_left_identity : forall a {v : f a}, fmap snd (mf_star mf_unit v) = v;
    mf_right_identity : forall a {v : f a}, fmap fst (mf_star v mf_unit) = v;

  }.

Notation " u ✶ v " := (mf_star u v) (at level 40, left associativity).

(** * Action*)
(** given a monoid m and a type a, a left action of m on a is a function by which elements of m can act as transformations on elements of type a. As monoids accumulate result, the actions also accumulate as is evident from the definition of act_comp. *)
Class Action m a `{Monoid m}  :=
  {
    act : m -> a -> a;

    act_id : forall {e : a}, act one e = e;
    act_comp : forall {m1 m2 : m} {e : a}, act (m1 ♢ m2) e = (act m1 (act m2 e))
  }.


Notation "m • a" := (act m a) (at level 60, right associativity). 

(** Action of m on a can distribute, when a is itself a monoid composed of a1 and a2 *)
Class Distr_Action m a `{Action m a} `{Monoid a}:=
  {
    d_act_annih : forall {m1 : m}, m1 • one = one;
    d_act_dist : forall {m1 : m} {a1 a2 : a},  m1 • (a1 ♢ a2) = (m1 • a1) ♢ (m1 • a2)
  }.

(** * Semidirect Product *)

(** Semidirect Product is just the product type (a,m) under the monoid operation, where m is a monoid acting distributively on the monoid a*)

(** Here we define sdp a b which is the product (a,b) *)
Inductive sdp (a b : Type) : Type :=
  | SDP : a -> b -> sdp a b.

Notation "a ⋊ b" := sdp (at level 40, left associativity). 
Notation "a ':⋊' b" := SDP (at level 40, left associativity). 

Check SDP.
Check sdp.

(** Now we define the identity and append operations of Semidirect Product*)
Section SDP.
  Variables (a m : Type) (A : Monoid a) (M : Monoid m) (AMA : Action m a) (DAMA : Distr_Action m a) (a1 a2 : a) (m1 m2 : m).
  
  Definition sdp_one := SDP a m one one.
  
  Definition sdp_app := fun X Y =>
    match X, Y with
    |(SDP _ _ a1 m1),(SDP _ _ a2 m2) => (SDP a m (a1 ♢ (m1 • a2)) (m1 ♢ m2))
    end.

Ltac crush :=
  repeat match goal with
         | [ H : ?T |- ?T ] => exact H
         | [ |- ?T = ?T ] => reflexivity
         | [H : sdp _ _ |- _] => destruct H
         | [ |- context[sdp_one]] => unfold sdp_one
         | [ |- context[sdp_app]] => unfold sdp_app
         | [ |- context[_•_]] => try (rewrite act_id); try (rewrite act_comp); try (rewrite d_act_annih); try (rewrite d_act_dist)
         | [ |- context[_♢_]] => try (rewrite left_identity); try (rewrite right_identity); try (rewrite associativity)          
         end.

(** We need to prove that Semidirect Product of a and m is indeed a monoid. *)
Instance Semidirect_Product : Monoid (sdp a m).
Proof.
  split with sdp_one sdp_app; intros.
  crush.
  crush.
  crush.
  rewrite associativity.
  rewrite associativity.
  crush.
Qed.

End SDP.

(** Monoids can also act on functors as shown *)
Class ActionF (m a : Type) (f:Type -> Type) `{Monoid m} `{Monoid a} `{Functor f} :=
  {
    actf : m -> f a -> f a;

    actf_id : forall {e : f a}, actf one e = e;
    actf_comp : forall {m1 m2 : m} {e : f a}, actf (m1 ♢ m2) e = (actf m1 (actf m2 e));
    uniformity : forall {g : a -> a} {u : f a} {m1 : m}, actf m1 (fmap g u) = fmap g (actf m1 u)
  }.

Notation " m ⊙ fa " := (actf m fa) (at level 40, left associativity).

(*
Check Type.
Check unit.
Print  unit.
Check mf_unit.

Class Distr_ActionMF (m : Type) (f:Type -> Type) `{ActionF m Type f} `{Monoidal_Functor f} :=
  {
    d_actf_annih : forall {m1 : m}, (m1 ⊙ mf_unit) = mf_unit
  }.
    

Class Distr_ActionAPF m a f `{ActionF m a f} `{Monoidal_Functor f} :=
  {
    stoicism : forall {m1 : m} {a1 : a}, m1 ⊙ pure a1 = pure a1;
    effectiveness : forall {m1 : m} {a1 : f a} {g : f (a -> a)}, m1 ⊙ (g <*> a1) = (m1 ⊙ g) <*> (m1 ⊙ a1) 
  }.
*)