Require Import Coq.Program.Tactics.
Require Import Coq.Program.Basics.
Require Import Datatypes.

Open Scope program_scope. 

Class Monoid (A : Type) :=
  {
    empty : A ;
    append : A -> A -> A ;

    left_identity : forall x, append empty x = x ;
    right_identity : forall x, append x empty = x ;
    associativity : forall x y z, append x (append y z) = append (append x y) z
  }.

Notation " m1 ♢ m2 " := (append m1 m2)
  (at level 40, left associativity).


Class Commutative_Monoid (A : Type) (m : Monoid A) :=
  {
    commutativity : forall x y, x ♢ y = y ♢ x
  }.


Class Functor (f : Type -> Type) :=
  {
    fmap {a b : Type} : (a -> b) -> (f a) -> (f b);

    homomorphism {a b c : Type} : forall (p : b -> c) (q : a -> b), fmap (p ∘ q) = (fmap p) ∘ (fmap q)
  }.

Class Applicative_Functor (f : Type -> Type) (f1 : Functor f) :=
  {
    pure {a : Type} : a -> f a;
    app_star {a b : Type}: f (a -> b) -> f a -> f b;

    identity : forall v, app_star (pure id) v = v;
    composition : forall u v w, app_star (app_star (app_star (pure compose) u) v) w = app_star u (app_star v w); 
    homomorphism : forall f x, app_star (pure f) (pure x) = pure (f x)
  }.

Notation " fab <*> fa " := (app_star fab fa) (at level 40, left associativity).