Require Import Coq.Program.Tactics.
Require Import Coq.Program.Basics.
Require Import Datatypes.

Open Scope program_scope. 

Class Monoid (A : Type) :=
  {
    one : A ;
    append : A -> A -> A ;

    left_identity : forall x, append one x = x ;
    right_identity : forall x, append x one = x ;
    associativity : forall x y z, append x (append y z) = append (append x y) z
  }.

Notation " m1 ♢ m2 " := (append m1 m2)
  (at level 40, left associativity).


Class Commutative_Monoid (A : Type) :=
  {
    underlying_monoid :> Monoid A;
    
    commutativity : forall x y, x ♢ y = y ♢ x
  }.

Print  Commutative_Monoid.

Class Functor (f : Type -> Type) :=
  {
    fmap {a b : Type} : (a -> b) -> (f a) -> (f b);

    ftor_homomorphism {a b c : Type} : forall (p : b -> c) (q : a -> b), fmap (p ∘ q) = (fmap p) ∘ (fmap q)
  }.

Check id.

Class Applicative_Functor (f : Type -> Type) :=
  {
    pure {a : Type} : a -> f a;
    app_star {a b : Type} : f (a -> b) -> f a -> f b;

    appftor_identity : forall {a : Type} (v : f a) , app_star (pure id) v = v;
    appftor_composition : forall {a b c : Type} (u : f (b -> c)) (v : f (a -> b)) (w : f a), app_star (app_star (app_star (pure compose) u) v) w = app_star u (app_star v w); 
    appftor_homomorphism : forall {a b: Type} (f : a -> b) (x : a), app_star (pure f) (pure x) = pure (f x)
  }.

Notation " fab <*> fa " := (app_star fab fa) (at level 40, left associativity).

