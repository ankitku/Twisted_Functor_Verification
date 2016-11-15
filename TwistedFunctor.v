Require Import Coq.Program.Tactics.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Datatypes.
Require Import Datatypes.

Open Scope program_scope. 
Open Scope core_scope. 
Open Scope type_scope. 

Class Monoid (a : Type) :=
  {
    one : a;
    append : a -> a -> a;

    left_identity : forall x, append one x = x ;
    right_identity : forall x, append x one = x ;
    associativity : forall x y z, append x (append y z) = append (append x y) z
  }.


Notation " m1 ♢ m2 " := (append m1 m2)
  (at level 40, left associativity).


Class Commutative_Monoid a `{Monoid (a : Type)} :=
  {    
    commutativity : forall x y, x ♢ y = y ♢ x
  }.

Print  Commutative_Monoid.

Class Functor (f : Type -> Type) :=
  {
    fmap {a b : Type} : (a -> b) -> (f a) -> (f b);

    ftor_homomorphism {a b c : Type} : forall (p : b -> c) (q : a -> b), fmap (p ∘ q) = (fmap p) ∘ (fmap q)
  }.

Check id.

Class Applicative_Functor f `{Functor (f : Type -> Type)} :=
  {
    pure {a : Type} : a -> f a;
    app_star {a b : Type} : f (a -> b) -> f a -> f b;

    appftor_identity : forall {a : Type} (v : f a) , app_star (pure id) v = v;
    appftor_composition : forall {a b c : Type} (u : f (b -> c)) (v : f (a -> b)) (w : f a), app_star (app_star (app_star (pure compose) u) v) w = app_star u (app_star v w); 
    appftor_homomorphism : forall {a b: Type} (f : a -> b) (x : a), app_star (pure f) (pure x) = pure (f x)
  }.

Notation " fab <*> fa " := (app_star fab fa) (at level 40, left associativity).

(*
Class Monoidal_Functor (f : Type -> Type) :=
  {
    mf_unit : f unit;
    mf_star {a b : Type} : f a -> f b -> f (a * b);

    mf_left_identity : forall {a : Type} {v : f a}, (unit * a) = a -> mf_star mf_unit v = v ;
    mf_right_identity : forall v, mf_star v mf_unit = v ;
    mf_associativity : forall x y z, mf_star x (appmf_star y z) = mf_star (mf_star x y) z
  }.

✶
 *)

Class Action m (a : Type) `{Monoid (m : Type)}  :=
  {
    act : m -> a -> a;

    act_id : forall {e : a}, act one e = e;
    act_comp : forall {m1 m2 : m} {e : a}, act (m1 ♢ m2) e = (act m1 (act m2 e))
  }.

Notation "m • a" := (act m a) (at level 40, left associativity). 


Class Distr_Action m a `{Action (m a : Type)} :=
  {
    d_act_annih : m • one = one
  }.

