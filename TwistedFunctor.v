Require Import Coq.Program.Tactics.
Require Import Coq.Program.Basics.
Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.Arith.
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


Instance Mnat : Monoid nat.
Proof.
  split with 0 plus; intros; auto with arith.
Defined.

Notation " m1 ♢ m2 " := (append m1 m2)
  (at level 40, left associativity).


Class Commutative_Monoid a `{Monoid a} :=
  {    
    commutativity : forall x y, x ♢ y = y ♢ x
  }.

Print  Commutative_Monoid.

Class Functor (f : Type -> Type) :=
  {
    fmap {a b : Type} : (a -> b) -> (f a) -> (f b);

    ftor_homomorphism {a b c : Type} : forall (p : b -> c) (q : a -> b), fmap (p ∘ q) = (fmap p) ∘ (fmap q)
  }.


Class Applicative_Functor f `{Functor (f : Type -> Type)} :=
  {
    pure {a : Type} : a -> f a;
    app_star {a b : Type} : f (a -> b) -> f a -> f b;

    appftor_identity : forall {a : Type} (v : f a) , app_star (pure id) v = v;
    appftor_composition : forall {a b c : Type} (u : f (b -> c)) (v : f (a -> b)) (w : f a), app_star (app_star (app_star (pure compose) u) v) w = app_star u (app_star v w); 
    appftor_homomorphism : forall {a b: Type} (f : a -> b) (x : a), app_star (pure f) (pure x) = pure (f x)
  }.

Notation " fab <*> fa " := (app_star fab fa) (at level 40, left associativity).


Definition isomorphic_l {x : Type} {f : Type -> Type} (X : f (unit * x)) (Y : f x) : Prop := True.
Definition isomorphic_r {x : Type} {f : Type -> Type} (X : f (x * unit)) (Y : f x) : Prop := True.
Definition isomorphic_ass {x y z : Type} {f : Type -> Type} (B : f (x * (y * z))) (A : f (x * y * z)) : Prop := True.

Class Monoidal_Functor f `{Functor (f : Type -> Type)} :=
  {
    mf_unit : f unit;
    mf_star {a b : Type} : f a -> f b -> f (a * b);

    mf_left_identity : forall {a : Type} {v : f a}, isomorphic_l (mf_star mf_unit v) v;
    mf_right_identity : forall {a : Type} {v : f a}, isomorphic_r (mf_star v mf_unit) v;
    mf_associativity : forall {a b c: Type} {x : f a} {y : f b} {z : f c}, isomorphic_ass (mf_star x (mf_star y z)) (mf_star (mf_star x y) z)
  }.

Notation " u ✶ v " := (mf_star u v) (at level 40, left associativity).



Class Action m a `{Monoid m}  :=
  {
    act : m -> a -> a;

    act_id : forall {e : a}, act one e = e;
    act_comp : forall {m1 m2 : m} {e : a}, act (m1 ♢ m2) e = (act m1 (act m2 e))
  }.


Notation "m • a" := (act m a) (at level 60, right associativity). 


Class Distr_Action m a `{Action m a} `{Monoid a}:=
  {
    d_act_annih : forall {m1 : m}, m1 • one = one;
    d_act_dist : forall {m1 : m} {a1 a2 : a},  m1 • (a1 ♢ a2) = (m1 • a1) ♢ (m1 • a2)
  }.

Inductive sdp (a b : Type) : Type :=
  | SDP : a -> b -> sdp a b.

Notation "a ⋊ b" := sdp (at level 40, left associativity). 
Notation "a ':⋊' b" := SDP (at level 40, left associativity). 

Check SDP.
Check sdp.


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


Class ActionF (m a : Type) (f:Type -> Type) `{Monoid m} `{Monoid a} `{Functor f} :=
  {
    actf : m -> f a -> f a;

    actf_id : forall {e : f a}, actf one e = e;
    actf_comp : forall {m1 m2 : m} {e : f a}, actf (m1 ♢ m2) e = (actf m1 (actf m2 e));
    uniformity : forall {g : a -> a} {u : f a} {m1 : m}, actf m1 (fmap g u) = fmap g (actf m1 u)
  }.

Notation " m ⊙ fa " := (actf m fa) (at level 40, left associativity).


Class Distr_ActionAPF m a f `{ActionF m a f} `{Applicative_Functor f} :=
  {
    stoicism : forall {m1 : m} {a1 : a}, m1 ⊙ pure a1 = pure a1;
    effectiveness : forall {m1 : m} {a1 : f a} {g : f (a -> a)}, m1 ⊙ (g <*> a1) = (m1 ⊙ g) <*> (m1 ⊙ a1) 
  }.