module Lec2 (A : Set) where

open import Basics

-- Simply Typed Lambda Calculus and its evaluation semantics

data Ty : Set where
  iota : Ty
  _>>_ : Ty -> Ty -> Ty
infixr 5 _>>_

Val : Ty -> Set
Val iota = A
Val (S >> T) = Val S -> Val T

data Ctx : Set where
  [] : Ctx
  _/_ : Ctx -> Ty -> Ctx
infixl 4 _/_

Env : Ctx -> Set
Env [] = One
Env (G / S) = Env G * Val S

infix 3 _<:_
data _<:_ (T : Ty) : Ctx -> Set where
  ze : {G : Ctx} -> T <: G / T
  su : {G : Ctx}{S : Ty} ->  T <: G  ->  T <: G / S

goAway : forall {T} -> T <: [] -> Val T
goAway ()

get : forall {G T} -> T <: G -> Env G -> Val T
get ze (g , t) = t
get (su x) (g , s) = get x g

infix 3 _!-_
infixl 4 _$_
data _!-_ (G : Ctx) : Ty -> Set where

  var : forall {T}

        ->  T <: G
        -------------
        ->  G !- T

  _$_ : forall {S T}

        ->  G !- S >> T   ->  G !- S
        -------------------------------
        ->  G !- T

  lam : forall {S T}

        ->  G / S !- T
        ------------------
        ->  G !- S >> T

eval : forall {G T} -> G !- T -> Env G -> Val T
eval (var x) g = get x g
eval (f $ s) g = (eval f g) (eval s g)
eval (lam t) g = \ s -> eval t (g , s)


-- simultaneous renaming and substitution, simultaneously

record Kit (Im : Ctx -> Ty -> Set) : Set where
  constructor kit
  field
    kTm : forall {G T} -> Im G T -> G !- T
    kVa : forall {G T} -> T <: G -> Im G T
    kWk : forall {G T S} -> Im G T -> Im (G / S) T
open Kit

weak : forall {Im} -> Kit Im ->
  {G D : Ctx} ->
  ({T : Ty} -> T <: G -> Im D T) ->
  {S : Ty} ->
  ({T : Ty} -> T <: G / S -> Im (D / S) T)
weak k f ze = kVa k ze
weak k f (su x) = kWk k (f x)


replace : forall {Im} -> Kit Im ->
  {G D : Ctx} ->
  ({T : Ty} -> T <: G -> Im D T) ->
   {T : Ty} -> G !- T -> D !- T
replace k f (var x) = kTm k (f x)
replace k f (g $ s) = replace k f g $ replace k f s
replace k f (lam t) = lam (replace k (weak k f) t)
  

rename : {G D : Ctx} ->
  ({T : Ty} -> T <: G -> T <: D) ->
   {T : Ty} -> G !- T -> D !- T
rename = replace {\ D T -> T <: D}
  (kit var id su )

subst : {G D : Ctx} ->
  ({T : Ty} -> T <: G -> D !- T) ->
   {T : Ty} -> G !- T -> D !- T
subst = replace {_!-_}
  (kit id var (rename su))

