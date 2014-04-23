module Lec2 where

open import Basics

-- Simply Typed Lambda Calculus and its evaluation semantics

data Ty : Set where
  iota : Ty
  _>>_ : Ty -> Ty -> Ty
infixr 5 _>>_

-- Val

data Ctx : Set where
  [] : Ctx
  _/_ : Ctx -> Ty -> Ctx
infixl 4 _/_

-- Env

infix 3 _<:_
data _<:_ (T : Ty) : Ctx -> Set where

-- get

infix 3 _!-_
data _!-_ (G : Ctx) : Ty -> Set where

-- eval


-- simultaneous renaming and substitution, simultaneously

record Kit (Im : Ctx -> Ty -> Set) : Set where
  constructor kit
  field
    foo : One  -- dummy field

replace : forall {Im} -> Kit Im ->
  {G D : Ctx} ->
  ({T : Ty} -> T <: G -> Im D T) ->
   {T : Ty} -> G !- T -> D !- T
replace k f t = {!!}

rename : {G D : Ctx} ->
  ({T : Ty} -> T <: G -> T <: D) ->
   {T : Ty} -> G !- T -> D !- T
rename = replace {\ D T -> T <: D}
  {!!}

subst : {G D : Ctx} ->
  ({T : Ty} -> T <: G -> D !- T) ->
   {T : Ty} -> G !- T -> D !- T
subst = replace {_!-_}
  {!!}

