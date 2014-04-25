module Lec4 where

open import Basics

_+N_ : Nat -> Nat -> Nat
ze   +N y  = y
su x +N y  = su (x +N y)

data Cmp : Nat -> Nat -> Set where
  lt : forall {x} y  -> Cmp x (x +N su y)
  eq : forall {x}    -> Cmp x           x
  gt : forall {x} y  -> Cmp (x +N su y) x

cmp : forall x y -> Cmp x y
cmp x y = {!!}

{-
suInj : {x y : Nat} -> su x == su y -> x == y
suInj refl = refl
-}

data Plus (n : Nat) : Set where
  more : ((x y : Nat) -> n == su (x +N y) -> Plus y) -> Plus n

plusLemma : forall n x y -> n == su (x +N y) -> Plus y
plusLemma n x y = {!!}

plus : forall n -> Plus n
plus n = more (plusLemma n)

gcd : Nat -> Nat -> Nat
gcd x y = help x y (plus x) (plus y) where
  help : forall x y -> Plus x -> Plus y -> Nat
  help x y px py = {!!}



{-

data U : Set where
  `X `0 `1 : U
  _`+_ _`*_ : U -> U -> U

infixr 4 _`+_
infixr 5 _`*_

_%_ : forall U -> Set -> Set
`X       % X = X
`0       % X = Zero
`1       % X = One
(S `+ T) % X = S % X + T % X
(S `* T) % X = S % X * T % X

data Mu (F : U) : Set where
  [_] : F % Mu F -> Mu F

NAT = Mu (`1 `+ `X)

zero : NAT
zero = [ inl <> ]

suc : NAT -> NAT
suc n = [ inr n ]

data Match {X : Set}(x : X) : X -> Set where
  equal : Match x x
  apart : forall {y} -> Match x y  -- should really demand inequality

-- matchNode : forall G {F}(x y : G % Mu F) -> Match x y
match : forall {F}(x y : Mu F) -> Match x y
match {F} [ x ] [ y ] = {!!}

{-
Holey : U -> U
Holey F = {!!}

plug : forall F {X} -> Holey F % X -> X -> F % X
plug F hf x = {!!}





{-

data Context (F : U) : Set where
  here : Context F
  _>_ : Holey F % Mu F -> Context F -> Context F

_>>>_ : forall {F} -> Context F -> Mu F -> Mu F
here >>> x = x
_>>>_ {F} (xh > xc) x = [ plug F xh (xc >>> x) ]




data Found (G : U)(Y : Set)(P : Y -> Set) : G % Y -> Set where
  found : (hg : Holey G % Y)(y : Y)(p : P y) -> Found G Y P (plug G hg y)

data Where's_within_ {F}(wally : Mu F) : Mu F -> Set where
  somewhere : (there's : Context F) -> Where's wally within (there's >>> wally)

where's : forall {F} (x y : Mu F) -> Where's x within y + One
inner : forall {F} (x : Mu F)(f : F % Mu F) ->
  (Found F (Mu F) (\ y -> Where's x within y) f + One) ->
  Where's x within [ f ] + One
inward : forall {F} G (x : Mu F)(g : G % Mu F) ->
  Found G (Mu F) (\ y -> Where's x within y) g + One
where's x y = {!!}
inward G x g = {!!}
inner x f s = {!!}
-}-}-}