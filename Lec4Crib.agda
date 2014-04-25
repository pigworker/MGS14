module Lec4Crib where

open import Basics

_+N_ : Nat -> Nat -> Nat
ze   +N y  = y
su x +N y  = su (x +N y)

data Cmp : Nat -> Nat -> Set where
  lt : forall {x} y  -> Cmp x (x +N su y)
  eq : forall {x}    -> Cmp x           x
  gt : forall {x} y  -> Cmp (x +N su y) x

cmp : forall x y -> Cmp x y
cmp ze                     ze = eq
cmp ze                 (su y) = lt y
cmp (su x)                 ze = gt x
cmp (su x)             (su y) with cmp x y
cmp (su x)  (su .(x +N su y)) | lt y = lt y
cmp (su .y)            (su y) | eq   = eq
cmp (su .(x +N su y))  (su x) | gt y = gt y

suInj : {x y : Nat} -> su x == su y -> x == y
suInj refl = refl

data Plus (n : Nat) : Set where
  more : ((x y : Nat) -> n == su (x +N y) -> Plus y) -> Plus n

plusLemma : forall n x y -> n == su (x +N y) -> Plus y
plusLemma ze x y ()
plusLemma (su n) ze .n refl = more (plusLemma n)
plusLemma (su n) (su x) y q = plusLemma n x y (suInj q)

plus : forall n -> Plus n
plus n = more (plusLemma n)

gcd : Nat -> Nat -> Nat
gcd x y = help x y (plus x) (plus y) where
  help : forall x y -> Plus x -> Plus y -> Nat
  help ze y                            px py
    = y
  help (su x) ze                       px py
    = su x
  help (su x) (su y)                   px py with cmp x y
  help (su x) (su .(x +N su y))        px (more f) | lt y
    = help (su x) (su y)               px (f x (su y) refl)
  help (su .x)           (su x)        px       py | eq
    = su x
  help (su .(x +N su y)) (su x)        (more f) py | gt y
    = help (su y) (su x)               (f x (su y) refl) py

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

matchNode : forall G {F}(x y : G % Mu F) -> Match x y
match : forall {F}(x y : Mu F) -> Match x y
match {F} [ x ] [ y ] with matchNode F x y
match [ .y ] [ y ] | equal = equal
match [ x ] [ y ] | apart = apart
matchNode `X x y = match x y
matchNode `0 () y
matchNode `1 x y = equal
matchNode (G `+ H) (inl x) (inl y) with matchNode G x y
matchNode (G `+ H) (inl .y) (inl y) | equal = equal
matchNode (G `+ H) (inl x) (inl y) | apart = apart
matchNode (G `+ H) (inl x) (inr y) = apart
matchNode (G `+ H) (inr x) (inl y) = apart
matchNode (G `+ H) (inr x) (inr y) with matchNode H x y
matchNode (G `+ H) (inr .y) (inr y) | equal = equal
matchNode (G `+ H) (inr x) (inr y) | apart = apart
matchNode (G `* H) (x , x') (y , y') with matchNode G x y | matchNode H x' y'
matchNode (G `* H) (.y , .y') (y , y') | equal | equal = equal
matchNode (G `* H) (.y , x') (y , y') | equal | apart = apart
matchNode (G `* H) (x , x') (y , y') | apart | m' = apart


Holey : U -> U
Holey `X = `1
Holey `0 = `0
Holey `1 = `0
Holey (F `+ G) = Holey F `+ Holey G
Holey (F `* G) = Holey F `* G `+ F `* Holey G

plug : forall F {X} -> Holey F % X -> X -> F % X
plug `X <> x = x
plug `0 () x
plug `1 () x
plug (F `+ G) (inl xh) x = inl (plug F xh x)
plug (F `+ G) (inr xh) x = inr (plug G xh x)
plug (F `* G) (inl (xh , g)) x = plug F xh x , g
plug (F `* G) (inr (f , xh)) x = f , plug G xh x

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
where's x y with match x y
where's .y y | equal = inl (somewhere here)
where's {F} x [ f ] | apart = inner x f (inward F x f)
inner {F} x .(plug F hg (there's >>> x)) (inl (found hg .(there's >>> x)
   (somewhere there's))) = inl (somewhere (hg > there's))
inner x f (inr <>) = inr <>
inward `X x g with where's x g
inward `X x g | inl s = inl (found <> g s)
inward `X x g | inr <> = inr <>
inward `0 x g = inr <>
inward `1 x g = inr <>
inward (G `+ H) x g = {!!}
inward (G `* H) x g = {!!}
