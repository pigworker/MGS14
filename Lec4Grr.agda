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

data Found (F : U)(X : Set)(P : Holey F % X -> X -> Set) : F % X -> Set where
  found : (hf : Holey F % X)(x : X)(p : P hf x) -> Found F X P (plug F hf x)

lefty : forall F G {X} -> G % X -> Holey F % X -> Holey (F `* G) % X
lefty F G g hf = inl (hf , g)

righty : forall F G {X} -> F % X -> Holey G % X -> Holey (F `* G) % X
righty F G f hg = inr (f , hg)

seek : forall F {X}
       (P : Holey F % X -> X -> Set)
       (p? : (hf : Holey F % X)(x : X) -> P hf x + One)
       (f : F % X) -> Found F X P f + One
seek `X P p? x with p? <> x
seek `X P p? x | inl p = inl (found <> x p)
seek `X P p? x | inr <> = inr <>
seek `0 P p? f = inr <>
seek `1 P p? f = inr <>
seek (F `+ G) P p? (inl f) with seek F (P o inl) (p? o inl) f
seek (F `+ G) P p? (inl .(plug F hf x)) | inl (found hf x p)
  = inl (found (inl hf) x p)
seek (F `+ G) P p? (inl f) | inr <> = inr <>
seek (F `+ G) P p? (inr g) with seek G (P o inr) (p? o inr) g
seek (F `+ G) P p? (inr .(plug G hf x)) | inl (found hf x p)
  = inl (found (inr hf) x p)
seek (F `+ G) P p? (inr g) | inr <> = inr <>
seek (F `* G) P p? (f , g) with seek F (P o lefty F G g) (p? o lefty F G g) f
seek (F `* G) P p? (.(plug F hf x) , g) | inl (found hf x p)
  = inl (found (inl (hf , g)) x p)
seek (F `* G) P p? (f , g) | inr <> with seek G (P o righty F G f) (p? o righty F G f) g
seek (F `* G) P p? (f , .(plug G hf x)) | inr <> | inl (found hf x p)
  = inl (found (inr (f , hf)) x p)
seek (F `* G) P p? (f , g) | inr <> | inr <> = inr <>

data Zipper (F : U) : Set where
  root : Zipper F
  _<_ : Zipper F -> Holey F % Mu F -> Zipper F

_<<<_ : forall {F} -> Zipper F -> Mu F -> Mu F
root <<< x = x
_<<<_ {F} (fz < xh) x = fz <<< [ plug F xh x ]

data Where's {F}(wally : Mu F) : Mu F -> Set where
  somewhere : (there's : Zipper F) -> Where's wally (there's <<< wally)

whereIn : forall {F} x (z : Zipper F) y -> Where's x (z <<< y) + One
whereIn x z y with match x y
whereIn .y z y | equal = inl (somewhere z)
whereIn {F} x z [ f ] | apart with
  seek F (\ hf y -> Where's x (z <<< [ plug F hf y ])) (\ hf -> whereIn x (z < hf)) f
whereIn {F} x z [ .(plug F hf y) ] | apart | inl (found hf y p) = inl p
whereIn x z [ f ] | apart | inr <> = inr <>


where's : forall {F}(x y : Mu F) -> Where's x y + One
where's x y = whereIn x root y
