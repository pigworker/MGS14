module Lec1 where

-- this will probably involve numbers and vectors
-- remember to make addition for numbers +N so that
-- coproduct of sets can be +

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

_+N_ : Nat -> Nat -> Nat
ze +N y = y
su x +N y = su (x +N y)

-- apart from that, improvise

data Vect (X : Set) : Nat -> Set where
  [] : Vect X ze
  _,_ : {n : Nat} -> X -> Vect X n -> Vect X (su n)


vadd : {n : Nat} -> Vect Nat n -> Vect Nat n -> Vect Nat n
vadd [] [] = []
vadd {su n} (x , xs) (y , ys) = {!-l!}