module Lec3 where

open import Basics

-- two topics in this lecture
-- (1) ordering invariants
-- (2) datatype generic programming

K : Set                                      -- the set of keys
K = Nat
_<K=_ : K -> K -> Set                        -- ordering for keys
ze <K= y = One
su x <K= ze = Zero
su x <K= su y = x <K= y
total : (j k : K) -> (j <K= k) + (k <K= j)   -- totality of <K=
total ze y = inl <>
total (su x) ze = inr <>
total (su x) (su y) = total x y

-- how to describe the node structure of simple datatypes containing keys

data U : Set where
  `Rec `1 : U
  _`+_ _`*K*_ : U -> U -> U
infixr 3 _`+_
infixr 4 _`*K*_

-- if we know what can go in recursive positions, we can say what is the
-- set of nodes with a given structure

infixr 6 _%_
_%_ : U -> Set -> Set
`Rec % Rec = Rec
`1 % Rec = One
(S `+ T) % Rec = S % Rec + T % Rec
(S `*K* T) % Rec = S % Rec * K * T % Rec

-- tying the knot

data Mu (T : U) : Set where
  [_] : T % Mu T -> Mu T

-- examples

LIST : U
LIST = `1 `+ `1 `*K* `Rec

-- nil : Mu LIST
pattern nil = [ inl <> ]

-- _::_ : K -> Mu LIST -> Mu LIST
pattern _::_ k ks = [ inr (<> , k , ks) ]
infixr 4 _::_

TREE : U
TREE = `1 `+ `Rec `*K* `Rec

leaf : Mu TREE
leaf = [ inl <> ]

node : Mu TREE -> K -> Mu TREE -> Mu TREE
node l k r = [ inr (l , k , r) ]

-- a datatype-specific program

_++_ : Mu LIST -> Mu LIST -> Mu LIST
nil ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- a datatype-generic program

list : forall {R} -> Mu R -> Mu LIST
list {R} [ r ] = go R r where
  go : forall T -> T % Mu R -> Mu LIST
  go `Rec t = list t
  go `1 <> = nil
  go (S `+ T) (inl s) = go S s
  go (S `+ T) (inr t) = go T t
  go (S `*K* T) (s , k , t) = go S s ++ (k :: go T t)



-- to work with ordering invariants, first extend K with extrema

data K^ : Set where
  bot : K^
  key : K -> K^
  top : K^

-- correspondingly extend the ordering relation

infixr 9 _<=_
_<=_ : K^ -> K^ -> Set
bot <= _ = One
_ <= bot = Zero
key x <= key y = x <K= y
_ <= top = One
top <= _ = Zero

-- now let us define *locally* ordered *bounded* data, where
--   the lower bound is below the first element
--   the first element is below the second element
--   ...
--   the last element is below the upper bound

_%%_[_-_] : U -> (K^ -> K^ -> Set) -> K^ -> K^ -> Set
`Rec %% Rec [ l - u ] = Rec l u
`1 %% Rec [ l - u ] = l <= u
(S `+ T) %% Rec [ l - u ] = S %% Rec [ l - u ] + T %% Rec [ l - u ]
(S `*K* T) %% Rec [ l - u ]
  = Sg K \ k -> S %% Rec [ l - key k ] * T %% Rec [ key k - u ]

data OMu_[_-_] (T : U)(l u : K^) : Set where
  [_] : T %% (OMu_[_-_] T) [ l - u ] -> OMu T [ l - u ]

KEY : U
KEY = `1 `*K* `1

{- get me when you need me
! : {X : Set}{{x : X}} -> X
! {{x}} = x
-}

-- insertion for ordered lists

insertL : forall {l u} ->
  OMu KEY [ l - u ] -> OMu LIST [ l - u ] -> OMu LIST [ l - u ]
insertL [ k , lk , ku ] [ inl lu ] = [ inr (k , lk , [ inl ku ]) ]
insertL [ k , lk , ku ] [ inr (j , lj , ju) ] with total k j
insertL [ k , lk , ku ] [ inr (j , lj , ju) ] | inl kj
  = [ inr (k , lk , [ inr (j , kj , ju) ]) ]
insertL [ k , lk , ku ] [ inr (j , lj , ju) ] | inr jk
  = [ inr (j , lj , insertL [ k , jk , ku ] ju) ]

insertSort : Mu LIST -> OMu LIST [ bot - top ]
insertSort nil        = [ inl <> ]
insertSort (k :: ks)  = insertL [ k , <> , <> ] (insertSort ks)


-- enough abstraction: take K to be Nat

myList : Mu LIST
myList = 20 :: 1 :: 18 :: 4 :: 13 :: 6 :: 10 :: 15 :: 2 :: 17 ::
         3 :: 19 :: 7 :: 16 :: 8 :: 11 :: 14 :: 9 :: 12 :: 5 :: nil

-- insertion for search trees

insertT : forall {l u} ->
  OMu KEY [ l - u ] -> OMu TREE [ l - u ] -> OMu TREE [ l - u ]
insertT [ k , lk , ku ] [ inl lu ] = [ inr (k , [ inl lk ] , [ inl ku ]) ]
insertT [ k , lk , ku ] [ inr (j , lj , ju) ] with total k j
insertT [ k , lk , ku ] [ inr (j , lj , ju) ] | inl kj
  = [ inr (j , insertT [ k , lk , kj ] lj , ju) ]
insertT [ k , lk , ku ] [ inr (j , lj , ju) ] | inr jk
  = [ inr (j , lj , insertT [ k , jk , ku ] ju) ]

makeT : Mu LIST -> OMu TREE [ bot - top ]
makeT nil = [ inl <> ]
makeT (k :: ks) = insertT [ k , <> , <> ] (makeT ks)

-- flattening to *ordered* lists

flatten : forall {T l u} -> OMu T [ l - u ] -> OMu LIST [ l - u ]
flatOne : forall R T {l u} -> T %% (OMu_[_-_] R) [ l - u ] -> OMu LIST [ l - u ]
flatten {T} t = {!!}
flatOne R T t = {!!}

treeSort : Mu LIST -> OMu LIST [ bot - top ]
treeSort = flatten o makeT

