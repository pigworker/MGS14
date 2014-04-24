module Lec3Crib where

open import Basics

{-
postulate  -- abstract for now, but could pick numbers, etc
  K : Set                 -- the set of keys
  _<K=_ : K -> K -> Set   -- ordering for keys
  total : (j k : K) -> (j <K= k) + (k <K= j)
-}

K : Set
K = Nat
_<K=_ : K -> K -> Set
ze <K= y = One
su x <K= ze = Zero
su x <K= su y = x <K= y
total : (j k : K) -> (j <K= k) + (k <K= j)
total ze k = inl <>
total (su x) ze = inr <>
total (su x) (su y) = total x y

data U : Set where
  `Rec `1 : U
  _`+_ _`*K*_ : U -> U -> U
infixr 3 _`+_
infixr 4 _`*K*_

infixr 6 _%_
_%_ : U -> Set -> Set
`Rec % Rec = Rec
`1 % Rec = One
-- `K % Rec = K
(S `+ T) % Rec = S % Rec + T % Rec
-- (S * T) % Rec = S % Rec * T % Rec
(S `*K* T) % Rec = S % Rec * K * T % Rec

data Mu (T : U) : Set where
  [_] : T % Mu T -> Mu T

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
  go `1 t = nil
  go (S `+ T) (inl s) = go S s
  go (S `+ T) (inr t) = go T t
  go (S `*K* T) (s , k , t) = go S s ++ (k :: go T t)



data K^ : Set where
  bot : K^
  key : K -> K^
  top : K^

infixr 9 _<=_
_<=_ : K^ -> K^ -> Set
bot   <= _     = One
_     <= bot   = Zero
key x <= key y = x <K= y
_     <= top   = One
top   <= _     = Zero

_%%_[_-_] : U -> (K^ -> K^ -> Set) -> K^ -> K^ -> Set
`Rec %% Rec [ l - u ] = Rec l u
`1 %% Rec [ l - u ] = l <= u
-- `K %% Rec [ l - u ] =   l <= key k  *  key k <= u 
(S `+ T) %% Rec [ l - u ] = S %% Rec [ l - u ] + T %% Rec [ l - u ]
(S `*K* T) %% Rec [ l - u ]
  = Sg K \ k -> S %% Rec [ l - key k ] * T %% Rec [ key k - u ]

data OMu_[_-_] (T : U)(l u : K^) : Set where
  [_] : T %% (OMu_[_-_] T) [ l - u ] -> OMu T [ l - u ]

KEY : U
KEY = `1 `*K* `1

! : {X : Set}{{x : X}} -> X
! {{x}} = x

insertL : forall {l u} ->
  OMu KEY [ l - u ] -> OMu LIST [ l - u ] -> OMu LIST [ l - u ]
insertL [ k , _ , _ ] [ inl _ ]
  = [ inr (k , ! , [ inl ! ]) ]
insertL [ k , _ , _ ] [ inr (j , _ , ju) ] with total k j
... | inl _ = [ inr (k , ! , [ inr (j , ! , ju) ]) ]
... | inr _ = [ inr (j , ! , insertL [ k , ! , ! ] ju) ]

insertSort : Mu LIST -> OMu LIST [ bot - top ]
insertSort nil = [ inl <> ]
insertSort (k :: ks) = insertL [ k , <> , <> ] (insertSort ks)

myList : Mu LIST
myList = 20 :: 1 :: 18 :: 4 :: 13 :: 6 :: 10 :: 15 :: 2 :: 17 ::
         3 :: 19 :: 7 :: 16 :: 8 :: 11 :: 14 :: 9 :: 12 :: 5 :: nil

insertT : forall {l u} ->
  OMu KEY [ l - u ] -> OMu TREE [ l - u ] -> OMu TREE [ l - u ]
insertT [ k , _ , _ ] [ inl _ ] = [ inr (k , [ inl ! ] , [ inl ! ]) ]
insertT [ k , lk , ku ] [ inr (j , lj , ju) ] with total k j
... | inl kj = [ (inr (j , insertT [ k , lk , kj ] lj , ju)) ]
... | inr jk = [ (inr (j , lj , insertT [ k , jk , ku ] ju)) ]

makeT : Mu LIST -> OMu TREE [ bot - top ]
makeT nil = [ inl <> ]
makeT (k :: ks) = insertT [ k , <> , <> ] (makeT ks)

splice : forall {l u} m ->
  OMu LIST [ l - key m ] -> OMu LIST [ key m - u ] -> OMu LIST [ l - u ]
splice m [ inl lm ] mu = [ inr (m , lm , mu) ]
splice m [ inr (k , lk , km) ] mu = [ inr (k , lk , splice m km mu) ]

flatten : forall {T l u} -> OMu T [ l - u ] -> OMu LIST [ l - u ]
flatOne : forall R T {l u} -> T %% (OMu_[_-_] R) [ l - u ] -> OMu LIST [ l - u ]
flatten {T} [ t ] = flatOne T T t 
flatOne R `Rec t = flatten t
flatOne R `1 t = [ inl t ]
flatOne R (S `+ T) (inl s) = flatOne R S s
flatOne R (S `+ T) (inr t) = flatOne R T t
flatOne R (S `*K* T) (k , lk , ku) = splice k (flatOne R S lk) (flatOne R T ku)

treeSort : Mu LIST -> OMu LIST [ bot - top ]
treeSort = flatten o makeT
