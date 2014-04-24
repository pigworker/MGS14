module Lec3 where

open import Basics

-- two topics in this lecture
-- (1) ordering invariants
-- (2) datatype generic programming

postulate  -- abstract for now, but could pick numbers, etc
  K : Set                                      -- the set of keys
  _<K=_ : K -> K -> Set                        -- ordering for keys
  total : (j k : K) -> (j <K= k) + (k <K= j)   -- totality of <K=

-- how to describe the node structure of simple datatypes containing keys

data U : Set where
  `Rec `1 `K : U
  _`+_ _`*_ : U -> U -> U
infixr 3 _`+_
infixr 4 _`*_

-- if we know what can go in recursive positions, we can say what is the
-- set of nodes with a given structure

infixr 6 _%_
_%_ : U -> Set -> Set
T % Rec = Rec

-- tying the knot

data Mu (T : U) : Set where
  [_] : T % Mu T -> Mu T

-- examples

LIST : U
LIST = `1 `+ `K `* `Rec

nil : Mu LIST
nil = {!!}

_::_ : K -> Mu LIST -> Mu LIST
_::_ k ks = {!!}
infixr 4 _::_

TREE : U
TREE = `1 `+ `Rec `* `K `* `Rec

leaf : Mu TREE
leaf = {!!}

node : Mu TREE -> K -> Mu TREE -> Mu TREE
node l k r = {!!}

-- a datatype-specific program

_++_ : Mu LIST -> Mu LIST -> Mu LIST
xs ++ ys = {!!}

-- a datatype-generic program

list : forall {R} -> Mu R -> Mu LIST
list {R} [ r ] = go R r where
  go : forall T -> T % Mu R -> Mu LIST
  go T t = {!!}


{- uncomment to end of file

-- to work with ordering invariants, first extend K with extrema

data K^ : Set where
  bot : K^
  key : K -> K^
  top : K^

-- correspondingly extend the ordering relation

infixr 9 _<=_
_<=_ : K^ -> K^ -> Set
x <= y = {!!}

-- now let us define *locally* ordered *bounded* data, where
--   the lower bound is below the first element
--   the first element is below the second element
--   ...
--   the last element is below the upper bound

_%%_[_-_] : U -> (K^ -> K^ -> Set) -> K^ -> K^ -> Set
T %% Rec [ l - u ] = {!!}

postulate OMu_[_-_] : (T : U)(l u : K^) -> Set
{-
data OMu_[_-_] (T : U)(l u : K^) : Set where
  [_] : T %% (OMu_[_-_] T) [ l - u ] -> OMu T [ l - u ]
-}

KEY : U
KEY = {!!}

{- get me when you need me
! : {X : Set}{{x : X}} -> X
! {{x}} = x
-}

-- insertion for ordered lists

insertL : forall {l u} ->
  OMu KEY [ l - u ] -> OMu LIST [ l - u ] -> OMu LIST [ l - u ]
insertL k ks = {!!}

{-
insertSort : Mu LIST -> OMu LIST [ bot - top ]
insertSort nil        = [ inl <> ]
insertSort (k :: ks)  = insertL [ k , <> , <> ] (insertSort ks)
-}

-- enough abstraction: take K to be Nat

{-
myList : Mu LIST
myList = 20 :: 1 :: 18 :: 4 :: 13 :: 6 :: 10 :: 15 :: 2 :: 17 ::
         3 :: 19 :: 7 :: 16 :: 8 :: 11 :: 14 :: 9 :: 12 :: 5 :: nil
-}

-- insertion for search trees

insertT : forall {l u} ->
  OMu KEY [ l - u ] -> OMu TREE [ l - u ] -> OMu TREE [ l - u ]
insertT k t = {!!}

makeT : Mu LIST -> OMu TREE [ bot - top ]
makeT ks = {!!}

-- flattening to *ordered* lists

flatten : forall {T l u} -> OMu T [ l - u ] -> OMu LIST [ l - u ]
flatOne : forall R T {l u} -> T %% (OMu_[_-_] R) [ l - u ] -> OMu LIST [ l - u ]
flatten {T} t = {!!}
flatOne R T t = {!!}

treeSort : Mu LIST -> OMu LIST [ bot - top ]
treeSort = flatten o makeT

-}