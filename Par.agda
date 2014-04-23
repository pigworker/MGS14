module Par where

open import Basics

data Two : Set where tt ff : Two

data List (X : Set) : Set where
  [] : List X
  _,_ : X -> List X -> List X

data Ty : Set1 where
  `X : Ty
  _`+_ _`*_ _`->_ : Ty -> Ty -> Ty
  `K : Set -> Ty
infixr 4 _`+_
infixr 5 _`*_
infixr 3 _`->_

SET : Ty -> Set -> Set
SET `X X = X
SET (S `+ T) X = SET S X + SET T X
SET (S `* T) X = SET S X * SET T X
SET (S `-> T) X = SET S X -> SET T X
SET (`K A) X = A

REL : (T : Ty){X Y : Set}(R : X -> Y -> Set) -> SET T X -> SET T Y -> Set
REL `X R x y = R x y
REL (S `+ T) R (inl xs) (inl ys) = REL S R xs ys
REL (S `+ T) R (inl xs) (inr yt) = Zero
REL (S `+ T) R (inr xt) (inl ys) = Zero
REL (S `+ T) R (inr xt) (inr yt) = REL T R xt yt
REL (S `* T) R (xs , ys) (xt , yt) = REL S R xs xt * REL T R ys yt
REL (S `-> T){X}{Y} R f g = (xs : SET S X)(ys : SET S Y) ->
  REL S R xs ys -> REL T R (f xs) (g ys)
REL (`K A) R a a' = a == a'

GROUP : Ty
GROUP = (`X `* `X `-> `X) `* `X `* (`X `-> `X)

Graph : {S T : Set} -> (S -> T) -> S -> T -> Set
Graph f s t = (f s) == t

GroupHom : {A B : Set} -> SET GROUP A -> SET GROUP B -> (A -> B) -> Set
GroupHom {A}{B}(am , a1 , ai) (bm , b1 , bi) f =
  ((a a' : A) -> f (am (a , a')) == (bm (f a , f a'))) *
  (f a1 == b1) *
  ((a : A) -> f (ai a) == bi (f a))

postulate
  A B : Set
  f : A -> B
  AG : SET GROUP A
  BG : SET GROUP B

fact1 : GroupHom AG BG f -> REL GROUP (Graph f) AG BG
fact1 (fm , f1 , fi)
  =  (\ { (a , a') (.(f a) , .(f a')) (refl , refl) -> fm a a' })
  ,  f1
  ,  ((\ { a .(f a) refl -> fi a }))

fact1' : REL GROUP (Graph f) AG BG -> GroupHom AG BG f
fact1' (fm , f1 , fi)
  =  (\ a a' -> fm (a , a') (f a , f a') (refl , refl))
  ,  f1
  ,  (\ a -> fi a (f a) refl)

QUEUE : Ty
QUEUE = `X `* (`K Nat `* `X `-> `X) `* (`X `-> `X) `* (`X `-> `K Two)

slowQ : SET QUEUE (List Nat)
slowQ
  =  []
  ,  (\ {(n , ns) -> n , ns})
  ,  (\ { [] -> [] ; (n , ns) -> ns })
  ,  (\ { [] -> tt ; _ -> ff })

revApp : {X : Set} -> List X -> List X -> List X
revApp [] ys = ys
revApp (x , xs) ys = revApp xs (x , ys)

