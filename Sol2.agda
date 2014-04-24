module Sol2 where

open import Basics
open import Lec2

------------------------------------------------------------------
-- normalization by evaluation for simply typed lambda calculus --
------------------------------------------------------------------

-- we may mutually define
data Nm (G : Ctx) : Ty -> Set      -- normal terms
data Ne (G : Ctx)(T : Ty) : Set    -- neutral terms
-- give the declarations, then fill in the constructors

data Nm G where
  lam : forall {S T} -> Nm (G / S) T -> Nm G (S >> T)
  [_] : Ne G iota -> Nm G iota

-- neutral terms are embedded only at base type, so the term
-- cannot be further eta-expanded

data Ne G T where
  var : T <: G -> Ne G T
  _$_ : forall {S} -> Ne G (S >> T) -> Nm G S -> Ne G T

-- the function in an application is always neutral, but
-- neutral terms have no lambda, so the term is beta-normal


{- 2.1 Extend renaming to normals and neutrals. -}

-- Computation sometimes moves terms under binders, which requires us to shift
-- their free variables. So we'll need this kit.

renameNm : forall {G D} -> Ren G D -> forall {T} -> Nm G T -> Nm D T
renameNe : forall {G D} -> Ren G D -> forall {T} -> Ne G T -> Ne D T
renameNm f (lam t)  = lam (renameNm (weak REN f) t)
renameNm f [ t ]    = [ renameNe f t ]
renameNe f (var x)  = var (f x)
renameNe f (g $ s)  = renameNe f g $ renameNm f s


{- 2.2 context extensions -}

-- a context extension is a forward sequence of types, notionally the
-- types of binders we move under, successively

data Ext : Set where
  [] : Ext
  _,_ : Ty -> Ext -> Ext
infixl 3 _<><_

-- implement the operation which extends a context and show that there
-- as a renaming from the shorter to the longer

_<><_ : Ctx -> Ext -> Ctx
G <>< []     = G
G <>< S , D  = G / S <>< D

sucFish : forall {G} X -> Ren G (G <>< X)
sucFish []       x = x
sucFish (S , X)  x = sucFish X (su x)
-- the clue is in the name


{- 2.3 A Kripke semantics -}

-- here, we need to model the ways in which a term can be used
-- there are many ways to achieve this objective, but this is my favourite

Model Go : Ctx -> Ty -> Set -- a mutual definition of two things sharing a type

Model G T -- everything can either
 = Go G T -- compute further
 + Ne G T -- or be rendered as a neutral term

Go G iota       -- base type values
  = Zero        -- have no way to compute further
Go G (S >> T)   -- function type values can compute...
  =   (X : Ext)          -- ...in any extension of their source context...
  ->  Model (G <>< X) S  -- ...taking a source value from that extended context...
  ->  Model (G <>< X) T  -- ...to a target value in that context

-- your turn: show that the model admits weakening

wModel : forall {G} T X -> Model G T -> Model (G <>< X) T
wModel iota      X        (inl ())
wModel (S >> T)  []       (inl f)   = inl f
wModel (S >> T)  (R , X)  (inl f)
  = wModel (S >> T) X (inl (\ Y -> f (R , Y)))
wModel T         X        (inr t)   = inr (renameNe (sucFish X) t)


{- 2.4 application (how to go) and quotation (how to stop) -}

-- define the following:
--   application for things in the model
_$$_ : forall {G S T} -> Model G (S >> T) -> Model G S -> Model G T
--   quotation from the model to normal forms
stop : forall {G T} -> Model G T -> Nm G T
-- hint: the fact that I've declared them together may be significant

inl f $$ s = f [] s
inr f $$ s = inr (f $ stop s)

stop {G} {iota}    (inl ())
stop {G} {iota}    (inr t)   = [ t ]
stop {G} {S >> T}  f
  = lam (stop (wModel (S >> T) (S , []) f $$ inr (var ze)))


{- 2.5 environments -}

-- Implement a suitable notion of environment, storing values in the model.
-- MEnv G D should store a Model D T for each T in G

MEnv : Ctx -> Ctx -> Set
MEnv G D  = forall {T} -> T <: G -> Model D T   -- or build a tuple

-- equip your notion of environment with projection

mget : forall {G D T} -> T <: G -> MEnv G D -> Model D T
mget x g = g x

-- equip your notion of environment with extension by one value
mpush : forall {G D S} -> MEnv G D -> Model D S -> MEnv (G / S) D
mpush g s ze      = s
mpush g s (su x)  = g x

-- equip your notion of environment with weakening

wMEnv : forall {G} {D} X -> MEnv G D -> MEnv G (D <>< X)
wMEnv X g = wModel _ X o g

-- construct the identity environment, modelling each free variable as itself

idMEnv : forall {G} -> MEnv G G
idMEnv = inr o var


{- 2.6 evaluation and normalization -}

-- show that each well typed term can be modelled wherever there is an
-- environment for its context

model : forall {G T} -> G |- T -> forall {D} -> MEnv G D -> Model D T
model (var x) g = mget x g
model (f $ s) g = model f g $$ model s g
model (lam t) g = inl \ X s -> model t (mpush (wMEnv X g) s)

-- put the pieces together and give a (one line) normalization function for open
-- terms

normal : forall {G T} -> G |- T -> Nm G T
normal t = stop (model t idMEnv)


{- 2.7 have fun computing; here's a start -}

myTerm : {T : Ty} -> [] |- (T >> T) >> (T >> T)
myTerm = lam (lam (var (su ze) $ (var (su ze) $ var ze)))

myTest : [] |- (iota >> iota) >> (iota >> iota)
myTest = myTerm $ (myTerm $ myTerm)
