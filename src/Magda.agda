module Magda where

--We need to model the agents that interact with the software.
-- , the world.
-- Each agent has specific material properties that make him better suited in specific computations
-- and specific material jobs. Thus agents need to have as type , a specific role of a system.

-- Roles have meaning inside specific organizational structures. or in other words the type of work performed and
-- the type of computation determines the roles that are needed, in a way that not one role can be taken apart and analyzed independently.

-- We model an organization as a function that takes agents as input and data and returns agents and data. Both types of data can represent information
-- about material work done by the agents.

-- In essence, we can not and do not model the material changes that happened to the world due to the work of the agents. Our representation of the organization,
-- this computable function needs to be aware of this work but be agnostic, do not know the exact content.

-- The world contains objects and actuators /sensors on objects. The state of the objects or the effect of the actuators can not be determined exactly, we need to postulate
-- the state and the actuators.


open import Prelude.Nat
open import Prelude.Equality
open import Prelude.Product
open import Prelude.Unit
open import Prelude.Show
open import Prelude.Bool
open import Prelude.String
open import Prelude.Semiring
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Function
import Prelude.Maybe as M


record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream public
  
record ComSuc {Ty : Set} {Ctx : Ty → Set} : Set where
  field
    cS : ∀(ty : Ty) → (ctx : Ctx ty) → Stream Bool
  
open ComSuc {{...}} public

private
  ComState : ∀{Ty : Set} → ∀{Ctx : Ty → Set} → Set
  ComState {Ty} {Ctx} = (ty : Ty) → (ctx : Ctx ty) → Nat

  inc : ∀{Ty : Set} → ∀{Ctx : Ty → Set} → ComState {Ty} {Ctx} → {ty : Ty} → (ctx : Ctx ty)
        → {{eqty : Eq Ty}} → {{eqctx : {ty : Ty} → Eq (Ctx ty)}} → ComState {Ty} {Ctx}
  inc {_} {_} prv {ty1} ctx1 ty2 ctx2
    = case (ty1 , ctx1) == (ty2 , ctx2) of
       λ { (yes _) → suc (prv ty2 ctx2)
          ; (no _) → prv ty2 ctx2}
  
  _isSuc_ : ∀{Ty : Set} → ∀{Ctx : Ty → Set} → ∀{ty} → Ctx ty → ComState {Ty} {Ctx}
            → {{comSuc : ComSuc {Ty} {Ctx}}} → Bool
  _isSuc_ {_} {_} {ty} ctx s {{cmS}} = h1 (s ty ctx) (cS ty ctx) where
    h1 : Nat → Stream Bool → Bool
    h1 zero str = head str
    h1 (suc x) str = h1 x (tail str)

SF : {Ty : Set} (Ctx : Ty → Set) (ty : Ty) (ctx : Ctx ty) (F : (ty : Ty) → Ctx ty → Set → Set) (A : Set) → Set
SF {Ty} Ctx ty ctx F A = ComState {Ty} {Ctx} → F ty ctx A × ComState {Ty} {Ctx}


-- The pure function is executed under the same context as
-- its input.
record Functor {Ty : Set} {Ctx : Ty → Set} (F : (ty : Ty) → Ctx ty → Set → Set) : Set₁ where
  field
    _<$>_ : ∀{ty ctx A B} → (A → B) → SF Ctx ty ctx F A → SF Ctx ty ctx F B

open Functor {{...}} public


record Applicative {Ty : Set} {Ctx : Ty → Set} (F : (ty : Ty) → Ctx ty → Set → Set) : Set₁ where
  field
    pure  : ∀{ty A} → ∀ ctx → A → (ComState {Ty} {Ctx} → F ty ctx A × ComState {Ty} {Ctx})
    _<*>_ : ∀{ty1 ty2 ctx1 ctx2 A B}
            → {{comSuc : ComSuc {Ty} {Ctx} }} → {{eqty : Eq Ty}} → {{eqctx : {ty : Ty} → Eq (Ctx ty)}}
            → SF Ctx ty1 ctx1 F (A → B) → SF Ctx ty2 ctx2 F A → SF Ctx ty1 ctx1 F B
    overlap {{super}} : Functor F

open Applicative {{...}} public

record Monad {Ty : Set} {Ctx : Ty → Set} (F : (ty : Ty) → Ctx ty → Set → Set) : Set₁ where
  coinductive
  field
    _>>=_ : ∀{ty1 ty2 ctx1 ctx2 A B}
            → {{comSuc : ComSuc {Ty} {Ctx} }} → {{eqty : Eq Ty}} → {{eqctx : {ty : Ty} → Eq (Ctx ty)}}
            → SF Ctx ty2 ctx2 F A → (A →  SF Ctx ty1 ctx1 F B) → SF Ctx ty1 ctx1 F B
    overlap {{super}} : Applicative F

  _<<=_ : ∀{ty1 ty2 ctx1 ctx2 A B}
          → {{comSuc : ComSuc {Ty} {Ctx} }} → {{eqty : Eq Ty}} → {{eqctx : {ty : Ty} → Eq (Ctx ty)}}
          → (A →  SF Ctx ty1 ctx1 F B) → SF Ctx ty2 ctx2 F A → SF Ctx ty1 ctx1 F B
  _<<=_ {ty1} {_} {ctx1} f x = _>>=_ x f

open Monad {{...}} public
  
  
private

  data Maybe {Ty : Set} (Ctx : Ty → Set) (ty : Ty) (ctx : Ctx ty) (A : Set) : Set where
    just    : A → Maybe Ctx ty ctx A
    nothing : Maybe Ctx ty ctx A

SMaybe : {Ty : Set} (Ctx : Ty → Set) (ty : Ty) (ctx : Ctx ty) (A : Set) → Set
SMaybe {Ty} Ctx ty ctx A = {{comSuc : ComSuc {Ty} {Ctx} }} → SF Ctx ty ctx (Maybe Ctx) A

instance
  functorMaybe : ∀{Ty Ctx} → Functor {Ty} (Maybe Ctx)
  _<$>_ {{functorMaybe}} {ty} {ctx} f x s = first h1 (x s) where
    h1 : Maybe _ _ _ _ → Maybe _ _ _ _ 
    h1 (just x) = just (f x)
    h1 nothing = nothing


  applMaybe : ∀{Ty Ctx} → Applicative {Ty} (Maybe Ctx)
  pure ⦃ applMaybe ⦄ ctx x s = just x , s
  _<*>_ ⦃ applMaybe ⦄ {ty1} {ty2} {ctx1} {ctx2} f x s
    = h2 where
    xs = x s
    h1 : Maybe _ _ _ _ → Maybe _ _ _ _  → Maybe _ _ _ _
    h1 (just f) (just x) = just (f x)
    h1 (just f) nothing = nothing
    h1 nothing x = nothing
    h2 = case ((ty1 , ctx1) == (ty2 , ctx2)) of
          λ { (yes _) → let mf , s2 = f (snd xs)
                        in h1 mf (fst xs) , s2
            ; (no _)  → case (ctx2 isSuc (snd xs)) of
                         λ { true → let mf , s2 = f (inc (snd xs) ctx2)
                                     in h1 mf (fst xs) , s2
                           ; false  → let mf , s2 = f (inc (snd xs) ctx2)
                                      in nothing , s2} }
    
  super {{applMaybe}} = functorMaybe


  monadMaybe : ∀{Ty Ctx} → Monad {Ty} (Maybe Ctx)
  _>>=_ ⦃ monadMaybe {Ty} {Ctx} ⦄ {ty1} {ty2} {ctx1} {ctx2} x f s = h3 where
    xs = x s
    h1 : Maybe Ctx ty2 ctx2 _ × ComState {Ty} {Ctx} → (_ → (ComState {Ty} {Ctx} → Maybe Ctx ty1 ctx1 _ × ComState {Ty} {Ctx})) → Maybe Ctx ty1 ctx1 _ × ComState {Ty} {Ctx}
    h1 (just x , s1) f = f x s1
    h1 (nothing , s1) f = nothing , s1 
    h2 : Bool → Maybe Ctx ty2 ctx2 _ × ComState {Ty} {Ctx} → (_ → (ComState {Ty} {Ctx} → Maybe Ctx ty1 ctx1 _ × ComState {Ty} {Ctx})) → Maybe Ctx ty1 ctx1 _ × ComState {Ty} {Ctx}
    h2 true (just x , s1) f = f x (inc s1 ctx2)
    h2 false (just x , s1) f = nothing , inc s1 ctx2
    h2 b (nothing , s1) f = nothing , inc s1 ctx2 
    h3 = case ((ty1 , ctx1) == (ty2 , ctx2)) of
          λ { (yes _) → h1 xs f
            ; (no _)  → h2 (ctx2 isSuc (snd xs)) xs f }
     
  super {{monadMaybe}} = applMaybe


-- Using this in computation is insecure. Just don't. Only use it with proofs about the computation.
_toM : ∀{Ty Ctx} → ∀{ty ctx A} → Maybe {Ty} Ctx ty ctx A → M.Maybe A
_toM (just x) = M.just x
_toM nothing = M.nothing

_>>=M_ : ∀{Ty Ctx} → ∀{ty1 ty2 ctx1 ctx2 A B}
         → {{comSuc : ComSuc {Ty} {Ctx} }} → {{eqty : Eq Ty}} → {{eqctx : {ty : Ty} → Eq (Ctx ty)}}
         → SF Ctx ty2 ctx2 (Maybe Ctx) A → (M.Maybe A →  SF Ctx ty1 ctx1 (Maybe Ctx) B)
         → SF Ctx ty1 ctx1 (Maybe Ctx) B
_>>=M_ {Ty} {Ctx} {ty1} {ty2} {ctx1} {ctx2} {A} {B} x f s = h3 where
  xs = x s
  h1 : Maybe Ctx ty2 ctx2 _ × ComState {Ty} {Ctx} → (_ → (ComState {Ty} {Ctx} → Maybe Ctx ty1 ctx1 _ × ComState {Ty} {Ctx})) → Maybe Ctx ty1 ctx1 _ × ComState {Ty} {Ctx}
  h1 (x , s1) f = f (x toM) s1
  h2 : Bool → Maybe Ctx ty2 ctx2 _ × ComState {Ty} {Ctx} → (_ → (ComState {Ty} {Ctx} → Maybe Ctx ty1 ctx1 _ × ComState {Ty} {Ctx})) → Maybe Ctx ty1 ctx1 _ × ComState {Ty} {Ctx}
  h2 true (just x , s1) f = f (M.just x) (inc s1 ctx2)
  h2 false (just x , s1) f = f M.nothing (inc s1 ctx2)
  h2 b (nothing , s1) f = f M.nothing (inc s1 ctx2)
  h3 = case ((ty1 , ctx1) == (ty2 , ctx2)) of
        λ { (yes _) → h1 xs f
          ; (no _)  → h2 (ctx2 isSuc (snd xs)) xs f }


init : ∀{Ty : Set} → ∀{Ctx : Ty → Set} → ComState {Ty} {Ctx}
init ty ctx = zero


bun : {Ty : Set} {Ctx : Ty → Set} {ty : Ty} {ctx : Ctx ty} {A : Set}
      → Stream (SMaybe {Ty} Ctx ty ctx A) → {{comSuc : ComSuc {Ty} {Ctx} }}
      → ComState {Ty} {Ctx} → Stream (M.Maybe A)
head (bun str s) = (fst (head str s)) toM
tail (bun str s) = bun (tail str) (snd (head str s))

sun : {Ty : Set} {Ctx : Ty → Set} {ty : Ty} {ctx : Ctx ty} {A : Set}
      → {{eqty : Eq Ty}} → {{eqctx : {ty : Ty} → Eq (Ctx ty)}}
      → Stream (SMaybe {Ty} Ctx ty ctx A)
      → {{comSuc : ComSuc {Ty} {Ctx} }} → ComState {Ty} {Ctx} → Maybe {Ty} Ctx ty ctx (Stream (M.Maybe A))
sun x s = just (bun x s)

-- Unknown here represents the environment, unknown data dependencies between the environment.
postulate
  Unknown : Set
  unknown : Unknown

-- This has the same value each time they are called. Only the first time is there any IO happenning.
postulate
  ⟵_     : ∀{Ty} → {ty : Ty} → ∀{Ctx} → {A : Set} → ∀ ctx → Unknown → Maybe Ctx ty ctx A
  ⟵_<_>  : ∀{Ty} → {ty : Ty} → ∀{Ctx} → ∀ ctx → (A : Set) → Unknown → Maybe Ctx ty ctx A
  <_>_⟶_ : ∀{Ty} → {ty : Ty} → ∀{Ctx} → (A : Set) → A → ∀ ctx → Maybe Ctx ty ctx Unknown
  _⟶_    : ∀{Ty} → {ty : Ty} → ∀{Ctx} → {A : Set} → A → ∀ ctx → Maybe Ctx ty ctx Unknown

infix 30 ⟵_ 
infix 30 <_>_⟶_ 
infix 30 _⟶_ 
