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
open import Prelude.String
open import Prelude.Function
open import Prelude.Semiring


-- 
-- record CoMonad (F : Set → Set) : Set₁ where
--   field
--     extract : ∀{A} → F A → A
--     duplicate : ∀{A} → F A → F (F A)
--     _$_ : ∀{A B} → (F A → B) → F A → F B
--     
-- open CoMonad {{...}}

-- inc : ∀{Ty : Set} → {Ctx : Ty → Set} → {{_ : {ty : Ty} → Eq (Ctx ty)}} → ∀{ty} → Ctx ty → (∀ {ty} → Ctx ty → Nat) → (∀ {ty} → Ctx ty → Nat)
-- inc ctx S x with x == ctx
-- ... | r = {!!}

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

S : Set
S = Stream (Stream Nat)

emptyS : S
head (head emptyS) = 0
tail (head emptyS) = head emptyS
tail emptyS = emptyS

record EnumSet {Ty : Set} (Ctx : Ty → Set) : Set where
  field
    enum :  ∀{ty} → Ctx ty → Nat

open EnumSet {{...}}

-- The pure function is executed under the same context as
-- its input.                                                       initial ending s
record Functor {Ty : Set} {Ctx : Ty → Set} {{_ : EnumSet Ctx}} (F : S → S → (ty : Ty) → Ctx ty → Set → Set) : Set₁ where
  field
    _<$>_ : ∀{s1 s2 ty ctx A B} → (A → B) → F s1 s2 ty ctx A → F s1 s2 ty ctx B

open Functor {{...}}

record Applicative {Ty : Set} {Ctx : Ty → Set} {{_ : EnumSet Ctx}} (F : S → S → (ty : Ty) → Ctx ty → Set → Set) : Set₁ where
  field
    pure  : ∀{s ty ctx A} → A → F s s ty ctx A
    _<*>_ : ∀{s1e s2s s2e ty1 ty2 ctx1 ctx2 A B} → F s2e s1e ty1 ctx1 (A → B) → F s2s s2e ty2 ctx2 A → F s2s s1e ty1 ctx1 B
    overlap {{super}} : Functor F

open Applicative {{...}}

record Monad {Ty : Set} {Ctx : Ty → Set} {{_ : EnumSet Ctx}} (F : S → S → (ty : Ty) → Ctx ty → Set → Set) : Set₁ where
  coinductive
  field
    _>>=_ : ∀{s1e s2s s2e ty1 ty2 ctx1 ctx2 A B} → F s2s s2e ty2 ctx2 A → (A → F s2e s1e ty1 ctx1 B) → F s2s s1e ty1 ctx1 B
    overlap {{super}} : Applicative F

  _<<=_ : ∀{s1e s2s s2e ty1 ty2 ctx1 ctx2 A B} → (A → F s2e s1e ty1 ctx1 B) → F s2s s2e ty2 ctx2 A → F s2s s1e ty1 ctx1 B
  f <<= x = x >>= f

open Monad {{...}}


data Maybe {Ty : Set} (Ctx : Ty → Set) {{_ : EnumSet Ctx}} (s1 s2 : S) (ty : Ty) (ctx : Ctx ty) (A : Set) : Set where
  just    : A → Maybe Ctx s1 s2 ty ctx A
  nothing : Maybe Ctx s1 s2 ty ctx A


instance
  functorMaybe : ∀{Ty Ctx} → {{_ : EnumSet Ctx}} → Functor {Ty} (Maybe Ctx)
  _<$>_ {{functorMaybe}} f (just x) = just (f x)
  _<$>_ {{functorMaybe}} f nothing = nothing

  applMaybe : ∀{Ty Ctx} → {{_ : EnumSet Ctx}} → Applicative {Ty} (Maybe Ctx)
  pure ⦃ applMaybe ⦄ x = just x
  _<*>_ ⦃ applMaybe ⦄ (just f) (just x) = just (f x)
  _<*>_ ⦃ applMaybe ⦄ (just f) nothing = nothing
  _<*>_ ⦃ applMaybe ⦄ nothing x = nothing
  super {{applMaybe}} = functorMaybe

  monadMaybe : ∀{Ty Ctx} → {{_ : EnumSet Ctx}} → Monad {Ty} (Maybe Ctx)
  _>>=_ ⦃ monadMaybe ⦄ (just x) f = case f x of
                           λ { (just x) → just x
                             ; nothing  → nothing}
  _>>=_ ⦃ monadMaybe ⦄ nothing f = nothing
  super {{monadMaybe}} = applMaybe



-- postulate
--   ⟵_ : ∀{Ty ty Ctx A} → ∀ ctx → Maybe {Ty} Ctx ty ctx A
--   ⟵_<_> : ∀{Ty ty Ctx} → ∀ ctx → (A : Set) → Maybe {Ty} Ctx ty ctx A
--   <_>_⟶_ : ∀{Ty ty Ctx} → (A : Set) → A → ∀ ctx → Maybe {Ty} Ctx ty ctx Unit
--   _⟶_ : ∀{Ty ty Ctx} → {A : Set} → A → ∀ ctx → Maybe {Ty} Ctx ty ctx Unit

-- infix 30 ⟵_ 
-- infix 30 <_>_⟶_ 
-- infix 30 _⟶_ 

-- data TyCtx : Set where
--   Engineer : TyCtx
--   Cook : TyCtx
--   Boss : TyCtx
  

-- data Ctx : TyCtx → Set where
--   Bob : Ctx Engineer
--   Tonia : Ctx Cook
--   Alice : Ctx Cook
--   Alex : Ctx Boss


-- fun : Maybe Ctx Cook Alice Unit
-- fun = (< String > "Pick a number :" ⟶ Bob) >>=
--       λ _ → (((λ z → "Bob chose this number :"  & (show z)) <$> ⟵ Bob < Nat >) >>= _⟶ Alice) >>=
--       λ _ → < String > "Thank you" ⟶ Bob >>= λ _ → pure unit


-- tun : {ty : TyCtx} → ∀ ctx → Maybe Ctx ty ctx Unit
-- tun ctx = < String > "What kind of food do you want, boss?" ⟶ Alex >>=
--           {!!}

-- gun : Maybe Ctx Boss Alex Unit
-- gun = < String > "Alex, who should cook? Tonia or Alice?" ⟶ Alex >>=
--       λ _ → (λ { "Alice" → tun Alice >>= λ _ → pure unit
--                ; "Tonia" → tun Tonia >>= λ _ → pure unit
--                ; _       → nothing }) <<= ⟵ Alex
