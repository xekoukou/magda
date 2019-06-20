module Magda2 where


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
open import Prelude.Maybe
open import Prelude.Monad
open import Prelude.Functor
open import Prelude.Sum renaming (Either to _∪_ ; left to _←∪ ; right to ∪→_ ; either to _∪ᶠ_)
open import Agda.Primitive


-- The container should not be inserted into any data type or record. IMPORTANT


private
  record Q {Ty : Set} {Ctx : Ty → Set} (ty : Ty) (ctx : Ctx ty) (A : Set) : Set where
    field
      value : A

  open Q

record WE (Q : {Ty : Set} {Ctx : Ty → Set} (ty : Ty) (ctx : Ctx ty) (A : Set) → Set) : Set₁ where
  field
    _⟨$⟩_ : ∀{Ty Ctx} → ∀{ty ctx A B} → (A → B) → Q {Ty} {Ctx} ty ctx A → Q {Ty} {Ctx} ty ctx B
    _⟨*⟩_ : {Ty : Set} {Ctx : Ty → Set}
            → ∀{ty1 ty2 ctx1 ctx2 A B}
            → Q {Ty} {Ctx} ty1 ctx1 (A → B) → Q {Ty} {Ctx} ty2 ctx2 A → Q {Ty} {Ctx} ty1 ctx1 B
    lift : ∀{Ty Ctx} → ∀{ty A} → ∀ ctx → A → Q {Ty} {Ctx} ty ctx A
    _⟩⟩=_ : {Ty : Set} {Ctx : Ty → Set}
            → ∀{ty1 ty2 ctx1 ctx2 A B}
            → Q {Ty} {Ctx} ty2 ctx2 A → (A → Q {Ty} {Ctx} ty1 ctx1 B) → Q {Ty} {Ctx} ty1 ctx1 B
    switch : {Ty1 : Set} {Ctx1 : Ty1 → Set} (Ty2 : Set) (Ctx2 : Ty2 → Set)
              → ∀{ty1 ty2 ctx1 ctx2 A} → Q {Ty1} {Ctx1} ty1 ctx1 A → Q {Ty2} {Ctx2} ty2 ctx2 A
    squash : {Ty1 : Set} {Ctx1 : Ty1 → Set} {Ty2 : Set} {Ctx2 : Ty2 → Set}
              → ∀{ty1 ty2 ctx1 ctx2 A} → Q {Ty1} {Ctx1} ty1 ctx1 (Q {Ty2} {Ctx2} ty2 ctx2 A) → Q {Ty2} {Ctx2} ty2 ctx2 A



open WE {{...}}

instance
  weQ : WE Q
  value (_⟨$⟩_ {{weQ}} f x) = f (value x)
  value (_⟨*⟩_ {{weQ}} f x) = value f (value x)
  value (lift {{weQ}} ctx a) = a
  _⟩⟩=_ {{weQ}} x f = f (value x)
  value (switch ⦃ weQ ⦄ Ty2 Ctx2 x) = value x
  squash ⦃ weQ ⦄ x = value x

private
-- This is used to split parallel results , especially when A and B live are in different contexts.
  record _×ₚ_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    field
      fst : A
      snd : B

  open _×ₚ_

-- We only allow the construction of such values, not the destruction.
_∥_ : ∀{a b} {A : Set a} {B : Set b} → A → B → A ×ₚ B
a ∥ b = record {fst = a ; snd = b}

-- Split destructs ×ₚ
split : ∀{Ty Ctx} → ∀{ty A B} → ∀ ctx → Q {Ty} {Ctx} ty ctx (A ×ₚ B)
        → Q {Ty} {Ctx} ty ctx A × Q {Ty} {Ctx} ty ctx B
split ctx x = record {value = fst (value x)} , record {value = snd (value x)}


record WTy : Set where

wTy : WTy
wTy = record {}

record World (wty : WTy) : Set where

world : World wTy
world = record {}


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


WQ : {Ty : Set} {Ctx : Ty → Set} (ty : Ty) (ctx : Ctx ty) (A : Set) → Set
WQ {Ty} {Ctx} ty ctx A
  = {{comSuc : ComSuc {Ty} {Ctx} }} → {{eqty : Eq Ty}} → {{eqctx : {ty : Ty} → Eq (Ctx ty)}}
    → Q {WTy} {World} wTy world (ComState {Ty} {Ctx}) → Q {Ty} {Ctx} ty ctx (Maybe A) × Q {WTy} {World} wTy world (ComState {Ty} {Ctx})


instance
  weWQ : WE WQ
  _⟨$⟩_ ⦃ weWQ ⦄ f x s = let r , s2 = x s
                          in (fmap f ⟨$⟩ r) , s2 
  lift ⦃ weWQ ⦄ ctx x s = lift ctx (just x) , s
  _⟨*⟩_ ⦃ weWQ ⦄ {_} {_} {ty1} {ty2} {ctx1} {ctx2} f x s = h2 where
    xs = x s
    h1 : Maybe _ → Maybe _ → Maybe _
    h1 (just f) (just x) = just (f x)
    h1 (just f) nothing = nothing
    h1 nothing x = nothing
-- The equality is computable by the owner of ctx1 , ctx2
-- or at compile time if there is no context.
    h2 = case ((ty1 , ctx1) == (ty2 , ctx2)) of
          λ { (yes refl) → let mf , s2 = f (snd xs)
          -- Only ctx1 performs any computation.
                        in ((h1 ⟨$⟩ mf) ⟨*⟩ (fst xs)) , s2
            ; (no _)  → let q = snd xs ⟩⟩= λ s1 →
                                  case (ctx2 isSuc s1) of
                                    λ { true →  let mf , s2 = f (lift world (inc s1 ctx2))
                                                in lift world (mf ∥ s2)
                                      ; false → let mf , s2 = f (lift world (inc s1 ctx2))
                                                in lift world (lift ctx1 nothing ∥ s2) }
                            mf , s2 = split world q
                        in ((h1 ⟨$⟩ squash mf) ⟨*⟩ fst xs) , squash s2}
  _⟩⟩=_ {{weWQ}} {_} {_} {ty1} {ty2} {ctx1} {ctx2} x f s = h3 where
    xs = x s
    h3 =  let q = case ((ty1 , ctx1) == (ty2 , ctx2)) of
                    λ { (yes refl) → fst xs ⟩⟩= λ a → case (fmap f a) of
                                                       λ { just x →  {!!}
                                                         ; nothing → {!!}}
                      ; (no _)  → {!!} }
          in {!!}
  switch {{weWQ}} = {!!}
  squash {{weWQ}} = {!!}
