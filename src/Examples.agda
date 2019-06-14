module Examples where

open import Prelude.Equality
import Prelude.String using (EqString)
open import Agda.Builtin.String
open import Prelude.Decidable
open import Prelude.Empty
open import Prelude.Bool
open import Prelude.Nat
open import Prelude.Show
open import Prelude.Function
open import Prelude.Semiring
open import Prelude.Maybe
open import Prelude.Product
open import Prelude.Unit
open import Magda


data TyCtx : Set where
  Engineer : TyCtx
  Cook : TyCtx

instance
  eqTyCtx : Eq TyCtx
  _==_ ⦃ eqTyCtx ⦄ Engineer Engineer = yes refl
  _==_ ⦃ eqTyCtx ⦄ Engineer Cook = no λ {()}
  _==_ ⦃ eqTyCtx ⦄ Cook Engineer = no λ {()}
  _==_ ⦃ eqTyCtx ⦄ Cook Cook = yes refl

record Ctx (ty : TyCtx) : Set where
  field
    connection : Nat

open Ctx 

instance
  eqCtx : {ty : TyCtx} → Eq (Ctx ty)
  _==_ ⦃ eqCtx ⦄ record { connection = c1 } record { connection = c2} with c1 == c2
  (eqCtx == record { connection = c1 }) record { connection = .c1 } | yes refl = yes refl
  (eqCtx == record { connection = c1 }) record { connection = c2 } | no x = no λ { refl → x refl}



comSuc : Bool → ComSuc {TyCtx} {Ctx}
head (cS ⦃ comSuc b ⦄ Engineer y) = b
tail (cS ⦃ comSuc b ⦄ Engineer y) = cS {{comSuc b}} Engineer y
head (cS ⦃ comSuc b ⦄ Cook y) = true
tail (cS ⦃ comSuc b ⦄ Cook y) = cS {{comSuc b}} Cook y

gun : (bob : Ctx Engineer) → ∀ alice → SMaybe Ctx Cook alice Nat
gun bob alice = pure bob 3 >>= λ x → pure alice (x + 2)

gunn : (bob : Ctx Engineer) → ∀ alice → SMaybe Ctx Engineer bob Nat × SMaybe Ctx Cook alice Nat
gunn bob alice = let b = pure bob 3
                 in b , b >>= λ x → pure alice (x + 2)



fun : (bob : Ctx Engineer) → ∀ alice → (fst (gun bob alice {{comSuc false}} init)) toM ≡ nothing
fun bob alice = refl

sun : (bob : Ctx Engineer) → ∀ alice → (fst (gun bob alice {{comSuc true}} init)) toM ≡ just 5
sun bob alice = refl

gun2 : (bob : Ctx Engineer) → ∀ alice → SMaybe Ctx Cook alice Nat
gun2 bob alice = pure bob 3 >>=M λ { nothing → pure alice 2
                                   ; (just x) → pure alice (x + 2)}

fun2 : (bob : Ctx Engineer) → ∀ alice → (fst (gun2 bob alice {{comSuc false}} init)) toM ≡ just 2
fun2 bob alice = refl

sun2 : (bob : Ctx Engineer) → ∀ alice → (fst (gun2 bob alice {{comSuc true}} init)) toM ≡ just 5
sun2 bob alice = refl


--------------------------------------------------------

data Ty-SC : Set where
  Server : Ty-SC
  Client : Ty-SC


instance
  eqTy-SC : Eq Ty-SC
  _==_ ⦃ eqTy-SC ⦄ Server Server = yes refl
  _==_ ⦃ eqTy-SC ⦄ Server Client = no λ {()}
  _==_ ⦃ eqTy-SC ⦄ Client Server = no (λ {()})
  _==_ ⦃ eqTy-SC ⦄ Client Client = yes refl

IP : Set
IP = Nat × Nat × Nat × Nat

ConInfo : Ty-SC → Set
ConInfo Server = IP
ConInfo Client = Nat

record Ctx-SC (ty : Ty-SC) : Set where
  field
    conInfo : ConInfo ty 

instance
  EqCtx-SC : {ty : Ty-SC} → Eq (Ctx-SC ty)
  _==_ ⦃ EqCtx-SC {Server} ⦄ record { conInfo = c1 } record { conInfo = c2 } with c1 == c2
  (EqCtx-SC {Server} == record { conInfo = c1 }) record { conInfo = c2 } | yes refl = yes refl
  (EqCtx-SC {Server} == record { conInfo = c1 }) record { conInfo = c2 } | no x = no λ { refl → x refl}
  _==_ ⦃ EqCtx-SC {Client} ⦄ record { conInfo = c1 } record { conInfo = c2 } with c1 == c2
  (EqCtx-SC {Client} == record { conInfo = c1 }) record { conInfo = .c1 } | yes refl = yes refl
  (EqCtx-SC {Client} == record { conInfo = c1 }) record { conInfo = c2 } | no x = no λ { refl → x refl}

-- This assumes that the server will receive an infinite amount of clients from the environment.
postulate
  clients : ∀ srv → SMaybe Ctx-SC Server srv (Stream (Ctx-SC Client))
-- Unknown means that the client was changed.
-- We need more specific unknowns.
-- Keep in mind that is function can only be used once.
  printString : ∀ cl → String → SMaybe Ctx-SC Client cl Unknown


-- TODO IMPORTANT x can be used outside of context.
-- I need to use reflection to return an error.
act : (srv : Ctx-SC Server) → (cl : Ctx-SC Client) → Nat → SMaybe Ctx-SC Server srv Unknown
act srv cl n = pure cl "What is the counter value , mate?" >>=
             λ x → case (x == "What is the counter value , mate?") of
                    λ { (yes y) → pure srv n >>= λ n → printString cl (show n) >>= pure srv
                      ; (no y) → pure srv "What?" >>= λ s → printString cl s   >>= pure srv } 

foldr : ∀ srv → (n : Nat) → Stream (Ctx-SC Client) → Stream (SMaybe Ctx-SC Server srv Unknown)
head (foldr srv n str) = act srv (head str) n
tail (foldr srv n str) = foldr srv (suc n) (tail str)

echo : ∀ srv → SMaybe Ctx-SC Server srv Unknown
echo srv = clients srv >>= {!foldr !}


bun : ∀ srv → Stream (SMaybe Ctx-SC Server srv Unknown) → SMaybe Ctx-SC Server srv (Stream (Maybe Unknown))
bun srv str = {!!}
