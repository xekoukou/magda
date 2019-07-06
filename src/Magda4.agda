module Magda4 where

open import Magda3

open import Agda.Builtin.Reflection
open import Tactic.Reflection.Equality
open import Tactic.Reflection

open import Prelude.Nat
open import Prelude.Ord
open import Prelude.Nat.Properties
open import Prelude.List
open import Prelude.Decidable
open import Prelude.Bool
open import Prelude.Semiring
open import Prelude.Equality
open import Prelude.Unit
open import Prelude.Show
open import Prelude.Product
open import Prelude.Maybe
open import Prelude.Function
open import Prelude.Monad
open import Prelude.String
open import Prelude.Sum


mapArg : {A : Set} → List (Arg A) → List A
mapArg [] = []
mapArg ((arg i x) ∷ xs) = x ∷ mapArg xs

mapClause : List Clause → List Term
mapClause [] = []
mapClause ((clause _ t) ∷ xs) = t ∷ mapClause xs
mapClause ((absurd-clause _) ∷ xs) = mapClause xs



-- We probably need to normalize all functions before typechecking.

{-# TERMINATING #-}
showT : Term → String
showDef : Definition → String

showT (var x args) = "var " & show x & " [ " & foldr (λ { (arg i x) y → "arg " & showT x & " , " & y}) "]" args
showT (con c args) = "con " & (primShowQName c) & " [ " & foldr (λ { (arg i x) y → "arg " & showT x & " , " & y}) "]" args
showT (def f args) = "def " & (primShowQName f) & " [ " & foldr (λ { (arg i x) y → "arg " & showT x & " , " & y}) "]" args
showT (lam v (abs s x)) = "lam " & s & " " & showT x
showT (pat-lam cs args) = "pat-lam"
showT (pi a b) = "pi"
showT (agda-sort s) = "agda-sort"
showT (lit l) = "lit"
showT (meta x x₁) = "meta"
showT unknown = "unknown"

showPatterns : List Pattern → String
showPattern : Pattern → String

showPatterns ps = " [ " & (foldr (λ x y → y & " , " & showPattern x) "" ps) & "]"

showPattern (con c ps) = "con " & primShowQName c & showPatterns (mapArg ps)
showPattern dot = "dot"
showPattern (var s) = "var " & s
showPattern (lit l) = "lit literal"
showPattern (proj f) = "proj " & primShowQName f
showPattern absurd = "absurd"

showClause : Clause → String
showClause (clause ps t) = "Cl " & showPatterns (mapArg ps) & " " & showT t
showClause (absurd-clause ps) = ""

showDef (function cs) = " [ " & (foldr _&_ " , " (map showClause cs)) & " ] "
showDef (data-type pars cs) = "data-type"
showDef (record-type c fs) = "record-type"
showDef (data-cons d) = "data-cons"
showDef axiom = "axiom"
showDef prim-fun = "prim-fun"



-- Update de buirjn indexes by adding +1 to them.
{-# TERMINATING #-}
updateTerm : Term → Term
updateTerm (var x args) = var (suc x) (map (λ { (arg i x) → arg i (updateTerm x)}) args)
updateTerm (con c args) = con c (map (λ { (arg i x) → arg i (updateTerm x)}) args)
updateTerm (def f args) = def f (map (λ { (arg i x) → arg i (updateTerm x)}) args)
updateTerm (lam v (abs s x)) = lam v (abs s (updateTerm x))
updateTerm (pat-lam cs args) = pat-lam cs (map (λ { (arg i x) → arg i (updateTerm x)}) args)
updateTerm (pi (arg i x) (abs s y)) = pi (arg i (updateTerm x)) (abs s (updateTerm y))
updateTerm (agda-sort (set t)) = agda-sort (set (updateTerm t))
updateTerm self@(agda-sort (lit n)) = self
updateTerm self@(agda-sort unknown) = self
updateTerm (lit l) = lit l
updateTerm (meta x args) = meta x (map (λ { (arg i x) → arg i (updateTerm x)}) args)
updateTerm unknown = unknown

updateContext : ∀{a} {A : Set a} → Visibility → Term → TC A → TC A
updateContext v t cn = bindTC (inferType t) λ ty → extendContext (arg (arg-info v relevant) ty) cn


ptmatched? : Clause → List Bool
ptmatched? (clause ps t) = map (λ { (arg i (con c ps)) → true
                                    ; (arg i dot) → true
                                    ; (arg i (var s)) → false
                                    ; (arg i (lit l)) → true
                                    ; (arg i (proj f)) → true
                                    ; (arg i absurd) → true}) ps
ptmatched? (absurd-clause ps) = map (λ _ → false) ps


ptmatchedL? : List Clause → List Bool
ptmatchedL? [] = []
ptmatchedL? (x ∷ xs) = foldr (λ x y → map (uncurry _&&_) (zip x y)) (ptmatched? x) (map ptmatched? xs)
                       


-- Is this correct ?
pmatched? : List Clause → Bool
pmatched? [] = false
pmatched? (clause ps t ∷ cls) = (foldr (λ { (arg i (con c ps)) y → true
                                          ; (arg i dot) y → true
                                          ; (arg i (var s)) y → y
                                          ; (arg i (lit l)) y → true
                                          ; (arg i (proj f)) y → true
                                          ; (arg i absurd) y → true}) false ps) || pmatched? cls
pmatched? (absurd-clause ps ∷ cls) = pmatched? cls


-- Finds the number of vars in a pattern.
{-# TERMINATING #-}
ddq : Pattern → Nat
ddq (con c ps) = foldr (λ x y → ddq x + y) 0 (mapArg ps)
ddq dot = zero
ddq (var s) = 1
ddq (lit l) = 0
ddq (proj f) = 0
ddq absurd = 0

-- Determines the width of the debruijn indexes. less than and more than and equal. [a , b )
ddw : Clause → List Nat
ddw (clause ps t) = let x = map ddq (mapArg ps)
                    in snd $ foldr (λ z y → let q = z + fst y in q , q ∷ snd y) (0 , []) (reverse x)
ddw (absurd-clause ps) = []

ddo : Clause → List (Nat × Maybe Term)
ddo cl = map (λ x → x , nothing) (ddw cl)

-- This might be unnecessary, since we will check this in place.
-- TODO return some information about the error.
ddv : List Nat → List (Nat × Term) → Maybe (List (Maybe Term))
ddv [] b = just []
ddv (x ∷ a) b = let s = foldr (λ z y → case (fst z <? x) of
                                        λ { false → fst y , z ∷ snd y
                                          ; true → snd z ∷ fst y , snd y}) ([] , []) b
                in case (h1 (fst s)) of
                     λ { false → nothing
                       ; true → case (ddv a (snd s)) of
                                 λ { nothing → nothing
                                   ; (just x) → case (fst s) of
                                                 λ { [] → just (nothing ∷ x)
                                                   ; (z ∷ _) → just (just z ∷ x)}}} where
  h1 : List Term → Bool
  h1 [] = true
  h1 [ x ] = true
  h1 (x ∷ y ∷ xs) = isYes (x == y) && h1 (y ∷ xs)

-- We accumulate the variables that are not defined in a lambda, but demand a specific context.
-- (the arguments of the function)
-- those that do not demand a specific context are omitted.
-- In case , the function is patern matched, then all arguments must belong to the same context.

data PM : Set where
-- The list describes the arguments. Each arguments might have multiple variables
-- but they must all belong to the same context.
  ¬pm : List (Maybe Term) → PM
  pm : Maybe Term → PM

ptm : PM → Set
-- Here the list is on all variables, even when some variables belong to the same argument.
ptm (¬pm _) = List (Nat × Term)
ptm (pm _) = Maybe Term



CState : Set
CState = List Term

FState : Set
FState = List (Name × PM)

addCS : CState → Term → CState
addCS cs t = t ∷ cs


_inCtx_!_ : Nat → Term → CState → Bool
n inCtx ctx ! [] = false
zero inCtx ctx ! (x ∷ cs) = case (ctx == x) of
                             λ { (yes x) → true
                               ; (no x) → false}
suc n inCtx ctx ! (x ∷ cs) = n inCtx ctx ! cs


-- Expressions other than a single var demand computation, thus the result is contained
-- in the context of the computation, the current context.
-- lambda can be passed away as variables, thus they must belong to a single context.
ff2 : Term → (Maybe Term) → CState → FState → (q : PM) → TC (FState × (ptm q))
gg2 : Name → FState → TC (FState × PM)

gg2 nm fs
  = getDefinition nm >>=
    λ { (function cs) → case (pmatched? cs) of
                          λ { false → let x = foldr (λ t y → bindTC y λ z → bindTC (ff2 t nothing [] (fst z) (¬pm [])) λ s → returnTC (fst s , snd s ∷ snd z))
                                                    (returnTC (fs , []))
                                                    (mapClause cs)
                                      in bindTC x λ z → let s = zip cs (snd z)
                                                            w = map (λ {(a , b) → ddv (ddw a) b}) s
                                                        in case (h1 w) of
                                                            λ { nothing → typeError (strErr "Context error" ∷ [])
                                                              ; (just x) → returnTC (fst z , ¬pm x)}
                            ; true → let x = foldr (λ t y → bindTC y λ z → ff2 t nothing [] (fst z) (pm (snd z)))
                                                   (returnTC (fs , nothing))
                                                   (mapClause cs)
                                     in bindTC x λ z → returnTC (fst z , pm (snd z))}
-- Axioms should also be handled.
      ; _ → typeError (strErr "This was supposed to be a function" ∷ [])} where
      h2 : List (Maybe Term) → List (Maybe Term) → Bool
      h2 [] [] = true
      h2 [] (x ∷ y) = false
      h2 (x ∷ x₁) [] = false
      h2 (nothing ∷ xs) (nothing ∷ ys) = h2 xs ys
      h2 (nothing ∷ xs) (just x ∷ ys) = false
      h2 (just x ∷ xs) (nothing ∷ ys) = false
      h2 (just x ∷ xs) (just y ∷ ys) = isYes (x == y) || h2 xs ys
      h1 : List (Maybe (List (Maybe Term))) → Maybe (List (Maybe Term))
      h1 [] = just []
      h1 [ nothing ] = nothing
      h1 [ just x ] = just x
      h1 (nothing ∷ y ∷ xs) = nothing
      h1 (just x ∷ nothing ∷ xs) = nothing
      h1 (just x ∷ just y ∷ xs) with h2 x y
      h1 (just x ∷ just y ∷ xs) | false = nothing
      h1 (just x ∷ just y ∷ xs) | true = h1 (just y ∷ xs)

ff2 t pctx cs fs = {!!}

-- Second Term is the current context.
{-# TERMINATING #-}
ff : Term → (Maybe Term) → CState → FState → Maybe Term → TC (Maybe Term)
gg : Name → TC (Maybe Term)

ff (var x args) pctx cs fs mctx =
  case pctx of
    λ { nothing → foldr (λ x y → bindTC y (λ w → ff x pctx cs fs w))
                                                      (returnTC mctx) (mapArg args)
      ; (just ctx) → case (x inCtx ctx ! cs) of               
                     λ { false → case mctx of                          
                                  λ { nothing → foldr (λ x y → bindTC y (λ w → ff x pctx cs fs w))
                                                      (returnTC pctx) (mapArg args)
                                    ; (just lctx) → case (ctx == lctx) of
                                                     λ { (yes _) → foldr (λ x y → bindTC y (λ w → ff x pctx cs fs w)) (returnTC mctx) (mapArg args)
                                                       ; (no _) → typeError ( strErr "Two arguments have different contexts." ∷ [])}}
                       ; true → foldr (λ x y → bindTC y (λ w → ff x pctx cs fs w)) (returnTC mctx) (mapArg args)}
      }
ff (con c args) ctx cs fs mctx = foldr (λ x y → bindTC y (λ w → ff x ctx cs fs w)) (returnTC mctx) (mapArg args)
ff (def (quote WE.lift) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ (arg _ nctx) ∷ (arg _ v) ∷ [])) ctx cs fs mctx
  = ff v (just nctx) cs fs mctx 
ff (def f args) ctx cs fs mctx
  = bindTC (foldr (λ x y → bindTC y (λ w → ff x ctx cs fs w)) (returnTC mctx) (mapArg args))
           λ w → {!!}
ff (lam v (abs s x)) pctx cs fs mctx
  = case pctx of
     λ { nothing → ff x pctx cs fs mctx
       ; (just ctx) → ff x pctx (ctx ∷ cs) fs mctx
       }
ff (pat-lam cls args) ctx cs fs mctx
  = bindTC (foldr (λ x y → bindTC y (λ w → ff x ctx cs fs w)) (returnTC mctx) (mapArg args))
           λ _ → foldr (λ x y → bindTC y (λ w → ff x ctx cs fs w)) (returnTC mctx) (mapClause cls)
ff (pi a b) ctx cs fs mctx = typeError (strErr "Found pie." ∷ [])
ff (agda-sort s) ctx cs fs mctx = typeError (strErr "Found Sort." ∷ [])
ff (lit l) ctx cs fs mctx = returnTC mctx
ff (meta x x₁) ctx cs fs mctx = typeError (strErr "Found Meta." ∷ [])
ff unknown ctx cs fs mctx = typeError (strErr "Found Unknown." ∷ [])


gg nm = getDefinition nm >>=
        λ { (function cs) → foldr (λ { (clause ps t) y → bindTC y (λ w → bindTC {!ff t !} {!!})
                                     ; (absurd-clause ps) y → y}) (returnTC nothing) cs
          ; _ → returnTC nothing}


macro
  bb : Term → Name → Term → TC ⊤
  bb (def (quote WE.lift) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ (arg _ c) ∷ x)) Q hole
    = typeError (termErr c ∷ []) 
  bb (lit (nat 3)) Q hole = typeError (strErr "aha" ∷ []) -- unify hole trm
  bb trm Q hole = typeError (termErr trm ∷ []) -- unify hole trm

postulate
  qq : Nat
  bob : Nat → Nat → Nat

f : Nat → Nat → Nat
f x z = bob x (ss z) where
  ss : Nat → Nat
  ss zero = x
  ss (suc _) = x
                  

data B : Set where
  erq : Nat → Nat → B
  wwe : Nat → B

aa : B → B →  Nat × Nat
aa (erq x y) (erq z w) = y , w
aa (erq x y) (wwe e) = e , x
aa (wwe x) s = x , x

cc : Nat → Nat
cc k = (λ z → z) k

qw : Nat → Nat → Nat
qw zero y  = y
qw (suc x) = λ y → x


macro
  xx : Term → TC ⊤
  xx hole = do
    un ← quoteTC {_} {Unit} unit
    d ← getDefinition (quote qw)
    typeError {_} {Unit} ((strErr (showDef d)) ∷ [])
    unify un hole

--  cc : Term → Term → TC ⊤
--  cc t hole = ff t 0 (unify t hole)

-- g : V wTy world Unit
-- g = bb (lift {V} {{weQ}} {WTy} {World} {wTy} {Unit} world unit) V


-- f : Nat → (Nat → Nat)
-- f x = cc h where
--   h : Nat → Nat
--   h y = y

g : Unit
g = xx

