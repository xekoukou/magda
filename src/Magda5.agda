module Magda5 where

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

postulate
  IMPOSSIBLE : ∀{α} → {A : Set α} → A

--TODO Deferentiate between non-use and use in primitive function or axiom.
-- Non-used is not captured on application, since it is probably used in the type system.
-- So we would not be able to use anywhere else.

-- Differentiate between lambda and non-lambda argument. ???? lambdas belong to a specific context, but their
-- arguments can be from other contexts, thus we need to keep more information.
-- The context of the lambda is derived when we apply the arguments. Inside the lambda, this is the current context.


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



ptmatched? : Clause → List Bool
ptmatched? (clause ps t) = map (λ { (arg i (con c ps)) → true
                                    ; (arg i dot) → true
                                    ; (arg i (var s)) → false
                                    ; (arg i (lit l)) → true
                                    ; (arg i (proj f)) → true
                                    ; (arg i absurd) → true}) ps
ptmatched? (absurd-clause ps) = map (λ _ → false) ps

-- We check that all clauses have the same number of top-level patterns,
-- so as to simplify things.
ptmatchedL? : (l : Nat) → List Clause → Maybe (List Bool)
ptmatchedL? zero [] = just []
ptmatchedL? (suc _) [] = nothing
ptmatchedL? l (x ∷ []) with ptmatched? x | l == length (ptmatched? x)
ptmatchedL? l (x ∷ []) | g | yes _ = just g
ptmatchedL? l (x ∷ []) | g | no _ = nothing
ptmatchedL? l (x ∷ y ∷ xs) with ptmatched? x | l == length (ptmatched? x)
ptmatchedL? l (x ∷ y ∷ xs) | g | yes _ = ptmatchedL? l (y ∷ xs) >>= λ z → just $ map (uncurry _&&_) (zip g z)
ptmatchedL? l (x ∷ y ∷ xs) | g | no _ = nothing
                       


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
                    in snd $ foldr (λ z y → let q = z + fst y in q , q ∷ snd y) (0 , []) x
ddw (absurd-clause ps) = []

data Used : Set where
  used : Used
  ¬used : Used

data Lambda : Used → Set where
  lambda : Lambda used
  ¬lambda : Lambda used
  unknown : Lambda ¬used

-- The uid must be unique. Make sure it is.
data TId : Set where
 metaId : Nat → TId
 trm : Term → TId

sv : (us : Used) → Lambda us → Set
record SVar : Set

sv used lambda = TId × List SVar
sv used ¬lambda = TId
sv ¬used y = Unit

record SVar where
  constructor svar
  inductive
  field
    vused : Used
    vlambda : Lambda vused
    vdat : sv vused vlambda

open SVar

-- They are equal if they have the same term or one of them is a meta, in
-- which case we save this information to try unification.

eqMet : TId → TId → Maybe (Maybe (Nat × Either Nat Term))
eqMet (metaId x) (metaId y) = just $ just $ x , (left y)
eqMet (metaId x) (trm y) = just $ just $ x , (right y)
eqMet (trm x) (metaId y) = just $ just $ y , (right x)
eqMet (trm x) (trm y) with x == y
... | yes _ = just nothing
... | no _ = nothing

-- The Term might contain variables, which means that the context is itself a previous argument.
-- To use the FState, one needs to apply the arguments fist.
FState : Set
FState = List (Name × List SVar)

-- The context of all lambda vars, including lambdas.
CState : Set
CState = List (Nat × SVar)

ddo : Clause → CState
ddo cl = map (λ x → x , record { vused = ¬used ; vlambda = unknown ; vdat = unit }) (ddw cl)


narg : Name → TC Nat
narg nm = bindTC (getType nm) λ z → returnTC (h1 z) where
  h1 : Term → Nat
  h1 (var x args) = 1
  h1 (con c args) = 1
  h1 (def f args) = 1
  h1 (lam v t) = 1
  h1 (pat-lam cs args) = 1
  h1 (pi a (abs _ t)) = 1 + h1 t
  h1 (agda-sort s) = 1 -- TODO return an error.
  h1 (lit l) = 1
  h1 (meta x x₁) = 1
  h1 unknown = 1

instance
  qEth : Eq (Either Nat Term)
  _==_ ⦃ qEth ⦄ (left x) (left y) with x == y
  ... | yes refl = yes refl
  ... | no d = no λ {refl → d refl}
  _==_ ⦃ qEth ⦄ (left x) (right y) = no λ {()}
  _==_ ⦃ qEth ⦄ (right x) (left y) = no λ {()}
  _==_ ⦃ qEth ⦄ (right x) (right y) with x == y
  ... | yes refl = yes refl
  ... | no d = no λ { refl → d refl}

-- Part of unification.
-- Returns nothing if the eqautions lead to two terms in an equations that are not equal.
-- The remaining reduced equations are consistent with each other.
redEqs : List (Nat × Either Nat Term) → Maybe (List (List Nat × (Either Nat Term)))
redEqs ls = h2 (re ls []) where
  re : List (Nat × Either Nat Term) → List (List (Either Nat Term)) → List (List (Either Nat Term))
  re [] q = q
  re ((x , y) ∷ ls) q = let z = foldr {B = (List (List (Either Nat Term))) × Bool}
                                      (λ z q → case (elem {{qEth}} (left x) z) -- it will only happen in one case.
                                                 of λ { true →  ((y ∷ z) ∷ fst q) , true
                                                      ; false → z ∷ fst q , snd q }) ([] , false) q
                            q = case (snd z) of
                                  λ { true → re ls (fst z)
                                    ; false → let w = foldr {B = (List (List (Either Nat Term))) × Bool}
                                                            (λ z q → case (elem {{qEth}} y z)
                                                                       of λ { true →  (((left x) ∷ z) ∷ fst q) , true
                                                                            ; false → z ∷ fst q , snd q }) ([] , false) q
                                              in case (snd w) of
                                                   λ { true → re ls (fst w)
                                                     ; false → re ls ((left x ∷ y ∷ []) ∷ q)}} -- Adding a new category.
                        in q
  -- All terms should be equal to each other , or there will be an error. (nothing)
  -- return all the metas that should/will be replaced with a unique term when it is found.
  h2 : List (List (Either Nat Term)) → Maybe (List (List Nat × (Either Nat Term)))
  h2 [] = just []
  h2 (x ∷ ls) = let z = foldr {B = List Nat × List Term}
                              (λ { (left e) y → e ∷ fst y , snd y
                                 ; (right e) y → fst y , e ∷ snd y}) ([] , []) x
                    q : Maybe (List Nat × (Either Nat Term))
                    q = case (h21 (snd z))
                          of λ { false → nothing
                               ; true → case (snd z) of
                                         λ { [] → case (fst z) of
                                                   λ { [] → IMPOSSIBLE -- Maybe throw a n internal error.
                                                     ; (x ∷ _) → just (fst z , left x)}
                                           ; (t ∷ _) → just (fst z , right t)}}
                in q >>= λ w → h2 ls >>= λ zs → just (w ∷ zs) where
    h21 : List Term → Bool
    h21 [] = true
    h21 [ x ] = true
    h21 (x ∷ y ∷ ls) with x == y
    ... | yes _ = h21 (y ∷ ls)
    ... | no _  = false



-- unify : List SVar → 


-- First arg is the term to be type checked.
-- Second arg is the current context.
-- Third is whether an argument is pattern matched.
-- Forth is the current analysis of the arguments, including the lambdas.
-- Fifth is the results for other functions.

ff : Term → (Maybe Term) → List Bool → CState → FState → TC (FState × List SVar)
gg : Name → FState → TC (FState × List SVar)

gg nm fs
  = narg nm >>=
    λ l → getDefinition nm >>=
    λ { (function cs) → maybe (typeError (strErr "Clauses with missing variables." ∷ []))
                (λ pt → let d = map ddo cs
                            x = foldr (λ t y → bindTC y
                                               λ z → bindTC (ff (fst t) nothing pt (snd t) (fst z))
                                                     λ s → case (h3 (snd s) (snd z)) of
                                                            λ { nothing → typeError (strErr "Error 232" ∷ [])
                                                              ; (just x) → returnTC (fst s , x)})
                                                    (returnTC (fs , h1 l))
                                                    (zip (mapClause cs) d)
                        in x) (ptmatchedL? l cs)
                       -- Axioms and primitive functions are simply computed in the context of the environment,
                       -- thus they do not pose any restrictions themselves.
      ; axiom → returnTC (fs , h1 l)
      ; prim-fun → returnTC (fs , h1 l)
      ; _ → typeError (strErr "This was supposed to be a function" ∷ [])} where
      -- h1 could be top level function.
      h1 : Nat → List SVar
      h1 zero = []
      h1 (suc x) = record { vused = ¬used ; vlambda = unknown ; vdat = unit } ∷ h1 x

      h2 : List SVar → List SVar → Maybe ((List SVar) × List (Nat × Either Nat Term))
      h2 [] [] = just $ [] , []
      h2 [] (_ ∷ _) = nothing
      h2 (x ∷ xs) [] = nothing
      h2 ((svar ¬used vlambda vdat) ∷ xs) (y ∷ ys) = h2 xs ys >>= λ zs → just $ (y ∷ (fst zs)) , snd zs 
      h2 (x@(svar used _ _) ∷ xs) ((svar ¬used _ _) ∷ ys) = h2 xs ys >>= λ zs → just $ x ∷ fst zs , snd zs
      h2 (svar used ¬lambda tx ∷ xs) (svar used ¬lambda ty ∷ ys) with eqMet tx ty
      ... | (just meq) =  h2 xs ys >>=
              λ zs → let bb = svar used ¬lambda tx ∷ (fst zs) -- here we forget ty
                         qq = snd zs                          -- but we keep the equation meq to perform the
                     in case meq of                           -- remaining unifications.
                         λ { nothing → just $ bb , qq
                           ; (just meq) → just $ bb , meq ∷ qq}
      ... | nothing = nothing
      h2 (svar used ¬lambda _ ∷ xs) (svar used lambda _ ∷ ys) = nothing
      h2 (svar used lambda _ ∷ xs) (svar used ¬lambda _ ∷ ys) = nothing
      h2 (svar used lambda (tx , lx) ∷ xs) (svar used lambda (ty , ly) ∷ ys) with eqMet tx ty
      ... | nothing = nothing
      ... | just meq = h2 lx ly >>= λ ss → h2 xs ys >>=
              λ zs → let bb = svar used lambda (tx , fst ss) ∷ (fst zs)  -- similar to the above comments.
                         qq = snd ss ++ snd zs
                     in case meq of
                         λ { nothing → just $ bb , qq
                           ; (just meq) → just $ bb , meq ∷ qq}

      h3 : List SVar → List SVar → Maybe (List SVar)
      h3 a b = {!!} where
        h31 = h2 a b
        h32 = h31 >>= λ q → redEqs (snd q) >>= λ {x → {!!}}
        

--       h2 (record { vused = used ; vlambda = lambda ; vdat = vdatx } ∷ xs) (record { vused = used ; vlambda = ¬lambda ; vdat = vdaty } ∷ ys) = nothing -- Internal error , not typeError. ??
--       h2 (record { vused = used ; vlambda = ¬lambda ; vdat = vdatx } ∷ xs) (record { vused = used ; vlambda = lambda ; vdat = vdaty } ∷ ys) = nothing -- Internal error , not typeError. ??
--       h2 (x@(record { vused = used ; vlambda = ¬lambda ; vdat = vdatx }) ∷ xs) (record { vused = used ; vlambda = ¬lambda ; vdat = vdaty } ∷ ys) with vdatx == vdaty
--       ... | yes _ = h2 xs ys >>= λ zs → just (x ∷ ys)
--       ... | no _  = nothing
-- 

-- An arg that is not a var needs to have the same context as the current one simply because some computation
-- needs to happen, so it will happen in the current context.
-- If it is a var , then we record the vars context in the lambda.

ff (var x args) ctx pt cs fs = {!!}
ff (con c args) ctx pt cs fs = {!!}
ff (def f args) ctx pt cs fs = {!!}
ff (lam v t) ctx pt cs fs = {!!}
ff (pat-lam cs₁ args) ctx pt cs fs = {!!}
ff (pi a b) ctx pt cs fs = {!!}
ff (agda-sort s) ctx pt cs fs = {!!}
ff (lit l) ctx pt cs fs = {!!}
ff (meta x x₁) ctx pt cs fs = {!!}
ff unknown ctx pt cs fs = {!!}
