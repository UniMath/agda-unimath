# Orbits


```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-groups.orbits where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; succ-ℕ; zero-ℕ; is-nonzero-ℕ)
open import elementary-number-theory.inequality-natural-numbers using (le-ℕ)
open import elementary-number-theory.iterating-functions using
  ( iterate; iterate-add-ℕ)
open import elementary-number-theory.well-ordering-principle-natural-numbers using
  ( minimal-element-ℕ; well-ordering-principle-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr; neq-inr-inl)
open import foundation.decidable-types using (is-decidable)
open import foundation.decidable-maps using (is-decidable-map)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-equiv)
open import foundation.equivalence-relations using (Eq-Rel)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop;
    trunc-Prop; unit-trunc-Prop)
open import foundation.universe-levels using (Level; UU; lzero)

open import foundation-core.embeddings using (is-emb)
open import foundation-core.fibers-of-maps using (fib)

open import univalent-combinatorics.standard-finite-types using (Fin; succ-Fin)
open import univalent-combinatorics.finite-types using (UU-Fin-Level; type-UU-Fin-Level)
```

## Idea

...

## Definitions

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) (f : (type-UU-Fin-Level X ≃ type-UU-Fin-Level X)) 
  where

  has-finite-orbits : (a : type-UU-Fin-Level X) → Σ ℕ (λ k → (is-nonzero-ℕ k) × Id (iterate k (map-equiv f) a) a)
  has-finite-orbits a = {!!}
    where
    P : ℕ → UU l
    P n = Σ ℕ (λ m → (le-ℕ m n) × (Id (iterate (succ-ℕ n) (map-equiv f) a) (iterate (succ-ℕ m) (map-equiv f) a)))
    min-repeating : minimal-element-ℕ P
    min-repeating = well-ordering-principle-ℕ P {!!} {!!}

  same-orbits : Eq-Rel l (type-UU-Fin-Level X)
  (pr1 same-orbits) a b = trunc-Prop (Σ ℕ (λ k → Id (iterate k (map-equiv f) a) b))
  pr1 (pr2 same-orbits) = unit-trunc-Prop (pair 0 refl)
  pr1 (pr2 (pr2 same-orbits)) {a} {b} P =
    apply-universal-property-trunc-Prop
      ( P)
      ( pr1 same-orbits b a)
      (λ (pair k p) → unit-trunc-Prop (cases-symmetry-same-orbits a b k p))
    where
    cases-symmetry-same-orbits : (a b : type-UU-Fin-Level X) (k1 : ℕ) → Id (iterate k1 (map-equiv f) a) b →
      Σ ℕ (λ k2 → Id (iterate k2 (map-equiv f) b) a)
    cases-symmetry-same-orbits a b zero-ℕ p = pair 0 (inv p)
    cases-symmetry-same-orbits a b (succ-ℕ k1) p = {!!}
  pr2 (pr2 (pr2 same-orbits)) {a} {b} {c} P Q =
    apply-universal-property-trunc-Prop
      ( P)
      ( pr1 same-orbits a c)
      ( λ (pair k1 p) →
        apply-universal-property-trunc-Prop
          ( Q)
          ( (pr1 same-orbits a c))
          ( λ (pair k2 q) →
            ( unit-trunc-Prop (pair
              ( add-ℕ k2 k1)
              ( (iterate-add-ℕ k2 k1 (map-equiv f) a) ∙
                ( (ap (iterate k2 (map-equiv f)) p ∙ q)))))))
```
