# Fibers of maps between finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.fibers-of-maps-between-finite-types where

open import foundation.contractible-types using (is-contr-total-path')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using
  ( equiv-pair-eq-Σ)
open import foundation.equivalences using (_∘e_)
open import foundation.fibers-of-maps using (fib)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.identity-types using (Id; refl; tr)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; unit-trunc-Prop)
open import foundation.sections using (map-section)
open import foundation.type-arithmetic-dependent-pair-types using
  ( left-unit-law-Σ-is-contr; inv-assoc-Σ)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import univalent-combinatorics.counting-fibers-of-maps using
  ( count-fib)
open import univalent-combinatorics.equality-finite-types using
  ( is-finite-eq; has-decidable-equality-is-finite)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-Prop; 𝔽; type-𝔽; is-finite-type-𝔽; is-finite-equiv')
```

## Idea

The fibers of maps between finite types are finite.

## Theorem

```agda
abstract
  is-finite-fib :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    is-finite X → is-finite Y → (y : Y) → is-finite (fib f y)
  is-finite-fib f is-finite-X is-finite-Y y =
    apply-universal-property-trunc-Prop
      ( is-finite-X)
      ( is-finite-Prop (fib f y))
      ( λ H →
        apply-universal-property-trunc-Prop
          ( is-finite-Y)
          ( is-finite-Prop (fib f y))
          ( λ K → unit-trunc-Prop (count-fib f H K y)))

fib-𝔽 : (X Y : 𝔽) (f : type-𝔽 X → type-𝔽 Y) → type-𝔽 Y → 𝔽
pr1 (fib-𝔽 X Y f y) = fib f y
pr2 (fib-𝔽 X Y f y) =
  is-finite-fib f (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y) y
```

```agda
abstract
  is-finite-fib-map-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
    (t : Σ A B) → is-finite (fib (map-section b) t)
  is-finite-fib-map-section {l1} {l2} {A} {B} b f g (pair y z) =
    is-finite-equiv'
      ( ( ( left-unit-law-Σ-is-contr
            ( is-contr-total-path' y)
            ( pair y refl)) ∘e
          ( inv-assoc-Σ A
            ( λ x → Id x y)
            ( λ t → Id (tr B (pr2 t) (b (pr1 t))) z))) ∘e
        ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
      ( is-finite-eq (has-decidable-equality-is-finite (g y)))
```
