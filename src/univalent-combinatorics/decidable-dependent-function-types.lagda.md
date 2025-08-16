# Decidable dependent function types

```agda
module univalent-combinatorics.decidable-dependent-function-types where

open import elementary-number-theory.decidable-dependent-function-types public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We describe conditions under which dependent products are decidable.

```agda
is-decidable-Π-Fin :
  {l1 : Level} (k : ℕ) {B : Fin k → UU l1} →
  ((x : Fin k) → is-decidable (B x)) → is-decidable ((x : Fin k) → B x)
is-decidable-Π-Fin zero-ℕ {B} d = inl ind-empty
is-decidable-Π-Fin (succ-ℕ k) {B} d =
  is-decidable-Π-Maybe
    ( is-decidable-Π-Fin k (λ x → d (inl x)))
    ( d (inr star))
```

```agda
is-decidable-Π-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-count e d =
  is-decidable-Π-equiv
    ( equiv-count e)
    ( λ x → id-equiv)
    ( is-decidable-Π-Fin
      ( number-of-elements-count e)
      ( λ x → d (map-equiv-count e x)))

is-decidable-Π-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-finite A →
  ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-is-finite {l1} {l2} {A} {B} H d =
  is-decidable-iff
    ( map-Π (λ x → ε-operator-is-decidable (d x)))
    ( map-Π (λ x → unit-trunc-Prop))
    ( is-decidable-iff
      ( α)
      ( finite-choice H)
      ( apply-universal-property-trunc-Prop H
        ( is-decidable-Prop (trunc-Prop ((x : A) → B x)))
        ( λ e →
          is-decidable-iff
            ( finite-choice H)
            ( α)
            ( is-decidable-Π-count e
              ( λ x →
                is-decidable-iff
                  ( unit-trunc-Prop)
                  ( ε-operator-is-decidable (d x))
                  ( d x))))))
  where
  α : type-trunc-Prop ((x : A) → B x) → (x : A) → type-trunc-Prop (B x)
  α = map-universal-property-trunc-Prop
        ( Π-Prop A (λ x → trunc-Prop (B x)))
        ( λ (f : (x : A) → B x) (x : A) → unit-trunc-Prop (f x))
```
