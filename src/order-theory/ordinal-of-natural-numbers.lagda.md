# The ordinal of natural numbers

```agda
module order-theory.ordinal-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.ordinal-induction-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.accessible-elements-relations
open import order-theory.ordinals
open import order-theory.transitive-well-founded-relations
open import order-theory.trichotomous-ordinals
open import order-theory.well-founded-relations
```

</details>

## Idea

The natural numbers equipped with strict inequality form an
[ordinal](order-theory.ordinals.md).

## Definition

```agda
abstract
  is-accessible-element-le-ℕ :
    (n : ℕ) → is-accessible-element-Relation le-ℕ n
  is-accessible-element-le-ℕ =
    ordinal-ind-ℕ
      ( is-accessible-element-Relation le-ℕ)
      ( λ n IH → access (λ {m} → IH m))

abstract
  is-well-founded-relation-le-ℕ :
    is-well-founded-Relation le-ℕ
  is-well-founded-relation-le-ℕ =
    is-accessible-element-le-ℕ

is-transitive-well-founded-relation-le-ℕ :
  is-transitive-well-founded-relation-Relation le-ℕ
is-transitive-well-founded-relation-le-ℕ =
  ( is-well-founded-relation-le-ℕ ,
    λ x y z y<z x<y → transitive-le-ℕ x y z x<y y<z)

abstract
  extensionality-principle-le-prop-ℕ :
    extensionality-principle-Ordinal le-prop-ℕ
  extensionality-principle-le-prop-ℕ m n H =
    rec-coproduct
      ( λ m<n → ex-falso (irreflexive-le-ℕ m ((pr2 (H m)) m<n)))
      ( rec-coproduct
        ( λ p → p)
        ( λ n<m → ex-falso (irreflexive-le-ℕ n ((pr1 (H n)) n<m))))
      ( trichotomy-le-ℕ m n)

is-ordinal-le-prop-ℕ : is-ordinal le-prop-ℕ
is-ordinal-le-prop-ℕ =
  ( is-transitive-well-founded-relation-le-ℕ ,
    extensionality-principle-le-prop-ℕ)

ordinal-ℕ : Ordinal lzero lzero
ordinal-ℕ = (ℕ , le-prop-ℕ , is-ordinal-le-prop-ℕ)

trichotomous-ordinal-ℕ : Trichotomous-Ordinal lzero lzero
trichotomous-ordinal-ℕ = (ordinal-ℕ , trichotomy-le-ℕ)
```
