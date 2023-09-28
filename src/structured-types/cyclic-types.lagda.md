# Cyclic types

```agda
module structured-types.cyclic-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers

open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **cyclic type** consists of a type `A` equipped with an automorphism
`e : A ≃ A` which is cyclic in the sense that

```text
  ∀ (x y : A), ∃ (k : ℤ), eᵏ x ＝ y.
```

Equivalently, a cyclic type is a
[connected set bundle](synthetic-homotopy-theory.connected-set-bundles-circle.md)
over the [circle](synthetic-homotopy-theory.circle.md).

Equivalently, a cyclic set is a set which is a `C`-torsor for some cyclic group
`C`.

## Definition

### The predicate of being a cyclic type

```agda
module _
  {l : Level} (X : Set l) (e : type-Set X ≃ type-Set X)
  where

  is-cyclic-prop-Set : Prop l
  is-cyclic-prop-Set =
    prod-Prop
      ( trunc-Prop (type-Set X))
      ( Π-Prop
        ( type-Set X)
        ( λ x →
          Π-Prop
            ( type-Set X)
            ( λ y →
              ∃-Prop ℤ
                ( λ k → map-iterate-automorphism-ℤ k e x ＝ y))))

  is-cyclic-Set : UU l
  is-cyclic-Set = type-Prop is-cyclic-prop-Set

Cyclic-Set : (l : Level) → UU (lsuc l)
Cyclic-Set l =
  Σ (Set l) (λ X → Σ (type-Set X ≃ type-Set X) (λ e → is-cyclic-Set X e))
```
