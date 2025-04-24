# Finitely presented types

```agda
module univalent-combinatorics.finitely-presented-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-presented-types
open import foundation.set-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is {{#concept "finitely presented" Agda=is-finitely-presented}} if it is
[presented](foundation.set-presented-types.md) by a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definitions

### To have a presentation of cardinality `k`

```agda
has-presentation-of-cardinality-Prop : {l : Level} → ℕ → UU l → Prop l
has-presentation-of-cardinality-Prop k A =
  is-set-presentation-Prop A (Fin-Set k)

has-presentation-of-cardinality : {l : Level} → ℕ → UU l → UU l
has-presentation-of-cardinality k A =
  type-Prop (has-presentation-of-cardinality-Prop k A)
```

### Finitely presented types

```agda
is-finitely-presented : {l : Level} → UU l → UU l
is-finitely-presented A =
  Σ ℕ (λ k → has-presentation-of-cardinality k A)
```

## Properties

### A type has finitely many connected components if and only if it has a finite presentation

```agda
has-presentation-of-cardinality-has-cardinality-connected-components :
  {l : Level} (k : ℕ) {A : UU l} →
  has-cardinality-connected-components k A →
  has-presentation-of-cardinality k A
has-presentation-of-cardinality-has-cardinality-connected-components k {A} H =
  apply-universal-property-trunc-Prop H
    ( has-presentation-of-cardinality-Prop k A)
    ( λ e →
      apply-universal-property-trunc-Prop
        ( P2 e)
        ( has-presentation-of-cardinality-Prop k A)
        ( λ g →
          unit-trunc-Prop
            ( pair
              ( λ x → pr1 (g x))
              ( is-equiv-htpy-equiv e (λ x → pr2 (g x))))))
  where
  P1 :
    (e : Fin k ≃ type-trunc-Set A) (x : Fin k) →
    type-trunc-Prop (fiber unit-trunc-Set (map-equiv e x))
  P1 e x = is-surjective-unit-trunc-Set A (map-equiv e x)
  P2 :
    (e : Fin k ≃ type-trunc-Set A) →
    type-trunc-Prop ((x : Fin k) → fiber unit-trunc-Set (map-equiv e x))
  P2 e = finite-choice-Fin k (P1 e)

has-cardinality-connected-components-has-presentation-of-cardinality :
  {l : Level} (k : ℕ) {A : UU l} → has-presentation-of-cardinality k A →
  has-cardinality-connected-components k A
has-cardinality-connected-components-has-presentation-of-cardinality k {A} H =
  apply-universal-property-trunc-Prop H
    ( has-cardinality-connected-components-Prop k A)
    ( λ (f , E) → unit-trunc-Prop (unit-trunc-Set ∘ f , E))
```

### To be finitely presented is a property

In other words, the cardinalty of a finite presentation is unique.

```agda
module _
  {l : Level} {A : UU l}
  where

  all-elements-equal-is-finitely-presented :
    all-elements-equal (is-finitely-presented A)
  all-elements-equal-is-finitely-presented (k , K) (l , L) =
    eq-type-subtype
      ( λ n → is-set-presentation-Prop A (Fin-Set n))
      ( eq-cardinality
        ( has-cardinality-connected-components-has-presentation-of-cardinality
          ( k)
          ( K))
        ( has-cardinality-connected-components-has-presentation-of-cardinality
          ( l)
          ( L)))

  is-prop-is-finitely-presented : is-prop (is-finitely-presented A)
  is-prop-is-finitely-presented =
    is-prop-all-elements-equal all-elements-equal-is-finitely-presented

is-finitely-presented-Prop : {l : Level} (A : UU l) → Prop l
is-finitely-presented-Prop A =
  ( is-finitely-presented A , is-prop-is-finitely-presented)
```
