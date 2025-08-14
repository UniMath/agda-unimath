# Equality in finite types

```agda
module univalent-combinatorics.equality-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.propositions

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Any finite type is a set because it is merely equivalent to a standard finite
type. Moreover, any finite type has decidable equality. In particular, this
implies that the type of identifications between any two elements in a finite
type is finite.

## Properties

### Any finite type has decidable equality

```agda
has-decidable-equality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-decidable-equality X
has-decidable-equality-is-finite {l1} {X} is-finite-X =
  apply-universal-property-trunc-Prop is-finite-X
    ( has-decidable-equality-Prop X)
    ( λ e →
      has-decidable-equality-equiv'
        ( equiv-count e)
        ( has-decidable-equality-Fin (number-of-elements-count e)))
```

### Any type of finite cardinality has decidable equality

```agda
has-decidable-equality-has-cardinality-ℕ :
  {l1 : Level} {X : UU l1} (k : ℕ) →
  has-cardinality-ℕ k X → has-decidable-equality X
has-decidable-equality-has-cardinality-ℕ {l1} {X} k H =
  apply-universal-property-trunc-Prop H
    ( has-decidable-equality-Prop X)
    ( λ e → has-decidable-equality-equiv' e (has-decidable-equality-Fin k))
```

### The type of identifications between any two elements in a finite type is finite

```agda
abstract
  is-finite-eq :
    {l : Level} {X : UU l} →
    has-decidable-equality X → {x y : X} → is-finite (Id x y)
  is-finite-eq d {x} {y} = is-finite-count (count-eq d x y)

is-finite-eq-is-finite :
    {l : Level} {X : UU l} → is-finite X → {x y : X} → is-finite (x ＝ y)
is-finite-eq-is-finite H = is-finite-eq (has-decidable-equality-is-finite H)

is-finite-eq-Finite-Type :
  {l : Level} → (X : Finite-Type l)
  {x y : type-Finite-Type X} → is-finite (x ＝ y)
is-finite-eq-Finite-Type X =
  is-finite-eq-is-finite (is-finite-type-Finite-Type X)

Id-Finite-Type :
  {l : Level} → (X : Finite-Type l) (x y : type-Finite-Type X) → Finite-Type l
pr1 (Id-Finite-Type X x y) = Id x y
pr2 (Id-Finite-Type X x y) = is-finite-eq-Finite-Type X

Id-Finite-Type-Prop :
  {l : Level} {X : Finite-Type l} (x y : type-Finite-Type X) → Prop l
Id-Finite-Type-Prop {l} {X} x y =
  has-decidable-equality-eq-Prop (has-decidable-equality-is-finite
  ( is-finite-type-Finite-Type X)) x y

Id-Finite-Type-Decidable-Prop :
  {l : Level} {X : Finite-Type l} (x y : type-Finite-Type X) → Decidable-Prop l
Id-Finite-Type-Decidable-Prop {l} {X} x y =
  has-decidable-equality-eq-Decidable-Prop (has-decidable-equality-is-finite
  ( is-finite-type-Finite-Type X)) x y

Id-has-cardinality-ℕ-Prop :
  {l : Level} {X : UU l} (k : ℕ) → has-cardinality-ℕ k X → (x y : X) → Prop l
Id-has-cardinality-ℕ-Prop {l} {X} k H x y =
  has-decidable-equality-eq-Prop
  ( has-decidable-equality-has-cardinality-ℕ k H) x y

Id-has-cardinality-ℕ-Decidable-Prop :
  {l : Level} {X : UU l} (k : ℕ) → has-cardinality-ℕ k X → (x y : X) →
  Decidable-Prop l
Id-has-cardinality-ℕ-Decidable-Prop {l} {X} k H x y =
  has-decidable-equality-eq-Decidable-Prop
  ( has-decidable-equality-has-cardinality-ℕ k H) x y
```
