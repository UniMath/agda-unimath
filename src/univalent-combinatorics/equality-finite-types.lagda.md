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
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Any finite type is a set because it is merely equivalent to a standard finite type. Moreover, any finite type has decidable equality. In particular, this implies that the type of identifications between any two elements in a finite type is finite.

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
has-decidable-equality-has-cardinality :
  {l1 : Level} {X : UU l1} (k : ℕ) →
  has-cardinality k X → has-decidable-equality X
has-decidable-equality-has-cardinality {l1} {X} k H =
  apply-universal-property-trunc-Prop H
    ( has-decidable-equality-Prop X)
    ( λ e → has-decidable-equality-equiv' e (has-decidable-equality-Fin k))
```

### The type of identifications between any two elements in a finite type is finite

```agda
abstract
  is-finite-eq :
    {l1 : Level} {X : UU l1} →
    has-decidable-equality X → {x y : X} → is-finite (Id x y)
  is-finite-eq d {x} {y} = is-finite-count (count-eq d x y)

Id-𝔽 : {l : Level} → (X : 𝔽 l) (x y : type-𝔽 X) → 𝔽 l
pr1 (Id-𝔽 X x y) = Id x y
pr2 (Id-𝔽 X x y) =
  is-finite-eq (has-decidable-equality-is-finite (is-finite-type-𝔽 X))
```
