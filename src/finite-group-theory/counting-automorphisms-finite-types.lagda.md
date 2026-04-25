# Counting automorphisms of finite types

```agda
module finite-group-theory.counting-automorphisms-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.natural-numbers

open import finite-group-theory.counting-permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [finite type](univalent-combinatorics.finite-types.md) `X` with
cardinality `n`, the type of [automorphisms](foundation.automorphisms.md) of `X`
has cardinality equal to the [factorial](elementary-number-theory.factorials.md)
of `n`.

## Properties

### Counting permutations of `X` from a counting of `X`

```agda
count-aut-count :
  {l : Level} {X : UU l} → count X → count (Aut X)
count-aut-count {X = X} (n , Fin-n≃X) =
  ( factorial-ℕ n ,
    tr
      ( λ k → Fin k ≃ Aut X)
      ( number-of-elements-count-Permutation n)
      ( equiv-aut-equiv Fin-n≃X ∘e equiv-count (count-Permutation n)))
```

### The automorphisms of a type `X` with cardinality `n` have cardinality `n!`

```agda
abstract
  has-cardinality-factorial-aut-has-cardinality-ℕ :
    {l : Level} {X : UU l} (n : ℕ) → has-cardinality-ℕ n X →
    has-cardinality-ℕ (factorial-ℕ n) (Aut X)
  has-cardinality-factorial-aut-has-cardinality-ℕ n =
    map-trunc-Prop
      ( λ Fin-n≃X → equiv-count (count-aut-count (n , Fin-n≃X)))

aut-Type-With-Cardinality-ℕ :
  {l : Level} (n : ℕ) → Type-With-Cardinality-ℕ l n →
  Type-With-Cardinality-ℕ l (factorial-ℕ n)
aut-Type-With-Cardinality-ℕ n (X , |X|=n) =
  ( Aut X , has-cardinality-factorial-aut-has-cardinality-ℕ n |X|=n)
```

### The automorphisms of a finite type

```agda
abstract
  is-finite-aut-is-finite :
    {l : Level} {X : UU l} → is-finite X → is-finite (Aut X)
  is-finite-aut-is-finite = map-trunc-Prop count-aut-count

aut-Finite-Type : {l : Level} → Finite-Type l → Finite-Type l
aut-Finite-Type (X , is-finite-X) =
  ( Aut X , is-finite-aut-is-finite is-finite-X)

abstract
  number-of-elements-aut-Finite-Type :
    {l : Level} (X : Finite-Type l) →
    number-of-elements-Finite-Type (aut-Finite-Type X) ＝
    factorial-ℕ (number-of-elements-Finite-Type X)
  number-of-elements-aut-Finite-Type FX@(X , is-finite-X) =
    rec-trunc-Prop
      ( Id-Prop ℕ-Set _ _)
      ( λ cX →
        ( inv
          ( compute-number-of-elements-is-finite
            ( count-aut-count cX)
            ( is-finite-aut-is-finite is-finite-X))) ∙
        ( ap factorial-ℕ (compute-number-of-elements-is-finite cX is-finite-X)))
      ( is-finite-X)
```
