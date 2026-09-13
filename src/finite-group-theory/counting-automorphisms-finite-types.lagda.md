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
module _
  {l1 : Level} {X : UU l1} ((n , e) : count X)
  where

  count-aut :
    count (Aut X)
  count-aut =
    ( factorial-ℕ n ,
      conjugation-aut e ∘e equiv-count (count-Permutation n))

  number-of-elements-count-aut :
    number-of-elements-count count-aut ＝ factorial-ℕ n
  number-of-elements-count-aut = refl
```

### The automorphisms of a type `X` with cardinality `n` have cardinality `n!`

```agda
module _
  {l1 : Level} (n : ℕ)
  where

  abstract
    has-cardinality-factorial-aut-has-cardinality-ℕ :
      {X : UU l1} →
      has-cardinality-ℕ n X → has-cardinality-ℕ (factorial-ℕ n) (Aut X)
    has-cardinality-factorial-aut-has-cardinality-ℕ =
      map-trunc-Prop
        ( λ e → equiv-count (count-aut (n , e)))

  aut-Type-With-Cardinality-ℕ :
    Type-With-Cardinality-ℕ l1 n → Type-With-Cardinality-ℕ l1 (factorial-ℕ n)
  aut-Type-With-Cardinality-ℕ (X , e) =
    ( Aut X , has-cardinality-factorial-aut-has-cardinality-ℕ e)
```

### The automorphisms of a finite type

```agda
module _
  {l1 : Level}
  where

  abstract
    is-finite-aut-is-finite :
      {X : UU l1} → is-finite X → is-finite (Aut X)
    is-finite-aut-is-finite = map-trunc-Prop count-aut

  aut-Finite-Type : Finite-Type l1 → Finite-Type l1
  aut-Finite-Type (X , H) =
    ( Aut X , is-finite-aut-is-finite H)

  abstract
    number-of-elements-aut-Finite-Type :
      (X : Finite-Type l1) →
      number-of-elements-Finite-Type (aut-Finite-Type X) ＝
      factorial-ℕ (number-of-elements-Finite-Type X)
    number-of-elements-aut-Finite-Type (X , H) =
      apply-universal-property-trunc-Prop H
        ( Id-Prop ℕ-Set _ _)
        ( λ (n , e) →
          inv
            ( compute-number-of-elements-is-finite
              ( count-aut (n , e))
              ( is-finite-aut-is-finite H)) ∙
          ap factorial-ℕ (compute-number-of-elements-is-finite (n , e) H))
```
