# Inhabited finitely enumerable types

```agda
module univalent-combinatorics.inhabited-finitely-enumerable-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.images
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.finitely-enumerable-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An
{{#concept "inhabited finitely enumerable type" Agda=Inhabited-Finitely-Enumerable-Type}}
is a
[finitely enumerable type](univalent-combinatorics.finitely-enumerable-types.md) that is [inhabited](foundation.inhabited-types.md).

## Definition

```agda
Inhabited-Finitely-Enumerable-Type : (l : Level) → UU (lsuc l)
Inhabited-Finitely-Enumerable-Type l =
  type-subtype
    ( is-inhabited-Prop ∘ type-Finitely-Enumerable-Type {l})

module _
  {l : Level} (X : Inhabited-Finitely-Enumerable-Type l)
  where

  finitely-enumerable-type-Inhabited-Finitely-Enumerable-Type :
    Finitely-Enumerable-Type l
  finitely-enumerable-type-Inhabited-Finitely-Enumerable-Type = pr1 X

  type-Inhabited-Finitely-Enumerable-Type : UU l
  type-Inhabited-Finitely-Enumerable-Type =
    type-Finitely-Enumerable-Type
      ( finitely-enumerable-type-Inhabited-Finitely-Enumerable-Type)
```

## Properties

### The image of an inhabited finitely enumerable type under a map is inhabited finitely enumerable

```agda
im-Inhabited-Finitely-Enumerable-Type :
  {l1 l2 : Level} (X : Inhabited-Finitely-Enumerable-Type l1) →
  {Y : UU l2} → (f : type-Inhabited-Finitely-Enumerable-Type X → Y) →
  Inhabited-Finitely-Enumerable-Type (l1 ⊔ l2)
im-Inhabited-Finitely-Enumerable-Type (X , |X|) f =
  ( im-Finitely-Enumerable-Type X f ,
    map-is-inhabited (map-unit-im f) |X|)
```

### For an inhabited finitely enumerable type `X`, there exists `n : ℕ` such that `Fin (succ-ℕ n)` surjects onto `X`

```agda
abstract
  exists-enumeration-Inhabited-Finitely-Enumerable-Type :
    {l : Level} (X : Inhabited-Finitely-Enumerable-Type l) →
    is-inhabited
      ( Σ ℕ (λ n → Fin (succ-ℕ n) ↠ type-Inhabited-Finitely-Enumerable-Type X))
  exists-enumeration-Inhabited-Finitely-Enumerable-Type ((X , ∃eX) , |X|) =
    map-trunc-Prop
      ( λ where
        eX@(zero-ℕ , _) →
          ex-falso
            ( is-nonempty-is-inhabited
              ( |X|)
              ( is-empty-is-zero-finite-enumeration eX refl))
        (succ-ℕ n , Fin-sn↠X) → (n , Fin-sn↠X))
      ( ∃eX)
```
