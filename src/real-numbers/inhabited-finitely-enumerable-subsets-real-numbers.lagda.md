# Inhabited finitely enumerable subsets of the real numbers

```agda
module real-numbers.inhabited-finitely-enumerable-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.inhabited-types
open import foundation.involutions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.finitely-enumerable-subsets-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.subsets-real-numbers

open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
open import univalent-combinatorics.inhabited-finitely-enumerable-subtypes
```

</details>

## Idea

An
{{#concept "inhabited finitely enumerable subset" Agda=inhabited-finitely-enumerable-subtype}}
of the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[subtype](foundation.subtypes.md) of `ℝ` that is
[inhabited and finitely enumerable](univalent-combinatorics.inhabited-finitely-enumerable-subtypes.md).

## Definition

```agda
inhabited-finitely-enumerable-subset-ℝ :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
inhabited-finitely-enumerable-subset-ℝ l1 l2 =
  inhabited-finitely-enumerable-subtype l1 (ℝ l2)

module _
  {l1 l2 : Level} (S : inhabited-finitely-enumerable-subset-ℝ l1 l2)
  where

  subset-inhabited-finitely-enumerable-subset-ℝ : subset-ℝ l1 l2
  subset-inhabited-finitely-enumerable-subset-ℝ =
    subtype-inhabited-finitely-enumerable-subtype S

  type-inhabited-finitely-enumerable-subset-ℝ : UU (l1 ⊔ lsuc l2)
  type-inhabited-finitely-enumerable-subset-ℝ =
    type-inhabited-finitely-enumerable-subtype S

  is-finitely-enumerable-inhabited-finitely-enumerable-subset-ℝ :
    is-finitely-enumerable-subtype subset-inhabited-finitely-enumerable-subset-ℝ
  is-finitely-enumerable-inhabited-finitely-enumerable-subset-ℝ =
    is-finitely-enumerable-type-inhabited-finitely-enumerable-subtype S

  inclusion-inhabited-finitely-enumerable-subset-ℝ :
    type-inhabited-finitely-enumerable-subset-ℝ → ℝ l2
  inclusion-inhabited-finitely-enumerable-subset-ℝ =
    inclusion-subtype subset-inhabited-finitely-enumerable-subset-ℝ

  is-inhabited-inhabited-finitely-enumerable-subset-ℝ :
    is-inhabited type-inhabited-finitely-enumerable-subset-ℝ
  is-inhabited-inhabited-finitely-enumerable-subset-ℝ =
    is-inhabited-type-inhabited-finitely-enumerable-subtype S
```

## Properties

### The elementwise negation of an inhabited finitely enumerable subset of real numbers

```agda
neg-inhabited-finitely-enumerable-subset-ℝ :
  {l1 l2 : Level} →
  inhabited-finitely-enumerable-subset-ℝ l1 l2 →
  inhabited-finitely-enumerable-subset-ℝ l1 l2
neg-inhabited-finitely-enumerable-subset-ℝ (S , |S|) =
  ( neg-finitely-enumerable-subset-ℝ S ,
    map-is-inhabited
      ( map-equiv
        ( equiv-precomp-equiv-type-subtype
          ( equiv-is-involution neg-neg-ℝ)
          ( subset-finitely-enumerable-subset-ℝ S)))
      ( |S|))
```
