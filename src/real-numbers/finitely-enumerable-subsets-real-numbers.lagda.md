# Finitely enumerable subsets of the real numbers

```agda
module real-numbers.finitely-enumerable-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.involutions
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.subsets-real-numbers

open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
```

</details>

## Idea

A [subset of the real numbers](real-numbers.subsets-real-numbers.md) is
{{#concept "finitely enumerable" disambiguation="subset of the real numbers" Agda=finitely-enumerable-subset-ℝ}}
if it is
[finitely enumerable](univalent-combinatorics.finitely-enumerable-subtypes.md)
as a [subtype](foundation.subtypes.md) of the
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
finitely-enumerable-subset-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
finitely-enumerable-subset-ℝ l1 l2 = finitely-enumerable-subtype l1 (ℝ l2)

module _
  {l1 l2 : Level} (S : finitely-enumerable-subset-ℝ l1 l2)
  where

  subset-finitely-enumerable-subset-ℝ : subset-ℝ l1 l2
  subset-finitely-enumerable-subset-ℝ = subtype-finitely-enumerable-subtype S

  type-finitely-enumerable-subset-ℝ : UU (l1 ⊔ lsuc l2)
  type-finitely-enumerable-subset-ℝ =
    type-subtype subset-finitely-enumerable-subset-ℝ

  is-finitely-enumerable-finitely-enumerable-subset-ℝ :
    is-finitely-enumerable-subtype subset-finitely-enumerable-subset-ℝ
  is-finitely-enumerable-finitely-enumerable-subset-ℝ =
    is-finitely-enumerable-subtype-finitely-enumerable-subtype S

  inclusion-finitely-enumerable-subset-ℝ :
    type-finitely-enumerable-subset-ℝ → ℝ l2
  inclusion-finitely-enumerable-subset-ℝ =
    inclusion-subtype subset-finitely-enumerable-subset-ℝ
```

## Properties

### The property of being inhabited

```agda
is-inhabited-finitely-enumerable-subset-ℝ :
  {l1 l2 : Level} → finitely-enumerable-subset-ℝ l1 l2 → UU (l1 ⊔ lsuc l2)
is-inhabited-finitely-enumerable-subset-ℝ =
  is-inhabited-finitely-enumerable-subtype
```

### The elementwise negation of a finitely enumerable subset of real numbers

```agda
neg-finitely-enumerable-subset-ℝ :
  {l1 l2 : Level} →
  finitely-enumerable-subset-ℝ l1 l2 → finitely-enumerable-subset-ℝ l1 l2
neg-finitely-enumerable-subset-ℝ (S , is-finitely-enumerable-S) =
  ( neg-subset-ℝ S ,
    is-finitely-enumerable-equiv
      ( equiv-precomp-equiv-type-subtype (equiv-is-involution neg-neg-ℝ) S)
      ( is-finitely-enumerable-S))
```
