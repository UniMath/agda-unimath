# Crisp injective maps

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-injective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
```

</details>

## Idea

A crisp map `f : @♭ A → B` is
{{#concept "crisp injective" Agda=is-crisp-injective}} if for all crisp `x` and
`y` and crisp `f x ＝ f y` we can show that `x ＝ y`. This stands in contrast to
{{#concept "crisply injective" Agda=is-crisply-injective}} maps, which are crisp
maps `f : A → B` such that for all crisp `x` and `y` and crisp `f x ＝ f y` we
can show that `x ＝ y`.

## Definitions

### Crisp injective maps

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  is-crisp-injective : (@♭ f : @♭ A → B) → UU (l1 ⊔ l2)
  is-crisp-injective f = {@♭ x y : A} → @♭ (f x ＝ f y) → x ＝ y
```

### Crisply injective maps

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  is-crisply-injective : (@♭ f : A → B) → UU (l1 ⊔ l2)
  is-crisply-injective f = {@♭ x y : A} → @♭ f x ＝ f y → x ＝ y
```

## Properties

### The flat constructor is crisp injective

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  is-crisp-injective-cons-flat : is-crisp-injective (cons-flat {A = A})
  is-crisp-injective-cons-flat p = ap counit-flat p
```

### The flat counit is crisply injective

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  is-crisply-injective-counit-flat : is-crisply-injective (counit-flat {A = A})
  is-crisply-injective-counit-flat {cons-flat x} {cons-flat y} p =
    crisp-ap cons-flat p
```
