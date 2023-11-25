# Constant type families

```agda
module foundation.constant-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

A type family `B` over `A` is said to be **constant**, if there is a type `X`
equipped with a family of equivalences `X ≃ B a` indexed by `a : A`.

The **standard constant type family** over `A` with fiber `B` is the constant
map `const A 𝒰 B : A → 𝒰`, where `𝒰` is a universe containing `B`.

## Definitions

### The predicate of being a constant type family

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-constant-type-family : UU (l1 ⊔ lsuc l2)
  is-constant-type-family = Σ (UU l2) (λ X → (a : A) → X ≃ B a)

  module _
    (H : is-constant-type-family)
    where

    type-is-constant-type-family : UU l2
    type-is-constant-type-family = pr1 H

    equiv-is-constant-type-family : (a : A) → type-is-constant-type-family ≃ B a
    equiv-is-constant-type-family = pr2 H
```

### The (standard) constant type family

```agda
constant-type-family : {l1 l2 : Level} (A : UU l1) (B : UU l2) → A → UU l2
constant-type-family A B a = B

is-constant-type-family-constant-type-family :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  is-constant-type-family (constant-type-family A B)
pr1 (is-constant-type-family-constant-type-family A B) = B
pr2 (is-constant-type-family-constant-type-family A B) a = id-equiv
```

## Properties

### Transport in a standard constant type family

```agda
tr-constant-type-family :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {x y : A} (p : x ＝ y) (b : B) →
  dependent-identification (constant-type-family A B) p b b
tr-constant-type-family refl b = refl
```

### Dependent action on paths of sections of standard constant type families

```agda
apd-constant-type-family :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {x y : A} (p : x ＝ y) →
  apd f p ＝ (tr-constant-type-family p (f x) ∙ ap f p)
apd-constant-type-family f refl = refl
```
