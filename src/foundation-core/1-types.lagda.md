# `1`-Types

```agda
module foundation-core.1-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Definition

A 1-type is a type that is 1-truncated.

```agda
is-1-type : {l : Level} → UU l → UU l
is-1-type = is-trunc one-𝕋

1-Type : (l : Level) → UU (lsuc l)
1-Type l = Σ (UU l) is-1-type

type-1-Type : {l : Level} → 1-Type l → UU l
type-1-Type = pr1

abstract
  is-1-type-type-1-Type :
    {l : Level} (A : 1-Type l) → is-1-type (type-1-Type A)
  is-1-type-type-1-Type = pr2
```

## Properties

### The identity type of a 1-type takes values in sets

```agda
Id-Set : {l : Level} (X : 1-Type l) (x y : type-1-Type X) → Set l
pr1 (Id-Set X x y) = (x ＝ y)
pr2 (Id-Set X x y) = is-1-type-type-1-Type X x y
```

### Any set is a 1-type

```agda
1-type-Set :
  {l : Level} → Set l → 1-Type l
1-type-Set A = truncated-type-succ-Truncated-Type zero-𝕋 A
```

### The 1-types are closed under equivalences

```agda
abstract
  is-1-type-is-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (f : A → B) → is-equiv f →
    is-1-type B → is-1-type A
  is-1-type-is-equiv = is-trunc-is-equiv one-𝕋

abstract
  is-1-type-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (e : A ≃ B) →
    is-1-type B → is-1-type A
  is-1-type-equiv = is-trunc-equiv one-𝕋

abstract
  is-1-type-is-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (f : A → B) →
    is-equiv f → is-1-type A → is-1-type B
  is-1-type-is-equiv' = is-trunc-is-equiv' one-𝕋

abstract
  is-1-type-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (e : A ≃ B) →
    is-1-type A → is-1-type B
  is-1-type-equiv' = is-trunc-equiv' one-𝕋
```
