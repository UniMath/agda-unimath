# Constant maps of pointed types

```agda
module structured-types.constant-maps-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Given a type `X` and a pointed type `A`, the constant map from `X` to `A` maps every element of `X` to the base point of `A`.

## Definition

```agda
const-Pointed-Type :
  {l1 l2 : Level} (X : UU l1) (A : Pointed-Type l2) → X → type-Pointed-Type A
const-Pointed-Type X A x = pt-Pointed-Type A

pointed-const-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) → A →* B
pr1 (pointed-const-Pointed-Type A B) =
  const-Pointed-Type (type-Pointed-Type A) B
pr2 (pointed-const-Pointed-Type A B) = refl
```
