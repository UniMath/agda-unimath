# Pointed families of types

```agda
module structured-types.pointed-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

A pointed family of types over a pointed type `A` is a family of types `B` over the underlying type of `A` equipped with a base point over the base point of `A`. Note that a pointed family of types should not be confused with a family of pointed types over `A`.

## Definition

```agda
Pointed-Fam :
  {l1 : Level} (l : Level) (A : Pointed-Type l1) → UU (lsuc l ⊔ l1)
Pointed-Fam l A = Σ (type-Pointed-Type A → UU l) (λ P → P (pt-Pointed-Type A))

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  where

  fam-Pointed-Fam : type-Pointed-Type A → UU l2
  fam-Pointed-Fam = pr1 B

  pt-Pointed-Fam : fam-Pointed-Fam (pt-Pointed-Type A)
  pt-Pointed-Fam = pr2 B
```

## Examples

### The constant pointed family

```agda
module _
  {l1 l2 : Level}
  where

  constant-Pointed-Fam :
    (A : Pointed-Type l1) → Pointed-Type l2 → Pointed-Fam l2 A
  constant-Pointed-Fam A B =
    pair (λ x → type-Pointed-Type B) (pt-Pointed-Type B)
```
