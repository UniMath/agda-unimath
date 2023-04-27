# Pointed dependent pair types

```agda
module structured-types.pointed-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-families-of-types
open import structured-types.pointed-types
```

</details>

## Idea

Given a pointed type `(A , a)` and a pointed family over it `(B , b)`, then the
dependent pair type `Σ A B` is again canonically pointed at `(a , b)`.

## Definition

```agda
module _
  {l1 l2 : Level}
  where

  Σ-Pointed-Type :
    (A : Pointed-Type l1) (B : Pointed-Fam l2 A) → Pointed-Type (l1 ⊔ l2)
  pr1 (Σ-Pointed-Type (A , a) (B , b)) = Σ A B
  pr2 (Σ-Pointed-Type (A , a) (B , b)) = a , b

  Σ* = Σ-Pointed-Type
```
