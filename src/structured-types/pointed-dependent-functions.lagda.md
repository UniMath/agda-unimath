# Pointed dependent functions

```agda
module structured-types.pointed-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-families-of-types
open import structured-types.pointed-types
```

</details>

## Idea

A pointed dependent function of a pointed family `B` over `A` is a dependent function of the underlying family taking the base point of `A` to the base point of `B`.

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  where

  pointed-Π : UU (l1 ⊔ l2)
  pointed-Π =
    fib (ev-pt (pt-Pointed-Type A) (fam-Pointed-Fam A B)) (pt-Pointed-Fam A B)

  function-pointed-Π :
    pointed-Π → (x : type-Pointed-Type A) → fam-Pointed-Fam A B x
  function-pointed-Π f = pr1 f

  preserves-point-function-pointed-Π :
    (f : pointed-Π) →
    Id (function-pointed-Π f (pt-Pointed-Type A)) (pt-Pointed-Fam A B)
  preserves-point-function-pointed-Π f = pr2 f
```
