# Pointed dependent functions

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.pointed-dependent-functions where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import synthetic-homotopy-theory.pointed-families-of-types using
  ( Pointed-Fam; fam-Pointed-Fam; pt-Pointed-Fam)
open import synthetic-homotopy-theory.pointed-types using
  ( Pointed-Type; type-Pointed-Type; pt-Pointed-Type)
```

## Idea

A pointed dependent function of a pointed family `B` over `A` is a dependent function of the underlying family taking the base point of `A` to the base point of `B`.

```agda
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  where

  pointed-Π : UU (l1 ⊔ l2)
  pointed-Π =
    Σ ( (x : type-Pointed-Type A) → fam-Pointed-Fam A B x)
      ( λ f → Id (f (pt-Pointed-Type A)) (pt-Pointed-Fam A B))

  function-pointed-Π :
    pointed-Π → (x : type-Pointed-Type A) → fam-Pointed-Fam A B x
  function-pointed-Π f = pr1 f

  preserves-point-function-pointed-Π :
    (f : pointed-Π) →
    Id (function-pointed-Π f (pt-Pointed-Type A)) (pt-Pointed-Fam A B)
  preserves-point-function-pointed-Π f = pr2 f
```
