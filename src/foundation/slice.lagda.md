---
title: Morphisms of the slice category of types
---

```agda
module foundation.slice where

open import foundation-core.slice public

open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.universe-levels

open import foundation.homotopies
open import foundation.structure-identity-principle
open import foundation.univalence
```

## Idea

The slice of a category over an object X is the category of morphisms into X. A morphism in the slice from `f : A → X` to `g : B → X` consists of a function `h : A → B` such that the triangle `f ~ g ∘ h` commutes. We make these definitions for types.

## Properties

### Univalence in a slice

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  abstract
    is-contr-total-equiv-slice' :
      (f : Slice l2 A) → is-contr (Σ (Slice l2 A) (equiv-slice' f))
    is-contr-total-equiv-slice' (pair X f) =
      is-contr-total-Eq-structure
        ( λ Y g e → f ~ (g ∘ map-equiv e))
        ( is-contr-total-equiv X)
        ( pair X id-equiv)
        ( is-contr-total-htpy f)

  abstract
    is-equiv-equiv-eq-Slice :
      (f g : Slice l2 A) → is-equiv (equiv-eq-Slice f g)
    is-equiv-equiv-eq-Slice f =
      fundamental-theorem-id
        ( is-contr-total-equiv-slice' f)
        ( equiv-eq-Slice f)

  extensionality-Slice :
    (f g : Slice l2 A) → (f ＝ g) ≃ equiv-slice' f g
  extensionality-Slice f g =
    (equiv-eq-Slice f g) , (is-equiv-equiv-eq-Slice f g)

  eq-equiv-slice :
    (f g : Slice l2 A) → equiv-slice' f g → f ＝ g
  eq-equiv-slice f g =
    map-inv-is-equiv (is-equiv-equiv-eq-Slice f g)
```

## See also

- For the formally dual notion see
  [foundation.coslice](foundation.coslice.html).
- For slices in the context of category theory see
  [category-theory.slice-precategories](category-theory.slice-precategories.html).
- For fibered maps see
  [foundation.fibered-maps](foundation.fibered-maps.html).
