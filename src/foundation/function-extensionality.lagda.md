# Function extensionality

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module foundation.function-extensionality where

open import foundation-core.function-extensionality public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-homotopies
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.transport
```

</details>

## Idea

The [function extensionality axiom](foundation-core.function-extensionality.md)
asserts that [identifications](foundation-core.identity-types.md) of (dependent)
functions are [equivalently](foundation-core.equivalences.md) described as
pointwise equalities between them. In other words, a function is completely
determined by its values.

We postulated the function extensionality axiom in
[`foundation-core.function-extensionality`](foundation-core.function-extensionality.md).
In this file, we will derive some elementary properties of the identification
`eq-htpy H` obtained from a homotopy `H`.

## Properties

### Transporting along identifications of the form `eq-htpy H`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  where

  dependent-homotopy-htpy-eq :
    {f g : (x : A) → B x} (p : f ＝ g) (h : (x : A) → C x (f x)) →
    dependent-homotopy C (htpy-eq p) h (tr (λ u → (x : A) → C x (u x)) p h)
  dependent-homotopy-htpy-eq refl h = refl-htpy

  dependent-homotopy-eq-htpy :
    {f g : (x : A) → B x} (H : f ~ g) (h : (x : A) → C x (f x)) →
    dependent-homotopy C H h (tr (λ u → (x : A) → C x (u x)) (eq-htpy H) h)
  dependent-homotopy-eq-htpy H h =
    ( htpy-eq (ap (λ K → tr-htpy C K h) (inv (is-section-eq-htpy H)))) ∙h
    ( dependent-homotopy-htpy-eq (eq-htpy H) h)

  dependent-homotopy-eq-htpy-refl-htpy :
    {f : (x : A) → B x} (h : (x : A) → C x (f x)) → {!!}
    {-
    tr-eq-htpy (refl-htpy {f = f}) h ~
    htpy-eq
      ( ap (λ p → tr (λ u → (x : A) → C x (u x)) p h) (eq-htpy-refl-htpy f)) -}
  dependent-homotopy-eq-htpy-refl-htpy h = {!!}
```

## See also

- That the univalence axiom implies function extensionality is proven in
  [`foundation.univalence-implies-function-extensionality`](foundation.univalence-implies-function-extensionality.md).
- Weak function extensionality is defined in
  [`foundation.weak-function-extensionality`](foundation.weak-function-extensionality.md).
