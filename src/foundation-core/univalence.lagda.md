# The univalence axiom

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.univalence where

open import foundation-core.contractible-types using (is-contr)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( _≃_; id-equiv; is-equiv; map-equiv)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id; fundamental-theorem-id')
open import foundation-core.homotopies using (_~_; refl-htpy)
open import foundation-core.identity-types using (Id; refl; ap; tr)
open import foundation-core.universe-levels using (Level; UU; lsuc)
```

## Idea

The univalence axiom characterizes the identity types of universes. It asserts that the map `Id A B → A ≃ B` is an equivalence.

## Definition

```agda
equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq refl = id-equiv

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})
```

## Properties

### The univalence axiom implies that the total space of equivalences is contractible

```agda
abstract
  is-contr-total-equiv-UNIVALENCE : {i : Level} (A : UU i) →
    ((B : UU i) → UNIVALENCE A B) → is-contr (Σ (UU i) (λ X → A ≃ X))
  is-contr-total-equiv-UNIVALENCE A UA =
    fundamental-theorem-id' A id-equiv (λ B → equiv-eq) UA
```

### Contractibility of the total space of equivalences implies univalence

```agda
abstract
  UNIVALENCE-is-contr-total-equiv : {i : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X)) → (B : UU i) → UNIVALENCE A B
  UNIVALENCE-is-contr-total-equiv A c =
    fundamental-theorem-id A id-equiv c (λ B → equiv-eq)
```

### Computing transport

```agda
tr-equiv-eq-ap : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  (p : Id x y) → (map-equiv (equiv-eq (ap B p))) ~ tr B p
tr-equiv-eq-ap refl = refl-htpy
```
