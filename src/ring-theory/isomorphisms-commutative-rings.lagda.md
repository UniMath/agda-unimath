---
title: Isomorphisms of commutative rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.isomorphisms-commutative-rings where

open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import ring-theory.commutative-rings using
  ( Comm-Ring; ring-Comm-Ring; is-prop-is-commutative-Ring;
    is-commutative-Comm-Ring)
open import ring-theory.isomorphisms-rings using
  ( iso-Ring; is-contr-total-iso-Ring; id-iso-Ring)
```

## Definition

```agda
iso-Comm-Ring :
  { l1 l2 : Level} → Comm-Ring l1 → Comm-Ring l2 → UU (l1 ⊔ l2)
iso-Comm-Ring R1 R2 = iso-Ring (ring-Comm-Ring R1) (ring-Comm-Ring R2)

is-contr-total-iso-Comm-Ring :
  { l1 : Level} (R1 : Comm-Ring l1) →
  is-contr (Σ (Comm-Ring l1) (iso-Comm-Ring R1))
is-contr-total-iso-Comm-Ring R1 =
  is-contr-total-Eq-subtype
    ( is-contr-total-iso-Ring (ring-Comm-Ring R1))
    ( is-prop-is-commutative-Ring)
    ( ring-Comm-Ring R1)
    ( id-iso-Ring (ring-Comm-Ring R1))
    ( is-commutative-Comm-Ring R1)
```
