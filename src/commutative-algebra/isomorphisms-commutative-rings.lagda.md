---
title: Isomorphisms of commutative rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module commutative-algebra.isomorphisms-commutative-rings where

open import commutative-algebra.commutative-rings using
  ( Commutative-Ring; ring-Commutative-Ring; is-prop-is-commutative-Ring;
    is-commutative-Commutative-Ring)

open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import ring-theory.isomorphisms-rings using
  ( iso-Ring; is-contr-total-iso-Ring; id-iso-Ring)
```

## Definition

```agda
iso-Commutative-Ring :
  { l1 l2 : Level} → Commutative-Ring l1 → Commutative-Ring l2 → UU (l1 ⊔ l2)
iso-Commutative-Ring R1 R2 = iso-Ring (ring-Commutative-Ring R1) (ring-Commutative-Ring R2)

is-contr-total-iso-Commutative-Ring :
  { l1 : Level} (R1 : Commutative-Ring l1) →
  is-contr (Σ (Commutative-Ring l1) (iso-Commutative-Ring R1))
is-contr-total-iso-Commutative-Ring R1 =
  is-contr-total-Eq-subtype
    ( is-contr-total-iso-Ring (ring-Commutative-Ring R1))
    ( is-prop-is-commutative-Ring)
    ( ring-Commutative-Ring R1)
    ( id-iso-Ring (ring-Commutative-Ring R1))
    ( is-commutative-Commutative-Ring R1)
```
