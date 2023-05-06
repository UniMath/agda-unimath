# Homomorphisms of commutative rings

```agda
module commutative-algebra.homomorphisms-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.sets
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-monoids

open import ring-theory.homomorphisms-rings
```

</details>

## Idea

A **homomorphism of commutative rings** is a homomorphism between their
underlying rings.

## Definition

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  where

  hom-Commutative-Ring : Set (l1 ⊔ l2)
  hom-Commutative-Ring =
    hom-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B)

  type-hom-Commutative-Ring : UU (l1 ⊔ l2)
  type-hom-Commutative-Ring =
    type-hom-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B)

  is-set-type-hom-Commutative-Ring : is-set type-hom-Commutative-Ring
  is-set-type-hom-Commutative-Ring =
    is-set-type-hom-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B)

  module _
    (f : type-hom-Commutative-Ring)
    where

    hom-ab-hom-Commutative-Ring :
      type-hom-Ab (ab-Commutative-Ring A) (ab-Commutative-Ring B)
    hom-ab-hom-Commutative-Ring =
      hom-ab-hom-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B) f

    hom-multiplicative-monoid-hom-Commutative-Ring :
      type-hom-Monoid
        ( multiplicative-monoid-Commutative-Ring A)
        ( multiplicative-monoid-Commutative-Ring B)
    hom-multiplicative-monoid-hom-Commutative-Ring =
      hom-multiplicative-monoid-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)
```
