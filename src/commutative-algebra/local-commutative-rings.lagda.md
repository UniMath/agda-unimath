# Local commutative rings

```agda
module commutative-algebra.local-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.invertible-elements-commutative-rings

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.invertible-elements-rings
open import ring-theory.local-rings
open import ring-theory.nontrivial-rings
open import ring-theory.rings
```

</details>

## Idea

A local ring is a ring such that whenever a sum of elements is invertible, then one of its summands is invertible. This implies that the non-invertible elements form an ideal. However, the law of excluded middle is needed to show that any ring of which the non-invertible elements form an ideal is a local ring.

## Definition

```agda
is-local-commutative-ring-Prop :
  {l : Level} (R : Commutative-Ring l) → Prop l
is-local-commutative-ring-Prop R = is-local-ring-Prop (ring-Commutative-Ring R)

is-local-Commutative-Ring : {l : Level} → Commutative-Ring l → UU l
is-local-Commutative-Ring R = is-local-Ring (ring-Commutative-Ring R)

is-prop-is-local-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → is-prop (is-local-Commutative-Ring R)
is-prop-is-local-Commutative-Ring R =
  is-prop-is-local-Ring (ring-Commutative-Ring R)

Local-Commutative-Ring : (l : Level) → UU (lsuc l)
Local-Commutative-Ring l = Σ (Commutative-Ring l) is-local-Commutative-Ring

module _
  {l : Level} (R : Local-Commutative-Ring l)
  where

  commutative-ring-Local-Commutative-Ring : Commutative-Ring l
  commutative-ring-Local-Commutative-Ring = pr1 R

  ring-Local-Commutative-Ring : Ring l
  ring-Local-Commutative-Ring =
    ring-Commutative-Ring commutative-ring-Local-Commutative-Ring

  set-Local-Commutative-Ring : Set l
  set-Local-Commutative-Ring = set-Ring ring-Local-Commutative-Ring

  type-Local-Commutative-Ring : UU l
  type-Local-Commutative-Ring =
    type-Ring ring-Local-Commutative-Ring

  is-local-commutative-ring-Local-Commutative-Ring :
    is-local-Commutative-Ring commutative-ring-Local-Commutative-Ring
  is-local-commutative-ring-Local-Commutative-Ring = pr2 R
```
