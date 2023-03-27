# Trivial commutative rings

```agda
module commutative-algebra.trivial-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.rings
open import ring-theory.trivial-rings
```

</details>

## Idea

Trivial commutative rings are commutative rings in which `0 = 1`.

## Definition

```agda
is-trivial-commutative-ring-Prop :
  {l : Level} → Commutative-Ring l → Prop l
is-trivial-commutative-ring-Prop R =
  Id-Prop
    ( set-Commutative-Ring R)
    ( zero-Commutative-Ring R)
    ( one-Commutative-Ring R)

is-trivial-Commutative-Ring :
  {l : Level} → Commutative-Ring l → UU l
is-trivial-Commutative-Ring R =
  type-Prop (is-trivial-commutative-ring-Prop R)

is-prop-is-trivial-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-prop (is-trivial-Commutative-Ring R)
is-prop-is-trivial-Commutative-Ring R =
  is-prop-type-Prop (is-trivial-commutative-ring-Prop R)

is-nontrivial-commutative-ring-Prop :
  {l : Level} → Commutative-Ring l → Prop l
is-nontrivial-commutative-ring-Prop R =
  neg-Prop (is-trivial-commutative-ring-Prop R)

is-nontrivial-Commutative-Ring :
  {l : Level} → Commutative-Ring l → UU l
is-nontrivial-Commutative-Ring R =
  type-Prop (is-nontrivial-commutative-ring-Prop R)

is-prop-is-nontrivial-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-prop (is-nontrivial-Commutative-Ring R)
is-prop-is-nontrivial-Commutative-Ring R =
  is-prop-type-Prop (is-nontrivial-commutative-ring-Prop R)
```

## Properties

### The carrier type of a zero commutative ring is contractible

```agda
is-contr-is-trivial-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-trivial-Commutative-Ring R →
  is-contr (type-Commutative-Ring R)
is-contr-is-trivial-Commutative-Ring R p =
  is-contr-is-trivial-Ring (ring-Commutative-Ring R) p
```
