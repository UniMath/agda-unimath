# Trivial commutative rings

```agda
module commutative-algebra.trivial-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.contractible-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.trivial-rings
```

</details>

## Idea

**Trivial commutative rings** are commutative rings in which `0 = 1`.

## Definition

```agda
is-trivial-commutative-ring-Prop :
  {l : Level} → Commutative-Ring l → Prop l
is-trivial-commutative-ring-Prop A =
  Id-Prop
    ( set-Commutative-Ring A)
    ( zero-Commutative-Ring A)
    ( one-Commutative-Ring A)

is-trivial-Commutative-Ring :
  {l : Level} → Commutative-Ring l → UU l
is-trivial-Commutative-Ring A =
  type-Prop (is-trivial-commutative-ring-Prop A)

is-prop-is-trivial-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-prop (is-trivial-Commutative-Ring A)
is-prop-is-trivial-Commutative-Ring A =
  is-prop-type-Prop (is-trivial-commutative-ring-Prop A)

is-nontrivial-commutative-ring-Prop :
  {l : Level} → Commutative-Ring l → Prop l
is-nontrivial-commutative-ring-Prop A =
  neg-Prop (is-trivial-commutative-ring-Prop A)

is-nontrivial-Commutative-Ring :
  {l : Level} → Commutative-Ring l → UU l
is-nontrivial-Commutative-Ring A =
  type-Prop (is-nontrivial-commutative-ring-Prop A)

is-prop-is-nontrivial-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-prop (is-nontrivial-Commutative-Ring A)
is-prop-is-nontrivial-Commutative-Ring A =
  is-prop-type-Prop (is-nontrivial-commutative-ring-Prop A)
```

## Properties

### The carrier type of a zero commutative ring is contractible

```agda
is-contr-is-trivial-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) →
  is-trivial-Commutative-Ring A →
  is-contr (type-Commutative-Ring A)
is-contr-is-trivial-Commutative-Ring A p =
  is-contr-is-trivial-Ring (ring-Commutative-Ring A) p
```
