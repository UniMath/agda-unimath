# Trivial left modules over commutative rings

```agda
module linear-algebra.trivial-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.trivial-left-modules-rings
```

</details>

## Idea

The
{{#concept "trivial module" Disambiguation="over a commutative ring" Agda=trivial-left-module-Commutative-Ring}}
over a [commutative ring](commutative-algebra.commutative-rings.md) `R` is the
[left module](linear-algebra.left-modules-commutative-rings.md) over `R`
consisting of exactly one element, `0`.

## Definition

### The property of being a trivial module

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  is-trivial-prop-left-module-Commutative-Ring : Prop l2
  is-trivial-prop-left-module-Commutative-Ring =
    is-trivial-prop-left-module-Ring (ring-Commutative-Ring R) M

  is-trivial-left-module-Commutative-Ring : UU l2
  is-trivial-left-module-Commutative-Ring =
    type-Prop is-trivial-prop-left-module-Commutative-Ring
```

### The trivial module

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  where

  trivial-left-module-Commutative-Ring : left-module-Commutative-Ring lzero R
  trivial-left-module-Commutative-Ring =
    trivial-left-module-Ring (ring-Commutative-Ring R)

  is-trivial-trivial-left-module-Commutative-Ring :
    is-trivial-left-module-Commutative-Ring
      ( R)
      ( trivial-left-module-Commutative-Ring)
  is-trivial-trivial-left-module-Commutative-Ring =
    is-trivial-trivial-left-module-Ring (ring-Commutative-Ring R)
```
