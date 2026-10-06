# Trivial left modules over rings

```agda
module linear-algebra.trivial-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subuniverse-of-contractible-types
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.trivial-groups

open import linear-algebra.left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

The
{{#concept "trivial module" Disambiguation="over a ring" Agda=trivial-left-module-Ring}}
over a [ring](ring-theory.rings.md) `R` is the
[left module](linear-algebra.left-modules-rings.md) over `R` consisting of
exactly one element, `0`.

## Definition

### The property of being a trivial module

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  is-trivial-prop-left-module-Ring : Prop l2
  is-trivial-prop-left-module-Ring = is-contr-Prop (type-left-module-Ring R M)

  is-trivial-left-module-Ring : UU l2
  is-trivial-left-module-Ring = type-Prop is-trivial-prop-left-module-Ring
```

### The trivial module

```agda
module _
  {l : Level}
  (R : Ring l)
  where

  trivial-left-module-Ring : left-module-Ring lzero R
  trivial-left-module-Ring =
    make-left-module-Ring
      ( R)
      ( trivial-Ab)
      ( λ _ _ → star)
      ( λ _ _ _ → refl)
      ( λ _ _ _ → refl)
      ( λ _ → refl)
      ( λ _ _ _ → refl)

  is-trivial-trivial-left-module-Ring :
    is-trivial-left-module-Ring R trivial-left-module-Ring
  is-trivial-trivial-left-module-Ring = is-contr-unit
```
