# Finite bases of left modules over rings

```agda
module linear-algebra.finite-bases-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.bases-left-modules-rings
open import linear-algebra.left-modules-rings

open import ring-theory.rings

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (basis@(I , b , is-basis-b) : basis-left-module-Ring l3 R M)
  where

  is-finite-prop-basis-left-module-Ring : Prop l3
  is-finite-prop-basis-left-module-Ring = is-finite-Prop I

  is-finite-basis-left-module-Ring : UU l3
  is-finite-basis-left-module-Ring = is-finite I

module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  basis-fin-sequence-left-module-Ring : ℕ → UU (l1 ⊔ l2)
  basis-fin-sequence-left-module-Ring n =
    type-subtype (is-indexed-basis-prop-left-module-Ring R M (Fin n))
```
