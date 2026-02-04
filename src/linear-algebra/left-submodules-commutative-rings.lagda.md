# Left submodules over commutative rings

```agda
module linear-algebra.left-submodules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.left-submodules-rings
open import linear-algebra.subsets-left-modules-commutative-rings
```

</details>

## Idea

A
{{#concept "left submodule" Disambiguation="of a left module over a commutative ring" Agda=left-submodule-Commutative-Ring}}
of a [left module](linear-algebra.left-modules-commutative-rings.md) `M` over a
[commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[subset](linear-algebra.subsets-left-modules-commutative-rings.md) of `M` that
is closed under addition and multiplication by a scalar from `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (S : subset-left-module-Commutative-Ring l3 R M)
  where

  is-left-submodule-prop-Commutative-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-left-submodule-prop-Commutative-Ring =
    is-left-submodule-prop-Ring (ring-Commutative-Ring R) M S

  is-left-submodule-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-left-submodule-Commutative-Ring =
    type-Prop is-left-submodule-prop-Commutative-Ring

left-submodule-Commutative-Ring :
  {l1 l2 : Level} (l3 : Level) (R : Commutative-Ring l1) →
  left-module-Commutative-Ring l2 R → UU (l1 ⊔ l2 ⊔ lsuc l3)
left-submodule-Commutative-Ring l3 R =
  left-submodule-Ring l3 (ring-Commutative-Ring R)

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (S : left-submodule-Commutative-Ring l3 R M)
  where

  left-module-left-submodule-Commutative-Ring :
    left-module-Commutative-Ring (l2 ⊔ l3) R
  left-module-left-submodule-Commutative-Ring =
    left-module-left-submodule-Ring (ring-Commutative-Ring R) M S

  subset-left-submodule-Commutative-Ring :
    subset-left-module-Commutative-Ring l3 R M
  subset-left-submodule-Commutative-Ring =
    subset-left-submodule-Ring (ring-Commutative-Ring R) M S
```
