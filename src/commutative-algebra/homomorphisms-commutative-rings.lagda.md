# Homomorphisms of commutative rings

```agda
module commutative-algebra.homomorphisms-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
```

</details>

## Idea

A **homomorphism of commutative rings** is a homomorphism between their
underlying rings.

## Definition

```agda
type-hom-Commutative-Ring :
  { l1 l2 : Level} → Commutative-Ring l1 → Commutative-Ring l2 → UU (l1 ⊔ l2)
type-hom-Commutative-Ring A B =
  type-hom-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B)
```
