# Isomorphisms of commutative rings

```agda
module commutative-algebra.isomorphisms-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import ring-theory.isomorphisms-rings
```

</details>

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
    ( commutative-mul-Commutative-Ring R1)
```
