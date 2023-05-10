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

## Idea

An **isomorphism** of commutative rings is an invertible homomorphism of
commutative rings.

## Definition

```agda
iso-Commutative-Ring :
  { l1 l2 : Level} → Commutative-Ring l1 → Commutative-Ring l2 → UU (l1 ⊔ l2)
iso-Commutative-Ring A B =
  iso-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B)

is-contr-total-iso-Commutative-Ring :
  { l1 : Level} (A : Commutative-Ring l1) →
  is-contr (Σ (Commutative-Ring l1) (iso-Commutative-Ring A))
is-contr-total-iso-Commutative-Ring A =
  is-contr-total-Eq-subtype
    ( is-contr-total-iso-Ring (ring-Commutative-Ring A))
    ( is-prop-is-commutative-Ring)
    ( ring-Commutative-Ring A)
    ( id-iso-Ring (ring-Commutative-Ring A))
    ( commutative-mul-Commutative-Ring A)
```
