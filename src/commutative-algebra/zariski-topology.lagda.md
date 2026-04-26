# The Zariski topology on the set of prime ideals in a commutative ring

```agda
module commutative-algebra.zariski-topology where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.prime-ideals-commutative-rings

open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The **Zariski topology** on the set of prime ideals in a commutative ring is
described by what the closed sets are: A subset `I` of prime ideals is closed if
it is the intersection of all the prime ideals that

## Definitions

### Closed subsets in the Zariski topology

```agda
standard-closed-subset-zariski-topology-Commutative-Ring :
  {l1 l2 l3 : Level} (A : Commutative-Ring l1) →
  subtype l3 (type-Commutative-Ring A) →
  subtype (l1 ⊔ l2 ⊔ l3) (prime-ideal-Commutative-Ring l2 A)
standard-closed-subset-zariski-topology-Commutative-Ring A U P =
  leq-prop-subtype U (subset-prime-ideal-Commutative-Ring A P)

is-closed-subset-zariski-topology-Commutative-Ring :
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (U : subtype (l1 ⊔ l2 ⊔ l3) (prime-ideal-Commutative-Ring l2 A)) →
  Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-closed-subset-zariski-topology-Commutative-Ring {l1} {l2} {l3} A U =
  exists-structure-Prop
    ( subtype l3 (type-Commutative-Ring A))
    ( λ V → standard-closed-subset-zariski-topology-Commutative-Ring A V ＝ U)

closed-subset-zariski-topology-Commutative-Ring :
  {l1 l2 : Level} (l3 : Level) (A : Commutative-Ring l1) →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
closed-subset-zariski-topology-Commutative-Ring {l1} {l2} l3 A =
  type-subtype
    ( is-closed-subset-zariski-topology-Commutative-Ring {l1} {l2} {l3} A)
```
