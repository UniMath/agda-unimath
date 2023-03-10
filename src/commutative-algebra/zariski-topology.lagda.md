# The Zariski topology on the set of prime ideals in a commutative ring

```agda
module commutative-algebra.zariski-topology where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.prime-ideals-commutative-rings

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The Zariski topology on the set of prime ideals in a commutative ring is described by what the closed sets are: A subset `I` of prime ideals is closed if it is the intersection of all the prime ideals that

## Definitions

### Closed subsets in the Zariski topology

```agda
standard-closed-subset-zariski-topology-Commutative-Ring :
  {l1 l2 l3 : Level} (R : Commutative-Ring l1) →
  subtype l3 (type-Commutative-Ring R) →
  subtype (l1 ⊔ l2 ⊔ l3) (prime-ideal-Commutative-Ring l2 R)
standard-closed-subset-zariski-topology-Commutative-Ring R U P =
  inclusion-rel-subtype-Prop U (subset-prime-ideal-Commutative-Ring R P)

is-closed-subset-zariski-topology-Commutative-Ring :
  {l1 l2 l3 : Level} (R : Commutative-Ring l1)
  (U : subtype (l1 ⊔ l2 ⊔ l3) (prime-ideal-Commutative-Ring l2 R)) →
  Prop (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-closed-subset-zariski-topology-Commutative-Ring {l1} {l2} {l3} R U =
  ∃-Prop
    ( subtype l3 (type-Commutative-Ring R))
    ( λ V →
      standard-closed-subset-zariski-topology-Commutative-Ring R V ＝ U)

closed-subset-zariski-topology-Commutative-Ring :
  {l1 l2 : Level} (l3 : Level) (R : Commutative-Ring l1) →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
closed-subset-zariski-topology-Commutative-Ring {l1} {l2} l3 R =
  type-subtype
    ( is-closed-subset-zariski-topology-Commutative-Ring {l1} {l2} {l3} R)
```
