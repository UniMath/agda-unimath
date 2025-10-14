# Similarity of subtypes

```agda
module foundation.similarity-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.similarity-of-elements-large-posets
```

</details>

## Idea

Two [subtypes](foundation-core.subtypes.md) `P` and `Q` are said to be
{{#concept "similar" Disambiguation="subtypes" Agda=sim-subtype}} if they
contain the same elements. In other words, if `P ⊆ Q` and `Q ⊆ P`.

## Definition

### Similarity of subtypes

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l2 A) (Q : subtype l3 A)
  where

  sim-prop-subtype : Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-subtype = sim-prop-Large-Poset (powerset-Large-Poset A) P Q

  sim-subtype : UU (l1 ⊔ l2 ⊔ l3)
  sim-subtype = type-Prop sim-prop-subtype

  has-same-elements-sim-subtype :
    sim-subtype → has-same-elements-subtype P Q
  pr1 (has-same-elements-sim-subtype s x) = pr1 s x
  pr2 (has-same-elements-sim-subtype s x) = pr2 s x

  sim-has-same-elements-subtype :
    has-same-elements-subtype P Q → sim-subtype
  pr1 (sim-has-same-elements-subtype s) x = forward-implication (s x)
  pr2 (sim-has-same-elements-subtype s) x = backward-implication (s x)
```

#### Similarity is reflexive

```agda
refl-sim-subtype :
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) → sim-subtype P P
refl-sim-subtype {A = A} = refl-sim-Large-Poset (powerset-Large-Poset A)
```

#### Similarity is symmetric

```agda
symmetric-sim-subtype :
  {l1 l2 l3 : Level} {A : UU l1}
  (P : subtype l2 A) (Q : subtype l3 A) →
  sim-subtype P Q → sim-subtype Q P
symmetric-sim-subtype {A = A} =
  symmetric-sim-Large-Poset (powerset-Large-Poset A)
```

#### Similarity is transitive

```agda
transitive-sim-subtype :
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (P : subtype l2 A)
  (Q : subtype l3 A)
  (R : subtype l4 A) →
  sim-subtype Q R →
  sim-subtype P Q →
  sim-subtype P R
transitive-sim-subtype {A = A} =
  transitive-sim-Large-Poset (powerset-Large-Poset A)
```

#### Similarity is antisymmetric at the same universe level

```agda
eq-sim-subtype :
  {l1 l2 : Level} {A : UU l1} (P Q : subtype l2 A) →
  sim-subtype P Q → P ＝ Q
eq-sim-subtype {A = A} =
  eq-sim-Large-Poset (powerset-Large-Poset A)
```

### Similarity is a large similarity relation

```agda
large-similarity-relation-sim-subtype :
  {l : Level} (X : UU l) →
  Large-Similarity-Relation (λ l1 l2 → l ⊔ l1 ⊔ l2) (λ l → subtype l X)
large-similarity-relation-sim-subtype X =
  large-similarity-relation-sim-Large-Poset (powerset-Large-Poset X)
```

### A subtype is similar to itself raised to a universe level

```agda
abstract
  sim-raise-subtype :
    {l1 l2 : Level} {X : UU l1}
    (l3 : Level) (S : subtype l2 X) →
    sim-subtype S (raise-subtype l3 S)
  sim-raise-subtype _ _ = ( (λ _ → map-raise) , (λ _ → map-inv-raise))
```
