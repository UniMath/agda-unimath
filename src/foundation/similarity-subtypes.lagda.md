# Similarity of subtypes

```agda
module foundation.similarity-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.identity-types
open import foundation.large-locale-of-propositions
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.sets

open import order-theory.bottom-elements-large-posets
open import order-theory.bottom-elements-posets
open import order-theory.dependent-products-large-meet-semilattices
open import order-theory.dependent-products-large-posets
open import order-theory.dependent-products-large-preorders
open import order-theory.dependent-products-large-suplattices
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-suplattices
open import order-theory.meet-semilattices
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.similarity-of-elements-large-posets
open import order-theory.suplattices
open import order-theory.top-elements-large-posets
open import order-theory.top-elements-posets
```

</details>

## Idea

two [subtypes](foundation-core.subtypes.md) `P` and `Q` are said to be
{{#concept "similar" Disambiguation="subtypes" Agda=sim-subtype}} if they
contain the same elements. In other words, if `x ∈ P ⇔ x ∈ Q`.

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
module _
  {l1 : Level} {A : UU l1}
  where

  refl-sim-subtype : {l2 : Level} → (P : subtype l2 A) → sim-subtype P P
  refl-sim-subtype = refl-sim-Large-Poset (powerset-Large-Poset A)
```

#### Similarity is symmetric

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  symmetric-sim-subtype :
    {l2 l3 : Level} →
    (P : subtype l2 A) (Q : subtype l3 A) →
    sim-subtype P Q → sim-subtype Q P
  symmetric-sim-subtype = symmetric-sim-Large-Poset (powerset-Large-Poset A)
```

#### Similarity is transitive

```agda
  transitive-sim-subtype :
    {l2 l3 l4 : Level} →
    (P : subtype l2 A) →
    (Q : subtype l3 A) →
    (R : subtype l4 A) →
    sim-subtype Q R →
    sim-subtype P Q →
    sim-subtype P R
  transitive-sim-subtype = transitive-sim-Large-Poset (powerset-Large-Poset A)
```

#### Similarity is antisymmetric at the same universe level

```agda
  eq-sim-subtype :
    {l2 : Level} →
    (P Q : subtype l2 A) →
    sim-subtype P Q →
    P ＝ Q
  eq-sim-subtype = eq-sim-Large-Poset (powerset-Large-Poset A)
```
