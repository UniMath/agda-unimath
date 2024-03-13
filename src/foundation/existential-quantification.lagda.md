# Existential quantification

```agda
module foundation.existential-quantification where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Given a family of [propositions](foundation-core.propositions.md) `P` over `A`,
the
{{#concept "existential quantification" Disambiguation="on a subtype" Agda=exists}}
of `P` over `A` is the proposition `exists-type-family A P` asserting that there
is an element `a : A` such that `P a` holds. We use the
[propositional truncation](foundation.propositional-truncations.md) to define
the existential quantification, because the Curry-Howard interpretation of the
existential quantification as `Σ A P` does not guarantee that existential
quantifications are interpreted as propositions.

## Definition

### Existential quantification on arbitrary type families

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  exists-type-family-Prop : Prop (l1 ⊔ l2)
  exists-type-family-Prop = trunc-Prop (Σ A B)

  exists-type-family : UU (l1 ⊔ l2)
  exists-type-family = type-Prop exists-type-family-Prop

  is-prop-exists-type-family : is-prop exists-type-family
  is-prop-exists-type-family = is-prop-type-Prop exists-type-family-Prop
```

### Existential quantification

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  exists-Prop : Prop (l1 ⊔ l2)
  exists-Prop = exists-type-family-Prop A (type-Prop ∘ P)

  exists : UU (l1 ⊔ l2)
  exists = type-Prop exists-Prop

  abstract
    is-prop-exists : is-prop exists
    is-prop-exists = is-prop-type-Prop exists-Prop

  ∃₍₋₁₎ : Prop (l1 ⊔ l2)
  ∃₍₋₁₎ = exists-Prop
```

## Properties

### The introduction rule for existential quantification

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  intro-exists : (a : A) (b : B a) → exists-type-family A B
  intro-exists a b = unit-trunc-Prop (a , b)
```

### The elimination rule and the universal property of existential quantification

The
{{#concept "universal property" Disambiguation="of existential quantification"}}
of existential quantification states `∃ A P` is the least upper bound on the
predicate `P` in the
[poset of propositions](foundation.large-locale-of-propositions.md).

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  ev-intro-exists :
    {C : UU l3} → (exists-type-family A B → C) → (x : A) → (B x) → C
  ev-intro-exists H x p = H (intro-exists x p)

  elim-exists :
    (Q : Prop l3) →
    ((x : A) → (B x) → type-Prop Q) → (exists-type-family A B → type-Prop Q)
  elim-exists Q f = map-universal-property-trunc-Prop Q (ind-Σ f)

  abstract
    is-equiv-ev-intro-exists :
      (Q : Prop l3) → is-equiv (ev-intro-exists {type-Prop Q})
    is-equiv-ev-intro-exists Q =
      is-equiv-Prop'
        ( function-Prop (exists-type-family A B) Q)
        ( Π-Prop A (λ x → function-Prop (B x) Q))
        ( elim-exists Q)

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : A → Prop l2) (Q : Prop l3)
  where

  is-least-upper-bound-exists-Prop :
    type-Prop (Π₍₋₁₎ A (λ x → P x →₍₋₁₎ Q) ↔₍₋₁₎ ((∃₍₋₁₎ A P) →₍₋₁₎ Q))
  is-least-upper-bound-exists-Prop = (elim-exists Q , ev-intro-exists)
```

### Taking the cartesian product with a proposition distributes over existential quantification on arbitrary type families

```agda
module _
  {l1 l2 l3 : Level} (P : Prop l1) {A : UU l2} {B : A → UU l3}
  where

  map-distributive-product-exists :
    type-Prop P × exists-type-family A B →
    exists-type-family A (λ x → type-Prop P × B x)
  map-distributive-product-exists (p , e) =
    elim-exists
      ( exists-type-family-Prop A (λ x → type-Prop P × B x))
      ( λ x q → intro-exists x (p , q))
      ( e)

  map-inv-distributive-product-exists :
    exists-type-family A (λ x → type-Prop P × B x) →
    type-Prop P × exists-type-family A B
  map-inv-distributive-product-exists =
    elim-exists
      ( P ∧₍₋₁₎ exists-type-family-Prop A B)
      ( λ x (p , q) → (p , intro-exists x q))

  iff-distributive-product-exists :
    ( type-Prop P × exists-type-family A B) ↔
    ( exists-type-family A (λ x → type-Prop P × B x))
  iff-distributive-product-exists =
    ( map-distributive-product-exists ,
      map-inv-distributive-product-exists)

  eq-distributive-product-exists :
    P ∧₍₋₁₎ exists-type-family-Prop A B ＝
    exists-type-family-Prop A (λ x → type-Prop P × B x)
  eq-distributive-product-exists =
    eq-iff'
      ( P ∧₍₋₁₎ exists-type-family-Prop A B)
      ( exists-type-family-Prop A (λ x → type-Prop P × B x))
      ( iff-distributive-product-exists)
```

### Conjunction distributes over existential quantification

```agda
module _
  {l1 l2 l3 : Level} (P : Prop l1) {A : UU l2} (Q : A → Prop l3)
  where

  map-distributive-conjunction-exists-Prop :
    type-Prop (P ∧₍₋₁₎ (∃₍₋₁₎ A Q) →₍₋₁₎ ∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x))
  map-distributive-conjunction-exists-Prop =
    map-distributive-product-exists P

  map-inv-distributive-conjunction-exists-Prop :
    type-Prop (∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x) →₍₋₁₎ P ∧₍₋₁₎ (∃₍₋₁₎ A Q))
  map-inv-distributive-conjunction-exists-Prop =
    map-inv-distributive-product-exists P

  iff-distributive-conjunction-exists-Prop :
    type-Prop (P ∧₍₋₁₎ ∃₍₋₁₎ A Q ↔₍₋₁₎ ∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x))
  iff-distributive-conjunction-exists-Prop =
    iff-distributive-product-exists P

  eq-distributive-conjunction-exists-Prop :
    P ∧₍₋₁₎ (∃₍₋₁₎ A Q) ＝ ∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x)
  eq-distributive-conjunction-exists-Prop =
    eq-distributive-product-exists P
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
