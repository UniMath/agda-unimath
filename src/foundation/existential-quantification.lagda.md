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
of `P` over `A` is the proposition `∃ A P` asserting that there is an element
`a : A` such that `P a` holds. We use the
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

  ∃-Prop : Prop (l1 ⊔ l2)
  ∃-Prop = trunc-Prop (Σ A B)

  ∃ : UU (l1 ⊔ l2)
  ∃ = type-Prop ∃-Prop

  is-prop-∃ : is-prop ∃
  is-prop-∃ = is-prop-type-Prop ∃-Prop
```

### Existential quantification on predicates

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  exists-Prop : Prop (l1 ⊔ l2)
  exists-Prop = ∃-Prop A (type-Prop ∘ P)

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
  {l1 l2 : Level} {A : UU l1}
  where

  intro-∃ : {B : A → UU l2} (a : A) (b : B a) → ∃ A B
  intro-∃ a b = unit-trunc-Prop (a , b)

  intro-exists : (P : A → Prop l2) (x : A) → type-Prop (P x) → exists A P
  intro-exists P = intro-∃
```

### The elimination rule and the universal property of existential quantification

The
{{#concept "universal property" Disambiguation="of existential quantification"}}
of existential quantification states `∃ A P` is the least upper bound on the
family `P` in the
[poset of propositions](foundation.large-locale-of-propositions.md).

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : A → Prop l2) (Q : Prop l3)
  where

  ev-intro-exists-Prop :
    type-Prop (((∃₍₋₁₎ A P) →₍₋₁₎ Q) →₍₋₁₎ Π₍₋₁₎ A (λ x → (P x) →₍₋₁₎ Q))
  ev-intro-exists-Prop H x p = H (intro-exists P x p)

  elim-exists-Prop :
    type-Prop (Π₍₋₁₎ A (λ x → (P x) →₍₋₁₎ Q) →₍₋₁₎ (∃₍₋₁₎ A P) →₍₋₁₎ Q)
  elim-exists-Prop f =
    map-universal-property-trunc-Prop Q (ind-Σ f)

  abstract
    is-equiv-ev-intro-exists-Prop : is-equiv ev-intro-exists-Prop
    is-equiv-ev-intro-exists-Prop =
      is-equiv-Prop'
        ( ∃₍₋₁₎ A P →₍₋₁₎ Q)
        ( Π₍₋₁₎ A (λ x → P x →₍₋₁₎ Q))
        ( elim-exists-Prop)

  is-least-upper-bound-exists-Prop :
    ((a : A) → type-hom-Prop (P a) Q) ↔ type-hom-Prop (exists-Prop A P) Q
  is-least-upper-bound-exists-Prop = (elim-exists-Prop , ev-intro-exists-Prop)
```

### Conjunction distributes over existential quatification

```agda
module _
  {l1 l2 l3 : Level} (P : Prop l1) {A : UU l2} (Q : A → Prop l3)
  where

  map-distributive-conjunction-exists-Prop :
    type-Prop (P ∧₍₋₁₎ (∃₍₋₁₎ A Q) →₍₋₁₎ ∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x))
  map-distributive-conjunction-exists-Prop (p , e) =
    elim-exists-Prop Q
      ( ∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x))
      ( λ x q → intro-∃ x (p , q))
      ( e)

  map-inv-distributive-conjunction-exists-Prop :
    type-Prop (∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x) →₍₋₁₎ P ∧₍₋₁₎ (∃₍₋₁₎ A Q))
  map-inv-distributive-conjunction-exists-Prop =
    elim-exists-Prop
      ( λ x → P ∧₍₋₁₎ Q x)
      ( P ∧₍₋₁₎ (∃₍₋₁₎ A Q))
      ( λ x (p , q) → (p , intro-∃ x q))

  iff-distributive-conjunction-exists-Prop :
    type-Prop (P ∧₍₋₁₎ ∃₍₋₁₎ A Q ↔₍₋₁₎ ∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x))
  iff-distributive-conjunction-exists-Prop =
    ( map-distributive-conjunction-exists-Prop ,
      map-inv-distributive-conjunction-exists-Prop)

  eq-distributive-conjunction-exists-Prop :
    P ∧₍₋₁₎ (∃₍₋₁₎ A Q) ＝ ∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x)
  eq-distributive-conjunction-exists-Prop =
    eq-iff'
      ( P ∧₍₋₁₎ (∃₍₋₁₎ A Q))
      ( ∃₍₋₁₎ A (λ x → P ∧₍₋₁₎ Q x))
      ( iff-distributive-conjunction-exists-Prop)
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
