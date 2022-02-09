# Existential quantification

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.existential-quantification where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; ind-Σ)
open import foundation.equivalences using (is-equiv)
open import foundation.propositional-truncations using
  ( trunc-Prop; unit-trunc-Prop; map-universal-property-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-type-Prop; type-hom-Prop;
    is-equiv-is-prop; is-prop-type-hom-Prop; is-prop-Π)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

Given a family of propositions `P` over `A`, the existential quantification of `P` over `A` is the proposition `∃ A P` asserting that there is an element `a : A` such that `P a` holds. We use the propositional truncation to define the existential quantification, because the Curry-Howard interpretation of the existential quantification as `Σ A P` does not guarantee that existential quantifications are interpreted as propositions.

## Definition

### Existential quantification for families of propositions

```agda
exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU-Prop (l1 ⊔ l2)
exists-Prop {l1} {l2} {A} P = trunc-Prop (Σ A (λ x → type-Prop (P x)))

exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
exists P = type-Prop (exists-Prop P)

abstract
  is-prop-exists :
    {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → is-prop (exists P)
  is-prop-exists P = is-prop-type-Prop (exists-Prop P)
```

### Existential quantification of arbitrary type families

```agda
∃-Prop :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU-Prop (l1 ⊔ l2)
∃-Prop {A = A} B = trunc-Prop (Σ A B)

∃ :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
∃ B = type-Prop (∃-Prop B)

is-prop-∃ :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → is-prop (∃ B)
is-prop-∃ B = is-prop-type-Prop (∃-Prop B)
```

## Properties

### The introduction rule for existential quantification

```agda
intro-exists :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  (x : A) → type-Prop (P x) → exists P
intro-exists {A = A} P x p = unit-trunc-Prop (pair x p)

intro-∃ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a) →
  ∃ B
intro-∃ a b = unit-trunc-Prop (pair a b)
```

### The elimination rule and the universal property of existential quantification

```agda
ev-intro-exists-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : A → UU-Prop l2) (Q : UU-Prop l3) →
  type-hom-Prop (exists-Prop P) Q → (x : A) → type-hom-Prop (P x) Q
ev-intro-exists-Prop P Q H x p = H (intro-exists P x p)

elim-exists-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : A → UU-Prop l2) (Q : UU-Prop l3) →
  ((x : A) → type-hom-Prop (P x) Q) → type-hom-Prop (exists-Prop P) Q
elim-exists-Prop {A = A} P Q f =
  map-universal-property-trunc-Prop Q (ind-Σ f)

abstract
  is-equiv-ev-intro-exists-Prop :
    {l1 l2 l3 : Level} {A : UU l1} (P : A → UU-Prop l2) (Q : UU-Prop l3) →
    is-equiv (ev-intro-exists-Prop P Q)
  is-equiv-ev-intro-exists-Prop P Q =
    is-equiv-is-prop
      ( is-prop-type-hom-Prop (exists-Prop P) Q)
      ( is-prop-Π ((λ x → is-prop-type-hom-Prop (P x) Q)))
      ( elim-exists-Prop P Q)
```
