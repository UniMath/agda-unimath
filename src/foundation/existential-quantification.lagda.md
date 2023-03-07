# Existential quantification

```agda
module foundation.existential-quantification where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Given a family of propositions `P` over `A`, the existential quantification of `P` over `A` is the proposition `∃ A P` asserting that there is an element `a : A` such that `P a` holds. We use the propositional truncation to define the existential quantification, because the Curry-Howard interpretation of the existential quantification as `Σ A P` does not guarantee that existential quantifications are interpreted as propositions.

## Definition

### Existential quantification for families of propositions

```agda
exists-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → Prop (l1 ⊔ l2)
exists-Prop {l1} {l2} A P = trunc-Prop (Σ A (λ x → type-Prop (P x)))

exists :
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → UU (l1 ⊔ l2)
exists A P = type-Prop (exists-Prop A P)

abstract
  is-prop-exists :
    {l1 l2 : Level} (A : UU l1) (P : A → Prop l2) → is-prop (exists A P)
  is-prop-exists A P = is-prop-type-Prop (exists-Prop A P)
```

### Existential quantification of arbitrary type families

```agda
∃-Prop :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → Prop (l1 ⊔ l2)
∃-Prop A B = trunc-Prop (Σ A B)

∃ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
∃ A B = type-Prop (∃-Prop A B)

is-prop-∃ :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → is-prop (∃ A B)
is-prop-∃ A B = is-prop-type-Prop (∃-Prop A B)
```

## Properties

### The introduction rule for existential quantification

```agda
intro-exists :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  (x : A) → type-Prop (P x) → exists A P
intro-exists P x p = unit-trunc-Prop (pair x p)

intro-∃ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a) →
  ∃ A B
intro-∃ a b = unit-trunc-Prop (pair a b)
```

### The elimination rule and the universal property of existential quantification

```agda
ev-intro-exists-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : A → Prop l2) (Q : Prop l3) →
  type-hom-Prop (exists-Prop A P) Q → (x : A) → type-hom-Prop (P x) Q
ev-intro-exists-Prop P Q H x p = H (intro-exists P x p)

elim-exists-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (P : A → Prop l2) (Q : Prop l3) →
  ((x : A) → type-hom-Prop (P x) Q) → type-hom-Prop (exists-Prop A P) Q
elim-exists-Prop P Q f =
  map-universal-property-trunc-Prop Q (ind-Σ f)

abstract
  is-equiv-ev-intro-exists-Prop :
    {l1 l2 l3 : Level} (A : UU l1) (P : A → Prop l2) (Q : Prop l3) →
    is-equiv (ev-intro-exists-Prop P Q)
  is-equiv-ev-intro-exists-Prop A P Q =
    is-equiv-is-prop
      ( is-prop-type-hom-Prop (exists-Prop A P) Q)
      ( is-prop-Π ((λ x → is-prop-type-hom-Prop (P x) Q)))
      ( elim-exists-Prop P Q)
```
