# Decidability of dependent pair types

```agda
module foundation.decidable-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.maybe
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-unit-type
open import foundation.universe-levels
```

</details>

## Idea

We describe conditions under which dependent sums are decidable.

```agda
is-decidable-Σ-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A + B → UU l3) →
  is-decidable (Σ A (C ∘ inl)) → is-decidable (Σ B (C ∘ inr)) →
  is-decidable (Σ (A + B) C)
is-decidable-Σ-coprod {l1} {l2} {l3} {A} {B} C dA dB =
  is-decidable-equiv
    ( right-distributive-Σ-coprod A B C)
    ( is-decidable-coprod dA dB)

is-decidable-Σ-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable (Σ A (B ∘ unit-Maybe)) → is-decidable (B exception-Maybe) →
  is-decidable (Σ (Maybe A) B)
is-decidable-Σ-Maybe {l1} {l2} {A} {B} dA de =
  is-decidable-Σ-coprod B dA
    ( is-decidable-equiv
      ( left-unit-law-Σ (B ∘ inr))
      ( de))

is-decidable-Σ-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ A C) → is-decidable (Σ B D)
is-decidable-Σ-equiv {D = D} e f =
  is-decidable-equiv' (equiv-Σ D e f)

is-decidable-Σ-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ B D) → is-decidable (Σ A C)
is-decidable-Σ-equiv' {D = D} e f =
  is-decidable-equiv (equiv-Σ D e f)
```
