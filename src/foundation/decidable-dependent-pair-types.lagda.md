# Decidability of dependent pair types

```agda
module foundation.decidable-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.maybe
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-unit-type
open import foundation.uniformly-decidable-type-families
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.negation
```

</details>

## Idea

We describe conditions under which
[dependent sums](foundation.dependent-pair-types.md) are
[decidable](foundation.decidable-types.md)

## Properites

### Dependent sums of a uniformly decidable family of types

```agda
is-decidable-Σ-uniformly-decidable-family :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-decidable A →
  is-uniformly-decidable-family B →
  is-decidable (Σ A B)
is-decidable-Σ-uniformly-decidable-family (inl a) (inl b) =
  inl (a , b a)
is-decidable-Σ-uniformly-decidable-family (inl a) (inr b) =
  inr (λ x → b (pr1 x) (pr2 x))
is-decidable-Σ-uniformly-decidable-family (inr a) _ =
  inr (λ x → a (pr1 x))
```

### Decidability of dependent sums over coproducts

```agda
is-decidable-Σ-coproduct :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A + B → UU l3) →
  is-decidable (Σ A (C ∘ inl)) → is-decidable (Σ B (C ∘ inr)) →
  is-decidable (Σ (A + B) C)
is-decidable-Σ-coproduct {A = A} {B} C dA dB =
  is-decidable-equiv
    ( right-distributive-Σ-coproduct A B C)
    ( is-decidable-coproduct dA dB)
```

### Decidability of dependent sums over `Maybe`

```agda
is-decidable-Σ-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable (Σ A (B ∘ unit-Maybe)) → is-decidable (B exception-Maybe) →
  is-decidable (Σ (Maybe A) B)
is-decidable-Σ-Maybe {A = A} {B} dA de =
  is-decidable-Σ-coproduct B dA
    ( is-decidable-equiv (left-unit-law-Σ (B ∘ inr)) de)
```

### Decidability of dependent sums over equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x))
  where

  is-decidable-Σ-equiv : is-decidable (Σ A C) → is-decidable (Σ B D)
  is-decidable-Σ-equiv = is-decidable-equiv' (equiv-Σ D e f)

  is-decidable-Σ-equiv' : is-decidable (Σ B D) → is-decidable (Σ A C)
  is-decidable-Σ-equiv' = is-decidable-equiv (equiv-Σ D e f)
```
