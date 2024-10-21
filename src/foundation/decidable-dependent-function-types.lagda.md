# Decidability of dependent function types

```agda
module foundation.decidable-dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.functoriality-dependent-function-types
open import foundation.maybe
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.negation
```

</details>

## Idea

We describe conditions under which
[dependent function types](foundation.dependent-function-types.md) are
[decidable](foundation.decidable-types.md).

## Properties

### Decidability of dependent products of uniformly decidable families

```agda
is-decidable-Π-uniformly-decidable-family :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-decidable A →
  (((a : A) → B a) + ((a : A) → ¬ (B a))) →
  is-decidable ((a : A) → (B a))
is-decidable-Π-uniformly-decidable-family (inl a) (inl b) =
  inl b
is-decidable-Π-uniformly-decidable-family (inl a) (inr b) =
  inr (λ f → b a (f a))
is-decidable-Π-uniformly-decidable-family (inr na) _ =
  inl (ex-falso ∘ na)
```

### Decidablitilty of dependent products over coproducts

```agda
is-decidable-Π-coproduct :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A + B → UU l3} →
  is-decidable ((a : A) → C (inl a)) → is-decidable ((b : B) → C (inr b)) →
  is-decidable ((x : A + B) → C x)
is-decidable-Π-coproduct {C = C} dA dB =
  is-decidable-equiv
    ( equiv-dependent-universal-property-coproduct C)
    ( is-decidable-product dA dB)
```

### Decidability of dependent products over `Maybe`

```agda
is-decidable-Π-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable ((x : A) → B (unit-Maybe x)) →
  is-decidable (B exception-Maybe) →
  is-decidable ((x : Maybe A) → B x)
is-decidable-Π-Maybe {B = B} du de =
  is-decidable-equiv
    ( equiv-dependent-universal-property-Maybe B)
    ( is-decidable-product du de)
```

### Decidability of dependent products over an equivalence

```agda
is-decidable-Π-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((x : A) → C x) → is-decidable ((y : B) → D y)
is-decidable-Π-equiv {D = D} e f = is-decidable-equiv' (equiv-Π D e f)

is-decidable-Π-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((y : B) → D y) → is-decidable ((x : A) → C x)
is-decidable-Π-equiv' {D = D} e f = is-decidable-equiv (equiv-Π D e f)
```
