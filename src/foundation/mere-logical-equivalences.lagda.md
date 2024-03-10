# Mere logical equivalences

```agda
module foundation.mere-logical-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.mere-logical-consequences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

Two types `A` and `B` are
{{#concept "merely logically equivalent" Disambiguation="types" Agda=mere-iff}}
if the type of [logical equivalences](foundation.logical-equivalences.md)
between `A` and `B` is [inhabited](foundation.inhabited-types.md).

```text
  A ⇔ B := ║(A ↔ B)║₋₁
```

## Definitions

### Mere logical equivalence of types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  mere-iff-prop : Prop (l1 ⊔ l2)
  mere-iff-prop = trunc-Prop (A ↔ B)

  mere-iff : UU (l1 ⊔ l2)
  mere-iff = type-Prop mere-iff-prop

  is-prop-mere-iff : is-prop mere-iff
  is-prop-mere-iff = is-prop-type-Prop mere-iff-prop

  infixr 5 _⇔_
  _⇔_ : UU (l1 ⊔ l2)
  _⇔_ = mere-iff
```

## Properties

### Mere logical equivalence is a reflexive relation

```agda
module _
  {l : Level} (A : UU l)
  where

  refl-mere-iff : A ⇔ A
  refl-mere-iff = unit-trunc-Prop id-iff
```

### Mere logical equivalence is a transitive relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  trans-mere-iff : B ⇔ C → A ⇔ B → A ⇔ C
  trans-mere-iff |g| =
    rec-trunc-Prop
      ( mere-iff-prop A C)
      ( λ f →
        rec-trunc-Prop
          ( mere-iff-prop A C)
          ( λ g → unit-trunc-Prop (g ∘iff f))
          ( |g|))
```

### Mere logical equivalence is a symmetric relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  sym-mere-iff : A ⇔ B → B ⇔ A
  sym-mere-iff =
    rec-trunc-Prop (mere-iff-prop B A) (unit-trunc-Prop ∘ inv-iff)
```

### Merely logically equivalent types are coinhabited

If `A` and `B` are merely logically equivalent then they are
[coinhabited](foundation.coinhabited-types.md).

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  ev-forward-mere-iff' : A ⇔ B → A → is-inhabited B
  ev-forward-mere-iff' |f| a =
    rec-trunc-Prop
      ( trunc-Prop B)
      ( λ f → unit-trunc-Prop (forward-implication f a))
      ( |f|)

  ev-forward-mere-iff : A ⇔ B → is-inhabited A → is-inhabited B
  ev-forward-mere-iff |f| =
    rec-trunc-Prop (trunc-Prop B) (ev-forward-mere-iff' |f|)

  ev-backward-mere-iff' : A ⇔ B → B → is-inhabited A
  ev-backward-mere-iff' |f| b =
    rec-trunc-Prop
      ( trunc-Prop A)
      ( λ f → unit-trunc-Prop (backward-implication f b))
      ( |f|)

  ev-backward-mere-iff : A ⇔ B → is-inhabited B → is-inhabited A
  ev-backward-mere-iff |f| =
    rec-trunc-Prop (trunc-Prop A) (ev-backward-mere-iff' |f|)

  is-coinhabited-mere-iff : A ⇔ B → is-inhabited A ↔ is-inhabited B
  is-coinhabited-mere-iff |f| =
    ( ev-forward-mere-iff |f| , ev-backward-mere-iff |f|)
```

### Merely logically equivalent types are mutual logical consequences

If `A ⇔ B` then `A ⇒ B` and `B ⇒ A`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  forward-mere-consequence-mere-iff : A ⇔ B → A ⇒ B
  forward-mere-consequence-mere-iff =
    rec-trunc-Prop
      ( mere-consequence-prop A B)
      ( unit-trunc-Prop ∘ forward-implication)

  backward-mere-consequence-mere-iff : A ⇔ B → B ⇒ A
  backward-mere-consequence-mere-iff =
    rec-trunc-Prop
      ( mere-consequence-prop B A)
      ( unit-trunc-Prop ∘ backward-implication)
```

### Mere logical equivalence is equivalent to mutual mere logical consequence

For all types we have the equivalence

```text
  (A ⇔ B) ≃ (A ⇒ B) × (B ⇒ A).
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  mutual-mere-consequence-mere-iff : A ⇔ B → (A ⇒ B) × (B ⇒ A)
  pr1 (mutual-mere-consequence-mere-iff |f|) =
    forward-mere-consequence-mere-iff |f|
  pr2 (mutual-mere-consequence-mere-iff |f|) =
    backward-mere-consequence-mere-iff |f|

  mere-iff-mutual-mere-consequence : (A ⇒ B) × (B ⇒ A) → A ⇔ B
  mere-iff-mutual-mere-consequence (|f| , |g|) =
    rec-trunc-Prop
      ( mere-iff-prop A B)
      ( λ f →
        rec-trunc-Prop
          ( mere-iff-prop A B)
          ( λ g → unit-trunc-Prop (f , g))
          ( |g|))
      ( |f|)

  is-equiv-mutual-mere-consequence-mere-iff :
    is-equiv mutual-mere-consequence-mere-iff
  is-equiv-mutual-mere-consequence-mere-iff =
    is-equiv-is-prop
      ( is-prop-mere-iff A B)
      ( is-prop-product
        ( is-prop-mere-consequence A B)
        ( is-prop-mere-consequence B A))
      ( mere-iff-mutual-mere-consequence)

  is-equiv-mere-iff-mutual-mere-consequence :
    is-equiv mere-iff-mutual-mere-consequence
  is-equiv-mere-iff-mutual-mere-consequence =
    is-equiv-is-prop
      ( is-prop-product
        ( is-prop-mere-consequence A B)
        ( is-prop-mere-consequence B A))
      ( is-prop-mere-iff A B)
      ( mutual-mere-consequence-mere-iff)

  equiv-mutual-mere-consequence-mere-iff : (A ⇔ B) ≃ ((A ⇒ B) × (B ⇒ A))
  equiv-mutual-mere-consequence-mere-iff =
    ( mutual-mere-consequence-mere-iff ,
      is-equiv-mutual-mere-consequence-mere-iff)

  equiv-mere-iff-mutual-mere-consequence : ((A ⇒ B) × (B ⇒ A)) ≃ (A ⇔ B)
  equiv-mere-iff-mutual-mere-consequence =
    ( mere-iff-mutual-mere-consequence ,
      is-equiv-mere-iff-mutual-mere-consequence)
```

## See also

- [Mere logical consequences](foundation.mere-logical-consequences.md)
- [Coinhabitedness](foundation.coinhabited-types.md) is a related but weaker
  notion than mere-iff.
