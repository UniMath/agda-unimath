# Mere logical equivalences

```agda
module foundation.mere-logical-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.mere-functions
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
  mere-iff A B := ║(A ↔ B)║₋₁
```

## Definitions

### Mere logical equivalence of types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  prop-mere-iff : Prop (l1 ⊔ l2)
  prop-mere-iff = trunc-Prop (A ↔ B)

  mere-iff : UU (l1 ⊔ l2)
  mere-iff = type-Prop prop-mere-iff

  is-prop-mere-iff : is-prop mere-iff
  is-prop-mere-iff = is-prop-type-Prop prop-mere-iff
```

## Properties

### Mere logical equivalence is a reflexive relation

```agda
module _
  {l : Level} (A : UU l)
  where

  refl-mere-iff : mere-iff A A
  refl-mere-iff = unit-trunc-Prop id-iff
```

### Mere logical equivalence is a transitive relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  transitive-mere-iff : mere-iff B C → mere-iff A B → mere-iff A C
  transitive-mere-iff |g| =
    rec-trunc-Prop
      ( prop-mere-iff A C)
      ( λ f →
        rec-trunc-Prop
          ( prop-mere-iff A C)
          ( λ g → unit-trunc-Prop (g ∘iff f))
          ( |g|))
```

### Mere logical equivalence is a symmetric relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  symmetric-mere-iff : mere-iff A B → mere-iff B A
  symmetric-mere-iff =
    rec-trunc-Prop (prop-mere-iff B A) (unit-trunc-Prop ∘ inv-iff)
```

### Merely logically equivalent types are coinhabited

If `A` and `B` are merely logically equivalent then they are
[coinhabited](foundation.coinhabited-pairs-of-types.md).

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  ev-forward-mere-iff' : mere-iff A B → A → is-inhabited B
  ev-forward-mere-iff' |f| a =
    rec-trunc-Prop
      ( trunc-Prop B)
      ( λ f → unit-trunc-Prop (forward-implication f a))
      ( |f|)

  ev-forward-mere-iff : mere-iff A B → is-inhabited A → is-inhabited B
  ev-forward-mere-iff |f| =
    rec-trunc-Prop (trunc-Prop B) (ev-forward-mere-iff' |f|)

  ev-backward-mere-iff' : mere-iff A B → B → is-inhabited A
  ev-backward-mere-iff' |f| b =
    rec-trunc-Prop
      ( trunc-Prop A)
      ( λ f → unit-trunc-Prop (backward-implication f b))
      ( |f|)

  ev-backward-mere-iff : mere-iff A B → is-inhabited B → is-inhabited A
  ev-backward-mere-iff |f| =
    rec-trunc-Prop (trunc-Prop A) (ev-backward-mere-iff' |f|)

  is-coinhabited-mere-iff : mere-iff A B → is-inhabited A ↔ is-inhabited B
  is-coinhabited-mere-iff |f| =
    ( ev-forward-mere-iff |f| , ev-backward-mere-iff |f|)
```

### Merely logically equivalent types have bidirectional mere functions

If `A` and `B` are merely logically equivalent then we have a mere function from
`A` to `B` and a mere function from `B` to `A`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  forward-mere-function-mere-iff : mere-iff A B → mere-function A B
  forward-mere-function-mere-iff =
    rec-trunc-Prop
      ( prop-mere-function A B)
      ( unit-trunc-Prop ∘ forward-implication)

  backward-mere-function-mere-iff : mere-iff A B → mere-function B A
  backward-mere-function-mere-iff =
    rec-trunc-Prop
      ( prop-mere-function B A)
      ( unit-trunc-Prop ∘ backward-implication)
```

### Mere logical equivalence is equivalent to having bidirectional mere functions

For all types we have the equivalence

```text
  (mere-iff A B) ≃ (mere-function A B × mere-function B A).
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  mutual-mere-function-mere-iff :
    mere-iff A B → mere-function A B × mere-function B A
  pr1 (mutual-mere-function-mere-iff |f|) =
    forward-mere-function-mere-iff |f|
  pr2 (mutual-mere-function-mere-iff |f|) =
    backward-mere-function-mere-iff |f|

  mere-iff-mutual-mere-function :
    mere-function A B × mere-function B A → mere-iff A B
  mere-iff-mutual-mere-function (|f| , |g|) =
    rec-trunc-Prop
      ( prop-mere-iff A B)
      ( λ f →
        rec-trunc-Prop
          ( prop-mere-iff A B)
          ( λ g → unit-trunc-Prop (f , g))
          ( |g|))
      ( |f|)

  is-equiv-mutual-mere-function-mere-iff :
    is-equiv mutual-mere-function-mere-iff
  is-equiv-mutual-mere-function-mere-iff =
    is-equiv-has-converse-is-prop
      ( is-prop-mere-iff A B)
      ( is-prop-product
        ( is-prop-mere-function A B)
        ( is-prop-mere-function B A))
      ( mere-iff-mutual-mere-function)

  is-equiv-mere-iff-mutual-mere-function :
    is-equiv mere-iff-mutual-mere-function
  is-equiv-mere-iff-mutual-mere-function =
    is-equiv-has-converse-is-prop
      ( is-prop-product
        ( is-prop-mere-function A B)
        ( is-prop-mere-function B A))
      ( is-prop-mere-iff A B)
      ( mutual-mere-function-mere-iff)

  equiv-mutual-mere-function-mere-iff :
    (mere-iff A B) ≃ (mere-function A B × mere-function B A)
  equiv-mutual-mere-function-mere-iff =
    ( mutual-mere-function-mere-iff ,
      is-equiv-mutual-mere-function-mere-iff)

  equiv-mere-iff-mutual-mere-function :
    (mere-function A B × mere-function B A) ≃ (mere-iff A B)
  equiv-mere-iff-mutual-mere-function =
    ( mere-iff-mutual-mere-function ,
      is-equiv-mere-iff-mutual-mere-function)
```

## See also

- [Mere functions](foundation.mere-functions.md)
- [Coinhabitedness](foundation.coinhabited-pairs-of-types.md) is a related but
  weaker notion than mere-iff.
