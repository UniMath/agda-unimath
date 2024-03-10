# Implication

```agda
module foundation.implication where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

A type `A` {{#concept "implies" Disambiguation="types" Agda=implication}} the
type `B` if the type of maps from `A` to `B` is
[inhabited](foundation.inhabited-types.md).

```text
  A ⇒ B := ║(A → B)║₋₁
```

## Definitions

### Implications between types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  implication-prop : Prop (l1 ⊔ l2)
  implication-prop = trunc-Prop (A → B)

  implication : UU (l1 ⊔ l2)
  implication = type-Prop implication-prop

  is-prop-implication : is-prop implication
  is-prop-implication = is-prop-type-Prop implication-prop

  infixr 5 _⇒_
  _⇒_ : UU (l1 ⊔ l2)
  _⇒_ = implication
```

### The evaluation map on implications

If `A` implies `B` and `A` is inhabited, then `B` is inhabited.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  ev-implication' : (A ⇒ B) → A → ║ B ║₋₁
  ev-implication' |f| a =
    rec-trunc-Prop (trunc-Prop B) (λ f → unit-trunc-Prop (f a)) |f|

  ev-implication : (A ⇒ B) → ║ A ║₋₁ → ║ B ║₋₁
  ev-implication |f| |a| =
    rec-trunc-Prop (trunc-Prop B) (ev-implication' |f|) (|a|)
```

### Implication is a reflexive relation

```agda
module _
  {l : Level} (A : UU l)
  where

  id-implication : A ⇒ A
  id-implication = unit-trunc-Prop id
```

### Implication is a transitive relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  comp-implication : B ⇒ C → A ⇒ B → A ⇒ C
  comp-implication |g| =
    rec-trunc-Prop
      ( implication-prop A C)
      ( λ f →
        rec-trunc-Prop
          ( implication-prop A C)
          ( λ g → unit-trunc-Prop (g ∘ f))
          ( |g|))
```

## See also

- [Biimplication of types](foundation.biimplication.md)
- [Universal quantification](foundation.universal-quantification.md) for the
  dependent variant of implication.