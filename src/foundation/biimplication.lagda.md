# Biimplication of types

```agda
module foundation.biimplication where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.implication
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

The type of
{{#concept "biimplications" Disambiguation="of types" Agda=biimplication}}
between two types `A` and `B` is the
[proposition](foundation-core.propositions.md) that the type of
[logical equivalences](foundation.logical-equivalences.md) between `A` and `B`
is [inhabited](foundation.inhabited-types.md).

```text
  A ⇔ B := ║(A ↔ B)║₋₁
```

## Definitions

### The type of biimplications between `A` and `B`

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  biimplication-prop : Prop (l1 ⊔ l2)
  biimplication-prop = trunc-Prop (A ↔ B)

  biimplication : UU (l1 ⊔ l2)
  biimplication = type-Prop biimplication-prop

  is-prop-biimplication : is-prop biimplication
  is-prop-biimplication = is-prop-type-Prop biimplication-prop

  infixr 5 _⇔_
  _⇔_ : UU (l1 ⊔ l2)
  _⇔_ = biimplication
```

### The identity biimplication

```agda
module _
  {l : Level} (A : UU l)
  where

  id-biimplication : A ⇔ A
  id-biimplication = unit-trunc-Prop id-iff
```

### Composition of biimplications

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  comp-biimplication : B ⇔ C → A ⇔ B → A ⇔ C
  comp-biimplication |g| =
    rec-trunc-Prop
      ( biimplication-prop A C)
      ( λ f →
        rec-trunc-Prop
          ( biimplication-prop A C)
          ( λ g → unit-trunc-Prop (g ∘iff f))
          ( |g|))
```

### Biimplications are symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  inv-biimplication : A ⇔ B → B ⇔ A
  inv-biimplication =
    rec-trunc-Prop (biimplication-prop B A) (unit-trunc-Prop ∘ inv-iff)
```

## Properties

### Biimplied types are coinhabited

If `A` and `B` are biimplied then they are coinhabited.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  ev-forward-biimplication' : A ⇔ B → A → is-inhabited B
  ev-forward-biimplication' |f| a =
    rec-trunc-Prop
      ( trunc-Prop B)
      ( λ f → unit-trunc-Prop (forward-implication f a))
      ( |f|)

  ev-forward-biimplication : A ⇔ B → is-inhabited A → is-inhabited B
  ev-forward-biimplication |f| =
    rec-trunc-Prop (trunc-Prop B) (ev-forward-biimplication' |f|)

  ev-backward-biimplication' : A ⇔ B → B → is-inhabited A
  ev-backward-biimplication' |f| b =
    rec-trunc-Prop
      ( trunc-Prop A)
      ( λ f → unit-trunc-Prop (backward-implication f b))
      ( |f|)

  ev-backward-biimplication : A ⇔ B → is-inhabited B → is-inhabited A
  ev-backward-biimplication |f| =
    rec-trunc-Prop (trunc-Prop A) (ev-backward-biimplication' |f|)

  is-coinhabited-biimplication : A ⇔ B → is-inhabited A ↔ is-inhabited B
  is-coinhabited-biimplication |f| =
    ( ev-forward-biimplication |f| , ev-backward-biimplication |f|)
```

### Biimplied types are bidirectionally implied

If `A ⇔ B` then `A ⇒ B` and `B ⇒ A`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  forward-implication-biimplication : A ⇔ B → A ⇒ B
  forward-implication-biimplication =
    rec-trunc-Prop
      ( implication-prop A B)
      ( unit-trunc-Prop ∘ forward-implication)

  backward-implication-biimplication : A ⇔ B → B ⇒ A
  backward-implication-biimplication =
    rec-trunc-Prop
      ( implication-prop B A)
      ( unit-trunc-Prop ∘ backward-implication)
```

### Biimplication is equivalent to bidirectional implication

For all types we have the equivalence

```text
  (A ⇔ B) ≃ (A ⇒ B) × (B ⇒ A).
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  bidirectional-implication-biimplication : A ⇔ B → (A ⇒ B) × (B ⇒ A)
  pr1 (bidirectional-implication-biimplication |f|) =
    forward-implication-biimplication |f|
  pr2 (bidirectional-implication-biimplication |f|) =
    backward-implication-biimplication |f|

  biimplication-bidirectional-implication : (A ⇒ B) × (B ⇒ A) → A ⇔ B
  biimplication-bidirectional-implication (|f| , |g|) =
    rec-trunc-Prop
      ( biimplication-prop A B)
      ( λ f →
        rec-trunc-Prop
          ( biimplication-prop A B)
          ( λ g → unit-trunc-Prop (f , g))
          ( |g|))
      ( |f|)

  is-equiv-bidirectional-implication-biimplication :
    is-equiv bidirectional-implication-biimplication
  is-equiv-bidirectional-implication-biimplication =
    is-equiv-is-prop
      ( is-prop-biimplication A B)
      ( is-prop-product (is-prop-implication A B) (is-prop-implication B A))
      ( biimplication-bidirectional-implication)

  is-equiv-biimplication-bidirectional-implication :
    is-equiv biimplication-bidirectional-implication
  is-equiv-biimplication-bidirectional-implication =
    is-equiv-is-prop
      ( is-prop-product (is-prop-implication A B) (is-prop-implication B A))
      ( is-prop-biimplication A B)
      ( bidirectional-implication-biimplication)

  equiv-bidirectional-implication-biimplication : (A ⇔ B) ≃ ((A ⇒ B) × (B ⇒ A))
  equiv-bidirectional-implication-biimplication =
    ( bidirectional-implication-biimplication ,
      is-equiv-bidirectional-implication-biimplication)

  equiv-biimplication-bidirectional-implication : ((A ⇒ B) × (B ⇒ A)) ≃ (A ⇔ B)
  equiv-biimplication-bidirectional-implication =
    ( biimplication-bidirectional-implication ,
      is-equiv-biimplication-bidirectional-implication)
```

## See also

- [Implication of types](foundation.implication.md)
