# Pushouts

```agda
module synthetic-homotopy-theory.pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Postulates

```agda
postulate
  pushout :
    {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) → UU (l1 ⊔ l2 ⊔ l3)

postulate
  inl-pushout :
    {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) → A → pushout f g

postulate
  inr-pushout :
    {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) → B → pushout f g

postulate
  glue-pushout :
    {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) → ((inl-pushout f g) ∘ f) ~ ((inr-pushout f g) ∘ g)

cocone-pushout :
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) → cocone f g (pushout f g)
cocone-pushout f g =
  pair
    ( inl-pushout f g)
    ( pair
      ( inr-pushout f g)
      ( glue-pushout f g))

postulate
  up-pushout :
    {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) →
    universal-property-pushout l4 f g (cocone-pushout f g)

equiv-up-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (Z : UU l4) → ((pushout f g) → Z) ≃ (cocone f g Z)
equiv-up-pushout f g Z = (cocone-map f g (cocone-pushout f g)) , (up-pushout f g Z)
```

## Definitions

### The cogap map

```agda
cogap :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  { X : UU l4} (c : cocone f g X) → pushout f g → X
cogap f g =
  map-universal-property-pushout f g
    ( cocone-pushout f g)
    ( up-pushout f g)
```

### The `is-pushout` predicate

```agda
is-pushout :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-pushout f g c = is-equiv (cogap f g c)
```
