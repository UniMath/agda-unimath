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
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
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
pr1 (cocone-pushout f g) = inl-pushout f g
pr1 (pr2 (cocone-pushout f g)) = inr-pushout f g
pr2 (pr2 (cocone-pushout f g)) = glue-pushout f g

postulate
  up-pushout :
    {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
    (f : S → A) (g : S → B) →
    universal-property-pushout l4 f g (cocone-pushout f g)

equiv-up-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) (X : UU l4) → (pushout f g → X) ≃ (cocone f g X)
pr1 (equiv-up-pushout f g X) = cocone-map f g (cocone-pushout f g)
pr2 (equiv-up-pushout f g X) = up-pushout f g X
```

## Definitions

### The cogap map

```agda
cogap :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  { X : UU l4} → cocone f g X → pushout f g → X
cogap f g {X} = map-inv-equiv (equiv-up-pushout f g X)
```

### The `is-pushout` predicate

```agda
is-pushout :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-pushout f g c = is-equiv (cogap f g c)
```

## Properties

### Computation with the cogap map

```agda
compute-inl-cogap :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  { X : UU l4} (c : cocone f g X)
  ( a : A) → cogap f g c (inl-pushout f g a) ＝ horizontal-map-cocone f g c a
compute-inl-cogap f g c =
  pr1
    ( htpy-cocone-map-universal-property-pushout
      ( f)
      ( g)
      ( cocone-pushout f g)
      ( up-pushout f g)
      ( c))

compute-inr-cogap :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  { X : UU l4} (c : cocone f g X)
  ( b : B) → cogap f g c (inr-pushout f g b) ＝ vertical-map-cocone f g c b
compute-inr-cogap f g c =
  pr1
    ( pr2
      ( htpy-cocone-map-universal-property-pushout
        ( f)
        ( g)
        ( cocone-pushout f g)
        ( up-pushout f g)
        ( c)))

compute-glue-cogap :
  { l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  ( f : S → A) (g : S → B) →
  { X : UU l4} (c : cocone f g X)
  ( s : S) →
  ( ap (cogap f g c) (glue-pushout f g s)) ＝
  ( ( compute-inl-cogap f g c (f s) ∙ coherence-square-cocone f g c s) ∙
    ( inv (compute-inr-cogap f g c (g s))))
compute-glue-cogap f g c s =
  con-inv
    ( ap (cogap f g c) (glue-pushout f g s))
    ( compute-inr-cogap f g c (g s))
    ( compute-inl-cogap f g c (f s) ∙ coherence-square-cocone f g c s)
    ( pr2
      ( pr2
        ( htpy-cocone-map-universal-property-pushout
          ( f)
          ( g)
          ( cocone-pushout f g)
          ( up-pushout f g)
          ( c)))
      ( s))
```
