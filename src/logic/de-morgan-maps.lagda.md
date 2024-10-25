# De Morgan maps

```agda
module logic.de-morgan-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.negation
open import logic.de-morgan-types
open import foundation.universal-property-equivalences
open import foundation.dependent-pair-types
open import foundation.double-negation
open import logic.double-negation-elimination
open import foundation.empty-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.retractions
open import foundation.retracts-of-maps
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be
{{#concept "De Morgan" Disambiguation="map of types" Agda=is-de-morgan-map}} if
the [negation](foundation-core.negation.md) of its
[fibers](foundation-core.fibers-of-maps.md) are
[decidable](foundation.decidable-types.md). I.e., for every `y : B`, if
`fiber f y` is either [empty](foundation.empty-types.md) or
[irrefutable](foundation.irrefutable-propositions.md).

## Definintion

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-de-morgan-map : (A → B) → UU (l1 ⊔ l2)
  is-de-morgan-map f =
    (y : B) → is-decidable (¬ (fiber f y))
```

## Properties

### De Morgan maps are closed under homotopy

```agda
abstract
  is-de-morgan-map-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g →
    is-de-morgan-map g →
    is-de-morgan-map f
  is-de-morgan-map-htpy H K b =
    is-decidable-equiv'
      ( equiv-precomp (equiv-tot (λ a → equiv-concat (inv (H a)) b)) empty)
      ( K b)
```

### Decidable maps are De Morgan

```agda
is-de-morgan-map-is-decidable-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-decidable-map f → is-de-morgan-map f
is-de-morgan-map-is-decidable-map H y = is-decidable-neg-is-decidable (H y)
```

### Composition of De Morgan maps

Given a composition `g ∘ f` of De Morgan maps where the left factor `g` is
injective, then the composition is De Morgan.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  -- fiber-left-is-de-morgan-map-left :
  --   is-de-morgan-map g →
  --   (z : C) → ¬¬ (fiber (g ∘ f) z) → fiber g z
  -- fiber-left-is-de-morgan-map-left G z nngfz = ?
  --   -- G z (λ x → nngfz (λ w → x (f (pr1 w) , pr2 w)))

  -- fiber-right-is-de-morgan-map-comp :
  --   is-injective g →
  --   (G : is-de-morgan-map g) →
  --   is-de-morgan-map f →
  --   (z : C) (nngfz : ¬¬ (fiber (g ∘ f) z)) →
  --   fiber f (pr1 (fiber-left-is-de-morgan-map-left G z nngfz))
  -- fiber-right-is-de-morgan-map-comp H G F z nngfz =
  --   F ( pr1
  --       ( fiber-left-is-de-morgan-map-left G z nngfz))
  --         ( λ x →
  --           nngfz
  --             ( λ w →
  --               x ( pr1 w ,
  --                   H ( pr2 w ∙
  --                       inv
  --                         ( pr2
  --                           ( fiber-left-is-de-morgan-map-left
  --                               G z nngfz))))))

  is-de-morgan-map-comp :
    is-injective g →
    is-de-morgan-map g →
    is-de-morgan-map f →
    is-de-morgan-map (g ∘ f)
  is-de-morgan-map-comp H G F z = {!   !}
    -- map-inv-compute-fiber-comp g f z
    --   ( ( fiber-left-is-de-morgan-map-left G z nngfz) ,
    --     ( fiber-right-is-de-morgan-map-comp H G F z nngfz))
```

### Left cancellation for De Morgan maps

If a composite `g ∘ f` is De Morgan and the left factor `g` is injective, then
the right factor `f` is De Morgan.

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  (GF : is-de-morgan-map (g ∘ f))
  where

  fiber-comp-is-de-morgan-map-right-factor' :
    (y : B) → ¬¬ (fiber f y) → Σ (fiber g (g y)) (λ t → fiber f (pr1 t))
  fiber-comp-is-de-morgan-map-right-factor' y nnfy =
    map-compute-fiber-comp g f (g y)
      ( GF (g y) (λ ngfgy → nnfy λ x → ngfgy ((pr1 x) , ap g (pr2 x))))

  is-de-morgan-map-right-factor' :
    is-injective g → is-de-morgan-map f
  is-de-morgan-map-right-factor' G y nnfy =
    tr
      ( fiber f)
      ( G ( pr2
            ( pr1
              ( fiber-comp-is-de-morgan-map-right-factor'
                ( y)
                ( nnfy)))))
      ( pr2
        ( fiber-comp-is-de-morgan-map-right-factor' y nnfy))
```

### Any map out of the empty type is De Morgan

```text
abstract
  is-de-morgan-map-ex-falso :
    {l : Level} {X : UU l} →
    is-de-morgan-map (ex-falso {l} {X})
  is-de-morgan-map-ex-falso x f = ex-falso (f λ ())
```

### The identity map is De Morgan

```text
abstract
  is-de-morgan-map-id :
    {l : Level} {X : UU l} → is-de-morgan-map (id {l} {X})
  is-de-morgan-map-id x y = (x , refl)
```

### Equivalences are De Morgan maps

```text
abstract
  is-de-morgan-map-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-de-morgan-map f
  is-de-morgan-map-is-equiv H x =
    double-negation-elim-is-contr (is-contr-map-is-equiv H x)
```

### The map on total spaces induced by a family of De Morgan maps is De Morgan

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-de-morgan-map-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-de-morgan-map (f x)) →
    is-de-morgan-map (tot f)
  is-de-morgan-map-tot {f} H x =
    has-double-negation-elim-equiv (compute-fiber-tot f x) (H (pr1 x) (pr2 x))
```

### The map on total spaces induced by a De Morgan map on the base is De Morgan

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  is-de-morgan-map-Σ-map-base :
    {f : A → B} →
    is-de-morgan-map f →
    is-de-morgan-map (map-Σ-map-base f C)
  is-de-morgan-map-Σ-map-base {f} H x =
    has-double-negation-elim-equiv'
      ( compute-fiber-map-Σ-map-base f C x)
      ( H (pr1 x))
```

### Products of De Morgan maps are De Morgan

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-de-morgan-map-product :
    {f : A → B} {g : C → D} →
    is-de-morgan-map f →
    is-de-morgan-map g →
    is-de-morgan-map (map-product f g)
  is-de-morgan-map-product {f} {g} F G x =
    has-double-negation-elim-equiv
      ( compute-fiber-map-product f g x)
      ( double-negation-elim-product (F (pr1 x)) (G (pr2 x)))
```

### Coproducts of De Morgan maps are De Morgan

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-de-morgan-map-coproduct :
    {f : A → B} {g : C → D} →
    is-de-morgan-map f →
    is-de-morgan-map g →
    is-de-morgan-map (map-coproduct f g)
  is-de-morgan-map-coproduct {f} {g} F G (inl x) =
    has-double-negation-elim-equiv'
      ( compute-fiber-inl-map-coproduct f g x)
      ( F x)
  is-de-morgan-map-coproduct {f} {g} F G (inr y) =
    has-double-negation-elim-equiv'
      ( compute-fiber-inr-map-coproduct f g y)
      ( G y)
```

### De Morgan maps are closed under base change

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : C → D}
  where

  is-de-morgan-map-base-change :
    cartesian-hom-arrow g f →
    is-de-morgan-map f →
    is-de-morgan-map g
  is-de-morgan-map-base-change α F d =
    has-double-negation-elim-equiv
      ( equiv-fibers-cartesian-hom-arrow g f α d)
      ( F (map-codomain-cartesian-hom-arrow g f α d))
```

### De Morgan maps are closed under retracts of maps

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y}
  where

  is-de-morgan-retract-map :
    f retract-of-map g →
    is-de-morgan-map g →
    is-de-morgan-map f
  is-de-morgan-retract-map R G x =
    has-double-negation-elim-retract
      ( retract-fiber-retract-map f g R x)
      ( G (map-codomain-inclusion-retract-map f g R x))
```
