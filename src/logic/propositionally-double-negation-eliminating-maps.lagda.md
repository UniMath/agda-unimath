# Propositionally double negation eliminating maps

```agda
module logic.propositionally-double-negation-eliminating-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
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

open import logic.double-negation-eliminating-maps
open import logic.double-negation-elimination
open import logic.propositional-double-negation-elimination
open import logic.propositionally-decidable-maps
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be
{{#concept "propositionally double negation eliminating" Disambiguation="map of types" Agda=is-prop-double-negation-eliminating-map}}
if its [fibers](foundation-core.fibers-of-maps.md) satisfy
[propositional double negation elimination](logic.propositional-double-negation-elimination.md).
I.e., for every `y : B`, if `fiber f y` is
[irrefutable](foundation.irrefutable-propositions.md), then we do in fact have
then the fiber is in fact inhabited. In other words, double negation eliminating
maps come [equipped](foundation.structure.md) with a map

```text
  (y : B) → ¬¬ (fiber f y) → ║ fiber f y ║₋₁.
```

## Definintion

### Double negation elimination structure on a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-double-negation-eliminating-map : (A → B) → UU (l1 ⊔ l2)
  is-prop-double-negation-eliminating-map f =
    (y : B) → has-prop-double-negation-elim (fiber f y)

  is-property-is-prop-double-negation-eliminating-map :
    {f : A → B} → is-prop (is-prop-double-negation-eliminating-map f)
  is-property-is-prop-double-negation-eliminating-map {f} =
    is-prop-Π (λ y → is-prop-has-prop-double-negation-elim (fiber f y))

  is-prop-double-negation-eliminating-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-prop-double-negation-eliminating-map-Prop f =
    is-prop-double-negation-eliminating-map f ,
    is-property-is-prop-double-negation-eliminating-map
```

### The type of propositionally double negation eliminating maps

```agda
prop-double-negation-eliminating-map :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
prop-double-negation-eliminating-map A B =
  Σ (A → B) (is-prop-double-negation-eliminating-map)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : prop-double-negation-eliminating-map A B)
  where

  map-prop-double-negation-eliminating-map : A → B
  map-prop-double-negation-eliminating-map = pr1 f

  is-prop-double-negation-eliminating-prop-double-negation-eliminating-map :
    is-prop-double-negation-eliminating-map
      map-prop-double-negation-eliminating-map
  is-prop-double-negation-eliminating-prop-double-negation-eliminating-map =
    pr2 f
```

## Properties

### Double negation eliminating maps are closed under homotopy

```agda
abstract
  is-prop-double-negation-eliminating-map-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g →
    is-prop-double-negation-eliminating-map g →
    is-prop-double-negation-eliminating-map f
  is-prop-double-negation-eliminating-map-htpy H K b =
    has-prop-double-negation-elim-equiv
      ( equiv-tot (λ a → equiv-concat (inv (H a)) b))
      ( K b)
```

### Double negation eliminating maps are propositionally double negation eliminating

```agda
is-prop-double-negation-eliminating-map-is-double-negation-eliminating-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-double-negation-eliminating-map f →
  is-prop-double-negation-eliminating-map f
is-prop-double-negation-eliminating-map-is-double-negation-eliminating-map H y =
  has-prop-double-negation-elim-has-double-negation-elim (H y)
```

### Propositionally decidable maps are propositionally double negation eliminating

```agda
is-prop-double-negation-eliminating-map-is-inhabited-or-empty-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-inhabited-or-empty-map f → is-prop-double-negation-eliminating-map f
is-prop-double-negation-eliminating-map-is-inhabited-or-empty-map H y =
  prop-double-negation-elim-is-inhabited-or-empty (H y)
```

### Composition of double negation eliminating maps

Given a composition `g ∘ f` of double negation eliminating maps where the left
factor `g` is injective, then the composition is double negation eliminating.

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  fiber-left-is-prop-double-negation-eliminating-map-left :
    is-prop-double-negation-eliminating-map g →
    (z : C) → ¬¬ (fiber (g ∘ f) z) → fiber g z
  fiber-left-is-prop-double-negation-eliminating-map-left G z nngfz =
    G z (λ x → nngfz (λ w → x (f (pr1 w) , pr2 w)))

  fiber-right-is-prop-double-negation-eliminating-map-comp :
    is-injective g →
    (G : is-prop-double-negation-eliminating-map g) →
    is-prop-double-negation-eliminating-map f →
    (z : C) (nngfz : ¬¬ (fiber (g ∘ f) z)) →
    fiber f (pr1 (fiber-left-is-prop-double-negation-eliminating-map-left G z nngfz))
  fiber-right-is-prop-double-negation-eliminating-map-comp H G F z nngfz =
    F ( pr1
        ( fiber-left-is-prop-double-negation-eliminating-map-left G z nngfz))
          ( λ x →
            nngfz
              ( λ w →
                x ( pr1 w ,
                    H ( pr2 w ∙
                        inv
                          ( pr2
                            ( fiber-left-is-prop-double-negation-eliminating-map-left
                                G z nngfz))))))

  is-prop-double-negation-eliminating-map-comp :
    is-injective g →
    is-prop-double-negation-eliminating-map g →
    is-prop-double-negation-eliminating-map f →
    is-prop-double-negation-eliminating-map (g ∘ f)
  is-prop-double-negation-eliminating-map-comp H G F z nngfz =
    map-inv-compute-fiber-comp g f z
      ( ( fiber-left-is-prop-double-negation-eliminating-map-left G z nngfz) ,
        ( fiber-right-is-prop-double-negation-eliminating-map-comp H G F z nngfz))
```

### Left cancellation for double negation eliminating maps

If a composite `g ∘ f` is double negation eliminating and the left factor `g` is
injective, then the right factor `f` is double negation eliminating.

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  (GF : is-prop-double-negation-eliminating-map (g ∘ f))
  where

  fiber-comp-is-prop-double-negation-eliminating-map-right-factor' :
    (y : B) → ¬¬ (fiber f y) → Σ (fiber g (g y)) (λ t → fiber f (pr1 t))
  fiber-comp-is-prop-double-negation-eliminating-map-right-factor' y nnfy =
    map-compute-fiber-comp g f (g y)
      ( GF (g y) (λ ngfgy → nnfy λ x → ngfgy ((pr1 x) , ap g (pr2 x))))

  is-prop-double-negation-eliminating-map-right-factor' :
    is-injective g → is-prop-double-negation-eliminating-map f
  is-prop-double-negation-eliminating-map-right-factor' G y nnfy =
    tr
      ( fiber f)
      ( G ( pr2
            ( pr1
              ( fiber-comp-is-prop-double-negation-eliminating-map-right-factor'
                ( y)
                ( nnfy)))))
      ( pr2
        ( fiber-comp-is-prop-double-negation-eliminating-map-right-factor' y nnfy))
```

### Any map out of the empty type is double negation eliminating

```text
abstract
  is-prop-double-negation-eliminating-map-ex-falso :
    {l : Level} {X : UU l} →
    is-prop-double-negation-eliminating-map (ex-falso {l} {X})
  is-prop-double-negation-eliminating-map-ex-falso x f = ex-falso (f λ ())
```

### The identity map is double negation eliminating

```text
abstract
  is-prop-double-negation-eliminating-map-id :
    {l : Level} {X : UU l} → is-prop-double-negation-eliminating-map (id {l} {X})
  is-prop-double-negation-eliminating-map-id x y = (x , refl)
```

### Equivalences are double negation eliminating maps

```text
abstract
  is-prop-double-negation-eliminating-map-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-prop-double-negation-eliminating-map f
  is-prop-double-negation-eliminating-map-is-equiv H x =
    double-negation-elim-is-contr (is-contr-map-is-equiv H x)
```

### The map on total spaces induced by a family of double negation eliminating maps is double negation eliminating

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-prop-double-negation-eliminating-map-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-prop-double-negation-eliminating-map (f x)) →
    is-prop-double-negation-eliminating-map (tot f)
  is-prop-double-negation-eliminating-map-tot {f} H x =
    has-double-negation-elim-equiv (compute-fiber-tot f x) (H (pr1 x) (pr2 x))
```

### The map on total spaces induced by a double negation eliminating map on the base is double negation eliminating

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  is-prop-double-negation-eliminating-map-Σ-map-base :
    {f : A → B} →
    is-prop-double-negation-eliminating-map f →
    is-prop-double-negation-eliminating-map (map-Σ-map-base f C)
  is-prop-double-negation-eliminating-map-Σ-map-base {f} H x =
    has-double-negation-elim-equiv'
      ( compute-fiber-map-Σ-map-base f C x)
      ( H (pr1 x))
```

### Products of double negation eliminating maps are double negation eliminating

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-prop-double-negation-eliminating-map-product :
    {f : A → B} {g : C → D} →
    is-prop-double-negation-eliminating-map f →
    is-prop-double-negation-eliminating-map g →
    is-prop-double-negation-eliminating-map (map-product f g)
  is-prop-double-negation-eliminating-map-product {f} {g} F G x =
    has-double-negation-elim-equiv
      ( compute-fiber-map-product f g x)
      ( double-negation-elim-product (F (pr1 x)) (G (pr2 x)))
```

### Coproducts of double negation eliminating maps are double negation eliminating

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-prop-double-negation-eliminating-map-coproduct :
    {f : A → B} {g : C → D} →
    is-prop-double-negation-eliminating-map f →
    is-prop-double-negation-eliminating-map g →
    is-prop-double-negation-eliminating-map (map-coproduct f g)
  is-prop-double-negation-eliminating-map-coproduct {f} {g} F G (inl x) =
    has-double-negation-elim-equiv'
      ( compute-fiber-inl-map-coproduct f g x)
      ( F x)
  is-prop-double-negation-eliminating-map-coproduct {f} {g} F G (inr y) =
    has-double-negation-elim-equiv'
      ( compute-fiber-inr-map-coproduct f g y)
      ( G y)
```

### Double negation eliminating maps are closed under base change

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : C → D}
  where

  is-prop-double-negation-eliminating-map-base-change :
    cartesian-hom-arrow g f →
    is-prop-double-negation-eliminating-map f →
    is-prop-double-negation-eliminating-map g
  is-prop-double-negation-eliminating-map-base-change α F d =
    has-double-negation-elim-equiv
      ( equiv-fibers-cartesian-hom-arrow g f α d)
      ( F (map-codomain-cartesian-hom-arrow g f α d))
```

### Double negation eliminating maps are closed under retracts of maps

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y}
  where

  is-prop-double-negation-eliminating-retract-map :
    f retract-of-map g →
    is-prop-double-negation-eliminating-map g →
    is-prop-double-negation-eliminating-map f
  is-prop-double-negation-eliminating-retract-map R G x =
    has-double-negation-elim-retract
      ( retract-fiber-retract-map f g R x)
      ( G (map-codomain-inclusion-retract-map f g R x))
```
