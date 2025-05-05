# Double negation eliminating maps

```agda
module logic.double-negation-eliminating-maps where
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

open import logic.double-negation-elimination
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be
{{#concept "double negation eliminating" Disambiguation="map of types" Agda=is-double-negation-eliminating-map}}
if its [fibers](foundation-core.fibers-of-maps.md) satisfy
[untruncated double negation elimination](logic.double-negation-elimination.md).
I.e., for every `y : B`, if `fiber f y` is
[irrefutable](foundation.irrefutable-propositions.md), then we do in fact have
an element of the fiber `p : fiber f y`. In other words, double negation
eliminating maps come [equipped](foundation.structure.md) with a map

```text
  (y : B) → ¬¬ (fiber f y) → fiber f y.
```

## Definition

### Double negation elimination structure on a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-double-negation-eliminating-map : (A → B) → UU (l1 ⊔ l2)
  is-double-negation-eliminating-map f =
    (y : B) → has-double-negation-elim (fiber f y)
```

### The type of double negation eliminating maps

```agda
infix 5 _→¬¬_

_→¬¬_ : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A →¬¬ B = Σ (A → B) (is-double-negation-eliminating-map)

double-negation-eliminating-map :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
double-negation-eliminating-map = _→¬¬_

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A →¬¬ B)
  where

  map-double-negation-eliminating-map : A → B
  map-double-negation-eliminating-map = pr1 f

  is-double-negation-eliminating-double-negation-eliminating-map :
    is-double-negation-eliminating-map map-double-negation-eliminating-map
  is-double-negation-eliminating-double-negation-eliminating-map = pr2 f
```

## Properties

### Double negation eliminating maps are closed under homotopy

```agda
abstract
  is-double-negation-eliminating-map-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g →
    is-double-negation-eliminating-map g →
    is-double-negation-eliminating-map f
  is-double-negation-eliminating-map-htpy H K b =
    has-double-negation-elim-equiv
      ( equiv-tot (λ a → equiv-concat (inv (H a)) b))
      ( K b)
```

### Decidable maps are double negation eliminating

```agda
is-double-negation-eliminating-map-is-decidable-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-decidable-map f → is-double-negation-eliminating-map f
is-double-negation-eliminating-map-is-decidable-map H y =
  double-negation-elim-is-decidable (H y)
```

### Composition of double negation eliminating maps

Given a composition `g ∘ f` of double negation eliminating maps where the left
factor `g` is injective, then the composition is double negation eliminating.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  fiber-left-is-double-negation-eliminating-map-left :
    is-double-negation-eliminating-map g →
    (z : C) → ¬¬ (fiber (g ∘ f) z) → fiber g z
  fiber-left-is-double-negation-eliminating-map-left G z nngfz =
    G z (λ x → nngfz (λ w → x (f (pr1 w) , pr2 w)))

  fiber-right-is-double-negation-eliminating-map-comp :
    is-injective g →
    (G : is-double-negation-eliminating-map g) →
    is-double-negation-eliminating-map f →
    (z : C) (nngfz : ¬¬ (fiber (g ∘ f) z)) →
    fiber f (pr1 (fiber-left-is-double-negation-eliminating-map-left G z nngfz))
  fiber-right-is-double-negation-eliminating-map-comp H G F z nngfz =
    F ( pr1
        ( fiber-left-is-double-negation-eliminating-map-left G z nngfz))
          ( λ x →
            nngfz
              ( λ w →
                x ( pr1 w ,
                    H ( pr2 w ∙
                        inv
                          ( pr2
                            ( fiber-left-is-double-negation-eliminating-map-left
                                G z nngfz))))))

  is-double-negation-eliminating-map-comp :
    is-injective g →
    is-double-negation-eliminating-map g →
    is-double-negation-eliminating-map f →
    is-double-negation-eliminating-map (g ∘ f)
  is-double-negation-eliminating-map-comp H G F z nngfz =
    map-inv-compute-fiber-comp g f z
      ( ( fiber-left-is-double-negation-eliminating-map-left G z nngfz) ,
        ( fiber-right-is-double-negation-eliminating-map-comp H G F z nngfz))
```

### Left cancellation for double negation eliminating maps

If a composite `g ∘ f` is double negation eliminating and the left factor `g` is
injective, then the right factor `f` is double negation eliminating.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  (GF : is-double-negation-eliminating-map (g ∘ f))
  where

  fiber-comp-is-double-negation-eliminating-map-right-factor' :
    (y : B) → ¬¬ (fiber f y) → Σ (fiber g (g y)) (λ t → fiber f (pr1 t))
  fiber-comp-is-double-negation-eliminating-map-right-factor' y nnfy =
    map-compute-fiber-comp g f (g y)
      ( GF (g y) (λ ngfgy → nnfy λ x → ngfgy ((pr1 x) , ap g (pr2 x))))

  is-double-negation-eliminating-map-right-factor' :
    is-injective g → is-double-negation-eliminating-map f
  is-double-negation-eliminating-map-right-factor' G y nnfy =
    tr
      ( fiber f)
      ( G ( pr2
            ( pr1
              ( fiber-comp-is-double-negation-eliminating-map-right-factor'
                ( y)
                ( nnfy)))))
      ( pr2
        ( fiber-comp-is-double-negation-eliminating-map-right-factor' y nnfy))
```

### Any map out of the empty type is double negation eliminating

```agda
abstract
  is-double-negation-eliminating-map-ex-falso :
    {l : Level} {X : UU l} →
    is-double-negation-eliminating-map (ex-falso {l} {X})
  is-double-negation-eliminating-map-ex-falso x f = ex-falso (f λ ())
```

### The identity map is double negation eliminating

```agda
abstract
  is-double-negation-eliminating-map-id :
    {l : Level} {X : UU l} → is-double-negation-eliminating-map (id {l} {X})
  is-double-negation-eliminating-map-id x y = (x , refl)
```

### Equivalences are double negation eliminating maps

```agda
abstract
  is-double-negation-eliminating-map-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-double-negation-eliminating-map f
  is-double-negation-eliminating-map-is-equiv H x =
    double-negation-elim-is-contr (is-contr-map-is-equiv H x)
```

### The map on total spaces induced by a family of double negation eliminating maps is double negation eliminating

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-double-negation-eliminating-map-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-double-negation-eliminating-map (f x)) →
    is-double-negation-eliminating-map (tot f)
  is-double-negation-eliminating-map-tot {f} H x =
    has-double-negation-elim-equiv (compute-fiber-tot f x) (H (pr1 x) (pr2 x))
```

### The map on total spaces induced by a double negation eliminating map on the base is double negation eliminating

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  is-double-negation-eliminating-map-Σ-map-base :
    {f : A → B} →
    is-double-negation-eliminating-map f →
    is-double-negation-eliminating-map (map-Σ-map-base f C)
  is-double-negation-eliminating-map-Σ-map-base {f} H x =
    has-double-negation-elim-equiv'
      ( compute-fiber-map-Σ-map-base f C x)
      ( H (pr1 x))
```

### Products of double negation eliminating maps are double negation eliminating

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-double-negation-eliminating-map-product :
    {f : A → B} {g : C → D} →
    is-double-negation-eliminating-map f →
    is-double-negation-eliminating-map g →
    is-double-negation-eliminating-map (map-product f g)
  is-double-negation-eliminating-map-product {f} {g} F G x =
    has-double-negation-elim-equiv
      ( compute-fiber-map-product f g x)
      ( double-negation-elim-product (F (pr1 x)) (G (pr2 x)))
```

### Coproducts of double negation eliminating maps are double negation eliminating

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-double-negation-eliminating-map-coproduct :
    {f : A → B} {g : C → D} →
    is-double-negation-eliminating-map f →
    is-double-negation-eliminating-map g →
    is-double-negation-eliminating-map (map-coproduct f g)
  is-double-negation-eliminating-map-coproduct {f} {g} F G (inl x) =
    has-double-negation-elim-equiv'
      ( compute-fiber-inl-map-coproduct f g x)
      ( F x)
  is-double-negation-eliminating-map-coproduct {f} {g} F G (inr y) =
    has-double-negation-elim-equiv'
      ( compute-fiber-inr-map-coproduct f g y)
      ( G y)
```

### Double negation eliminating maps are closed under base change

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : C → D}
  where

  is-double-negation-eliminating-map-base-change :
    cartesian-hom-arrow g f →
    is-double-negation-eliminating-map f →
    is-double-negation-eliminating-map g
  is-double-negation-eliminating-map-base-change α F d =
    has-double-negation-elim-equiv
      ( equiv-fibers-cartesian-hom-arrow g f α d)
      ( F (map-codomain-cartesian-hom-arrow g f α d))
```

### Double negation eliminating maps are closed under retracts of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y}
  where

  is-double-negation-eliminating-retract-map :
    f retract-of-map g →
    is-double-negation-eliminating-map g →
    is-double-negation-eliminating-map f
  is-double-negation-eliminating-retract-map R G x =
    has-double-negation-elim-retract
      ( retract-fiber-retract-map f g R x)
      ( G (map-codomain-inclusion-retract-map f g R x))
```
