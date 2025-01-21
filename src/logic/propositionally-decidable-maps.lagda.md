# Propositionally decidable maps

```agda
module logic.propositionally-decidable-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.coproduct-types
open import foundation.decidable-dependent-pair-types
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.pi-0-trivial-maps
open import foundation.propositional-truncations
open import foundation.retracts-of-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.iterating-functions
open import foundation-core.retractions
open import foundation-core.sections

open import logic.propositionally-decidable-types
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be
{{#concept "propositionally decidable" Disambiguation="map of types" Agda=is-inhabited-or-empty-map}}
if its [fibers](foundation-core.fibers-of-maps.md) are
[propositionally decidable types](logic.propositionally-decidable-types.md).

## Definitions

### The structure on a map of decidability

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inhabited-or-empty-map : (A → B) → UU (l1 ⊔ l2)
  is-inhabited-or-empty-map f = (y : B) → is-inhabited-or-empty (fiber f y)
```

### The type of decidable maps

```agda
inhabited-or-empty-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
inhabited-or-empty-map A B = Σ (A → B) (is-inhabited-or-empty-map)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : inhabited-or-empty-map A B)
  where

  map-inhabited-or-empty-map : A → B
  map-inhabited-or-empty-map = pr1 f

  is-decidable-inhabited-or-empty-map :
    is-inhabited-or-empty-map map-inhabited-or-empty-map
  is-decidable-inhabited-or-empty-map = pr2 f
```

## Properties

### Propositionally decidable maps are closed under homotopy

```agda
abstract
  is-inhabited-or-empty-map-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g → is-inhabited-or-empty-map g → is-inhabited-or-empty-map f
  is-inhabited-or-empty-map-htpy H K b =
    is-inhabited-or-empty-equiv
      ( equiv-tot (λ a → equiv-concat (inv (H a)) b))
      ( K b)
```

### Decidable maps are propositionally decidable

```agda
is-inhabited-or-empty-map-is-decidable-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-decidable-map f → is-inhabited-or-empty-map f
is-inhabited-or-empty-map-is-decidable-map H x =
  is-inhabited-or-empty-is-decidable (H x)
```

### The identity map is decidable

```agda
abstract
  is-inhabited-or-empty-map-id :
    {l : Level} {X : UU l} → is-inhabited-or-empty-map (id {l} {X})
  is-inhabited-or-empty-map-id y = inl (unit-trunc-Prop (y , refl))
```

### Composition of propositionally decidable maps

The composite `g ∘ f` of two propositionally decidable maps is propositionally
decidable if `g` is injective.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  abstract
    is-inhabited-or-empty-map-comp :
      is-injective g →
      is-inhabited-or-empty-map g →
      is-inhabited-or-empty-map f →
      is-inhabited-or-empty-map (g ∘ f)
    is-inhabited-or-empty-map-comp H G F x =
      is-inhabited-or-empty-equiv
        ( compute-fiber-comp g f x)
        ( elim-is-inhabited-or-empty-Prop
          ( is-inhabited-or-empty-Prop
            ( Σ (fiber g x) (fiber f ∘ pr1)))
          ( λ t →
            elim-is-inhabited-or-empty-Prop
              ( is-inhabited-or-empty-Prop (Σ (fiber g x) (fiber f ∘ pr1)))
              ( λ s → inl (unit-trunc-Prop (t , s)))
              ( λ ns →
                inr
                  ( λ ts →
                    ns
                      ( pr1 (pr2 ts) ,
                        pr2 (pr2 ts) ∙ H ((pr2 (pr1 ts)) ∙ inv (pr2 t)))))
              ( F (pr1 t)))
          ( λ nt → inr (λ ts → nt (pr1 ts)))
          ( G x))
```

The composite `g ∘ f` of two propositionally decidable maps is propositionally
decidable if `g` is π₀-trivial.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  abstract
    is-inhabited-or-empty-map-comp-is-π₀-trivial-map' :
      is-π₀-trivial-map' g →
      is-inhabited-or-empty-map g →
      is-inhabited-or-empty-map f →
      is-inhabited-or-empty-map (g ∘ f)
    is-inhabited-or-empty-map-comp-is-π₀-trivial-map' H G F x =
      is-inhabited-or-empty-equiv
        ( compute-fiber-comp g f x)
        ( is-inhabited-or-empty-Σ-all-elements-merely-equal-base
          ( H x)
          ( G x)
          ( F ∘ pr1))

module _
  {l1 : Level} {A : UU l1} {f : A → A}
  (is-inhabited-or-empty-f : is-inhabited-or-empty-map f)
  (is-π₀-trivial-f : is-π₀-trivial-map' f)
  where

  is-inhabited-or-empty-map-iterate-is-π₀-trivial-map' :
    (n : ℕ) → is-inhabited-or-empty-map (iterate n f)
  is-inhabited-or-empty-map-iterate-is-π₀-trivial-map' zero-ℕ =
    is-inhabited-or-empty-map-id
  is-inhabited-or-empty-map-iterate-is-π₀-trivial-map' (succ-ℕ n) =
    is-inhabited-or-empty-map-comp-is-π₀-trivial-map'
      ( is-π₀-trivial-f)
      ( is-inhabited-or-empty-f)
      ( is-inhabited-or-empty-map-iterate-is-π₀-trivial-map' n)
```

### Left cancellation for decidable maps

If a composite `g ∘ f` is decidable and `g` is injective then `f` is decidable.

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  abstract
    is-inhabited-or-empty-map-right-factor' :
      is-inhabited-or-empty-map (g ∘ f) → is-injective g → is-inhabited-or-empty-map f
    is-inhabited-or-empty-map-right-factor' GF G y =
      rec-coproduct
        ( λ q → inl (pr1 q , G (pr2 q)))
        ( λ q → inr (λ x → q ((pr1 x) , ap g (pr2 x))))
        ( GF (g y))
```

### Retracts into types with decidable equality are decidable

```text
is-inhabited-or-empty-map-retraction :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → has-decidable-equality B →
  (i : A → B) → retraction i → is-inhabited-or-empty-map i
is-inhabited-or-empty-map-retraction d i (r , R) b =
  is-decidable-iff
    ( λ (p : i (r b) ＝ b) → r b , p)
    ( λ t → ap (i ∘ r) (inv (pr2 t)) ∙ ap i (R (pr1 t)) ∙ pr2 t)
    ( d (i (r b)) b)
```

### The map on total spaces induced by a family of decidable maps is decidable

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-inhabited-or-empty-map-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-inhabited-or-empty-map (f x)) → is-inhabited-or-empty-map (tot f)
  is-inhabited-or-empty-map-tot {f} H x =
    is-decidable-equiv (compute-fiber-tot f x) (H (pr1 x) (pr2 x))
```

### The map on total spaces induced by a decidable map on the base is decidable

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  is-inhabited-or-empty-map-Σ-map-base :
    {f : A → B} → is-inhabited-or-empty-map f → is-inhabited-or-empty-map (map-Σ-map-base f C)
  is-inhabited-or-empty-map-Σ-map-base {f} H x =
    is-decidable-equiv' (compute-fiber-map-Σ-map-base f C x) (H (pr1 x))
```

### Products of decidable maps are decidable

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-inhabited-or-empty-map-product :
    {f : A → B} {g : C → D} →
    is-inhabited-or-empty-map f → is-inhabited-or-empty-map g → is-inhabited-or-empty-map (map-product f g)
  is-inhabited-or-empty-map-product {f} {g} F G x =
    is-decidable-equiv
      ( compute-fiber-map-product f g x)
      ( is-decidable-product (F (pr1 x)) (G (pr2 x)))
```

### Coproducts of decidable maps are decidable

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-inhabited-or-empty-map-coproduct :
    {f : A → B} {g : C → D} →
    is-inhabited-or-empty-map f →
    is-inhabited-or-empty-map g →
    is-inhabited-or-empty-map (map-coproduct f g)
  is-inhabited-or-empty-map-coproduct {f} {g} F G (inl x) =
    is-decidable-equiv' (compute-fiber-inl-map-coproduct f g x) (F x)
  is-inhabited-or-empty-map-coproduct {f} {g} F G (inr y) =
    is-decidable-equiv' (compute-fiber-inr-map-coproduct f g y) (G y)
```

### Propositionally decidable maps are closed under base change

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : C → D}
  where

  is-inhabited-or-empty-map-base-change :
    cartesian-hom-arrow g f → is-inhabited-or-empty-map f → is-inhabited-or-empty-map g
  is-inhabited-or-empty-map-base-change α F d =
    is-decidable-equiv
      ( equiv-fibers-cartesian-hom-arrow g f α d)
      ( F (map-codomain-cartesian-hom-arrow g f α d))
```

### Propositionally decidable maps are closed under retracts of maps

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y}
  where

  is-decidable-retract-map :
    f retract-of-map g → is-inhabited-or-empty-map g → is-inhabited-or-empty-map f
  is-decidable-retract-map R G x =
    is-decidable-retract-of
      ( retract-fiber-retract-map f g R x)
      ( G (map-codomain-inclusion-retract-map f g R x))
```
