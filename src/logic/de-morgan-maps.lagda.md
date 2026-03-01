# De Morgan maps

```agda
module logic.de-morgan-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-arrows
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies

open import logic.de-morgan-types
open import logic.de-morgans-law
open import logic.double-negation-eliminating-maps
open import logic.double-negation-elimination
open import logic.propositionally-decidable-maps
open import logic.propositionally-decidable-types
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be
{{#concept "De Morgan" Disambiguation="map of types" Agda=is-de-morgan-map}} if
the [negation](foundation-core.negation.md) of its
[fibers](foundation-core.fibers-of-maps.md) are
[decidable](foundation.decidable-types.md). I.e., the map `f : A → B` is De
Morgan if for every `y : B`, the fiber `fiber f y` is either
[empty](foundation.empty-types.md) or not empty. This is equivalent to asking
that the fibers satisfy [De Morgan's law](logic.de-morgans-law.md), but is a
[small](foundation.small-types.md) condition.

## Definition

### De Morgan maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-de-morgan-map : (A → B) → UU (l1 ⊔ l2)
  is-de-morgan-map f = (y : B) → is-de-morgan (fiber f y)

  is-prop-is-de-morgan-map : {f : A → B} → is-prop (is-de-morgan-map f)
  is-prop-is-de-morgan-map {f} =
    is-prop-Π (λ y → is-prop-is-de-morgan (fiber f y))

  is-de-morgan-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-de-morgan-map-Prop f = is-de-morgan-map f , is-prop-is-de-morgan-map
```

### The type of De Morgan maps

```agda
infix 5 _→ᵈᵐ_

_→ᵈᵐ_ : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A →ᵈᵐ B = Σ (A → B) (is-de-morgan-map)

de-morgan-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
de-morgan-map = _→ᵈᵐ_

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A →ᵈᵐ B)
  where

  map-de-morgan-map : A → B
  map-de-morgan-map = pr1 f

  is-de-morgan-de-morgan-map : is-de-morgan-map map-de-morgan-map
  is-de-morgan-de-morgan-map = pr2 f
```

### Self-De-Morgan maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-self-de-morgan-map : (A → B) → UU (l1 ⊔ l2)
  is-self-de-morgan-map f =
    (y z : B) → de-morgans-law' (fiber f y) (fiber f z)
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
is-de-morgan-map-is-decidable-map H y = is-de-morgan-is-decidable (H y)
```

### Double negation eliminating De Morgan maps are decidable

```agda
is-decidable-map-is-double-negation-eliminating-de-morgan-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-de-morgan-map f → is-double-negation-eliminating-map f → is-decidable-map f
is-decidable-map-is-double-negation-eliminating-de-morgan-map H K y =
  is-decidable-is-decidable-neg-has-double-negation-elim (K y) (H y)
```

### Left cancellation for De Morgan maps

If a composite `g ∘ f` is De Morgan and the left factor `g` is injective, then
the right factor `f` is De Morgan.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  is-de-morgan-map-right-factor' :
    is-injective g →
    is-de-morgan-map (g ∘ f) →
    is-de-morgan-map f
  is-de-morgan-map-right-factor' H GF y =
    rec-coproduct
      ( λ ngfy → inl (λ p → ngfy (pr1 p , ap g (pr2 p))))
      ( λ nngfy → inr (λ nq → nngfy (λ p → nq (pr1 p , H (pr2 p)))))
      ( GF (g y))
```

### Composition of De Morgan maps with decidable maps

If `g` is a decidable injection and `f` is a De Morgan map, then `g ∘ f` is De
Morgan.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  is-de-morgan-map-comp-is-decidable-map :
    is-injective g →
    is-decidable-map g →
    is-de-morgan-map f →
    is-de-morgan-map (g ∘ f)
  is-de-morgan-map-comp-is-decidable-map H G F y =
    rec-coproduct
      ( λ u →
        is-de-morgan-iff
          ( λ v → (pr1 v) , ap g (pr2 v) ∙ pr2 u)
          ( λ w → pr1 w , H (pr2 w ∙ inv (pr2 u)))
          ( F (pr1 u)))
      ( λ ng → inl (λ u → ng (f (pr1 u) , pr2 u)))
      ( G y)
```

### Any map out of the empty type is De Morgan

```agda
abstract
  is-de-morgan-map-ex-falso :
    {l : Level} {X : UU l} → is-de-morgan-map (ex-falso {l} {X})
  is-de-morgan-map-ex-falso =
    is-de-morgan-map-is-decidable-map is-decidable-map-ex-falso
```

### The identity map is De Morgan

```agda
abstract
  is-de-morgan-map-id :
    {l : Level} {X : UU l} → is-de-morgan-map (id {l} {X})
  is-de-morgan-map-id =
    is-de-morgan-map-is-decidable-map is-decidable-map-id
```

### Equivalences are De Morgan maps

```agda
abstract
  is-de-morgan-map-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-de-morgan-map f
  is-de-morgan-map-is-equiv H =
    is-de-morgan-map-is-decidable-map (is-decidable-map-is-equiv H)
```

### The map on total spaces induced by a family of De Morgan maps is De Morgan

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-de-morgan-map-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-de-morgan-map (f x)) →
    is-de-morgan-map (tot f)
  is-de-morgan-map-tot {f} H x =
    is-decidable-equiv (equiv-neg (compute-fiber-tot f x)) (H (pr1 x) (pr2 x))
```

### The map on total spaces induced by a De Morgan map on the base is De Morgan

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  is-de-morgan-map-Σ-map-base :
    {f : A → B} →
    is-de-morgan-map f →
    is-de-morgan-map (map-Σ-map-base f C)
  is-de-morgan-map-Σ-map-base {f} H x =
    is-decidable-equiv'
      ( equiv-neg (compute-fiber-map-Σ-map-base f C x))
      ( H (pr1 x))
```

### Products of De Morgan maps are De Morgan

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-de-morgan-map-product :
    {f : A → B} {g : C → D} →
    is-de-morgan-map f →
    is-de-morgan-map g →
    is-de-morgan-map (map-product f g)
  is-de-morgan-map-product {f} {g} F G y =
    is-de-morgan-equiv
      ( compute-fiber-map-product f g y)
      ( is-de-morgan-product (F (pr1 y)) (G (pr2 y)))
```

### Coproducts of De Morgan maps are De Morgan

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-de-morgan-map-coproduct :
    {f : A → B} {g : C → D} →
    is-de-morgan-map f →
    is-de-morgan-map g →
    is-de-morgan-map (map-coproduct f g)
  is-de-morgan-map-coproduct {f} {g} F G (inl x) =
    is-decidable-equiv'
      ( equiv-neg (compute-fiber-inl-map-coproduct f g x))
      ( F x)
  is-de-morgan-map-coproduct {f} {g} F G (inr x) =
    is-decidable-equiv'
      ( equiv-neg (compute-fiber-inr-map-coproduct f g x))
      ( G x)
```

### De Morgan maps are closed under base change

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : C → D}
  where

  is-de-morgan-map-base-change :
    cartesian-hom-arrow g f →
    is-de-morgan-map f →
    is-de-morgan-map g
  is-de-morgan-map-base-change α F d =
    is-decidable-equiv
      ( equiv-neg (equiv-fibers-cartesian-hom-arrow g f α d))
      ( F (map-codomain-cartesian-hom-arrow g f α d))
```

### De Morgan maps are closed under retracts of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y}
  where

  is-de-morgan-retract-arrow :
    f retract-of-arrow g →
    is-de-morgan-map g →
    is-de-morgan-map f
  is-de-morgan-retract-arrow R G x =
    is-decidable-iff
      ( map-neg (inclusion-retract (retract-fiber-retract-arrow f g R x)))
      ( map-neg (map-retraction-retract (retract-fiber-retract-arrow f g R x)))
      ( G (map-codomain-inclusion-retract-arrow f g R x))
```

### Propositionally decidable maps are De Morgan

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-de-morgan-map-is-inhabited-or-empty-map :
    is-inhabited-or-empty-map f → is-de-morgan-map f
  is-de-morgan-map-is-inhabited-or-empty-map H b =
    is-decidable-iff
      ( is-empty-type-trunc-Prop')
      ( is-empty-type-trunc-Prop)
      ( is-decidable-neg (is-decidable-trunc-Prop-is-inhabited-or-empty (H b)))
```
