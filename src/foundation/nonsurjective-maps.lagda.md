# Nonsurjective maps

```agda
module foundation.nonsurjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-maps
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.injective-maps
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.propositions

open import logic.propositionally-decidable-maps
```

</details>

## Idea

A map `f : A → B` is {{#concept "nonsurjective"}} if there
[exists](foundation.existential-quantification.md) a
[fiber](foundation-core.fibers-of-maps.md) that is [not](foundation.negation.md)
inhabited.

## Definitions

### The nonimage of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  nonim : UU (l1 ⊔ l2)
  nonim = Σ B (λ y → ¬ fiber f y)
```

### Nonsurjectivity of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-nonsurjective : UU (l1 ⊔ l2)
  is-nonsurjective = ║ nonim f ║₋₁

  is-prop-is-nonsurjective : is-prop is-nonsurjective
  is-prop-is-nonsurjective = is-prop-exists-structure B (λ y → ¬ fiber f y)

  is-nonsurjective-Prop : Prop (l1 ⊔ l2)
  is-nonsurjective-Prop = exists-structure-Prop B (λ y → ¬ fiber f y)
```

### Nonsurjective maps between types

```agda
nonsurjective-map : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
nonsurjective-map A B = Σ (A → B) is-nonsurjective

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : nonsurjective-map A B)
  where

  map-nonsurjective-map : A → B
  map-nonsurjective-map = pr1 f

  is-nonsurjective-map-nonsurjective-map :
    is-nonsurjective map-nonsurjective-map
  is-nonsurjective-map-nonsurjective-map = pr2 f
```

## Properties

### Nonsurjective maps are not surjective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-not-surjective-is-nonsurjective' : ¬¬ nonim f → ¬ is-surjective f
  is-not-surjective-is-nonsurjective' F H =
    F (λ (x , np) → rec-trunc-Prop empty-Prop np (H x))

  is-not-surjective-is-nonsurjective : is-nonsurjective f → ¬ is-surjective f
  is-not-surjective-is-nonsurjective F =
    is-not-surjective-is-nonsurjective'
      ( intro-double-negation-type-trunc-Prop F)
```

### If `g ∘ f` is nonsurjective and `g` is surjective then `f` is nonsurjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  is-nonsurjective-right-nonim-comp-is-surjective-left :
    is-surjective g → nonim (g ∘ f) → is-nonsurjective f
  is-nonsurjective-right-nonim-comp-is-surjective-left G (c , np) =
    map-trunc-Prop
      ( λ (y , q) → (y , map-neg (inclusion-fiber-comp g f (y , q)) np))
      ( G c)

  is-nonsurjective-right-is-surjective-left :
    is-surjective g → is-nonsurjective (g ∘ f) → is-nonsurjective f
  is-nonsurjective-right-is-surjective-left G =
    rec-trunc-Prop
      ( is-nonsurjective-Prop f)
      ( is-nonsurjective-right-nonim-comp-is-surjective-left G)
```

### If `g ∘ f` is nonsurjective and `g` is decidable then `g` or `f` is nonsurjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  decide-nonim-comp :
    is-decidable-map g →
    nonim (g ∘ f) → nonim f + nonim g
  decide-nonim-comp H (c , np) =
    map-coproduct
      ( λ (y , q) → y , map-neg (inclusion-fiber-comp g f (y , q)) np)
      ( c ,_)
      ( H c)

  decide-is-nonsurjective-nonim-comp' :
    is-decidable-map g →
    nonim (g ∘ f) → is-nonsurjective f + is-nonsurjective g
  decide-is-nonsurjective-nonim-comp' H (c , np) =
    map-coproduct
      ( λ (y , q) →
        unit-trunc-Prop (y , map-neg (inclusion-fiber-comp g f (y , q)) np))
        (λ p → unit-trunc-Prop (c , p))
      ( H c)

  is-nonsurjective-is-nonsurjective-comp' :
    is-decidable-map g →
    is-nonsurjective (g ∘ f) →
    disjunction-type (is-nonsurjective f) (is-nonsurjective g)
  is-nonsurjective-is-nonsurjective-comp' H =
    map-trunc-Prop (decide-is-nonsurjective-nonim-comp' H)
```

In fact, it suffices that `g` is propositionally decidable.

```agda
  decide-is-nonsurjective-nonim-comp :
    is-inhabited-or-empty-map g →
    nonim (g ∘ f) → is-nonsurjective f + is-nonsurjective g
  decide-is-nonsurjective-nonim-comp H (c , np) =
    map-coproduct
      ( map-trunc-Prop
        ( λ (y , q) → y , map-neg (inclusion-fiber-comp g f (y , q)) np))
      ( λ p → unit-trunc-Prop (c , p))
      ( H c)

  is-nonsurjective-is-nonsurjective-comp :
    is-inhabited-or-empty-map g →
    is-nonsurjective (g ∘ f) →
    disjunction-type (is-nonsurjective f) (is-nonsurjective g)
  is-nonsurjective-is-nonsurjective-comp H =
    map-trunc-Prop (decide-is-nonsurjective-nonim-comp H)
```

### If `g` is nonsurjective then so is `g ∘ f`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  nonim-comp : nonim g → nonim (g ∘ f)
  nonim-comp (c , np) = (c , map-neg (left-fiber-comp g f) np)

  is-nonsurjective-comp : is-nonsurjective g → is-nonsurjective (g ∘ f)
  is-nonsurjective-comp = map-trunc-Prop nonim-comp
```

### If `g` is injective and `f` is nonsurjective then so is `g ∘ f`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  nonim-comp-is-injective-left : is-injective g → nonim f → nonim (g ∘ f)
  nonim-comp-is-injective-left G (c , np) =
    ( g c , map-neg (tot (λ _ → G)) np)

  is-nonsurjective-comp-is-injective-left :
    is-injective g → is-nonsurjective f → is-nonsurjective (g ∘ f)
  is-nonsurjective-comp-is-injective-left G =
    map-trunc-Prop (nonim-comp-is-injective-left G)
```
