# Nonsurjective maps

```agda
module foundation.nonsurjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements-images
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
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
open import foundation.law-of-excluded-middle
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.surjective-maps
open import foundation.types-with-decidable-existential-quantification
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.propositions

open import logic.de-morgan-maps
open import logic.propositionally-decidable-maps
open import logic.propositionally-decidable-types
```

</details>

## Idea

A map `f : A → B` is
{{#concept "nonsurjective" Disambiguation="map of types" Agda=is-nonsurjective Agda=nonsurjective-map}}
if there [exists](foundation.existential-quantification.md) a
[fiber](foundation-core.fibers-of-maps.md) that is [not](foundation.negation.md)
inhabited.

**Terminology.** A map that is not nonsurjective is called _extremely dense_ in
the terminology of Escardó {{#cite Esc26}}.

## Definitions

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
  is-not-surjective-is-nonsurjective =
    is-not-surjective-is-nonsurjective' ∘ intro-double-negation-type-trunc-Prop
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
```

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
  is-nonsurjective-comp-is-injective-left =
    map-trunc-Prop ∘ nonim-comp-is-injective-left
```

### Propositionally decidable and not nonsurjective maps are surjective

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B}
  where abstract

  is-surjective-not-nonim-is-inhabited-or-empty-map :
    is-inhabited-or-empty-map f → ¬ nonim f → is-surjective f
  is-surjective-not-nonim-is-inhabited-or-empty-map H nn b =
    rec-coproduct id (λ nf → ex-falso (nn (b , nf))) (H b)

  is-surjective-is-not-nonsurjective-is-inhabited-or-empty-map :
    is-inhabited-or-empty-map f → ¬ is-nonsurjective f → is-surjective f
  is-surjective-is-not-nonsurjective-is-inhabited-or-empty-map H K =
    is-surjective-not-nonim-is-inhabited-or-empty-map H (K ∘ unit-trunc-Prop)

  is-surjective-is-not-nonsurjective-LEM :
    level-LEM (l1 ⊔ l2) →
    ¬ is-nonsurjective f → is-surjective f
  is-surjective-is-not-nonsurjective-LEM lem =
    is-surjective-is-not-nonsurjective-is-inhabited-or-empty-map
      ( λ y →
        is-inhabited-or-empty-is-decidable-trunc-Prop
          ( lem (trunc-Prop (fiber f y))))
```

### If the codomain is searchable and `f` is propositionally decidable, then if `f` is not surjective it is nonsurjective

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B}
  where abstract

  is-surjective-not-nonim-has-decidable-∃ :
    has-decidable-∃-Level l2 A →
    has-decidable-equality B →
    ¬ nonim f → is-surjective f
  is-surjective-not-nonim-has-decidable-∃ h d =
    is-surjective-not-nonim-is-inhabited-or-empty-map
      ( is-inhabited-or-empty-map-has-decidable-∃-Level h d f)
```

For decidability of nonsurjectivity, it suffices that `f` is
[De Morgan](logic.de-morgan-maps.md): the negation of each fiber is decidable.

```agda
  is-decidable-is-nonsurjective-is-de-morgan-map-has-decidable-∃ :
    has-decidable-∃-Level (l1 ⊔ l2) B →
    is-de-morgan-map f →
    is-decidable (is-nonsurjective f)
  is-decidable-is-nonsurjective-is-de-morgan-map-has-decidable-∃ h Hf =
    h ( (λ b → ¬ fiber f b) , Hf)

  is-decidable-is-nonsurjective-has-decidable-equality-codomain-has-decidable-∃ :
    has-decidable-∃-Level (l1 ⊔ l2) B →
    has-decidable-∃-Level l2 A →
    has-decidable-equality B →
    is-decidable (is-nonsurjective f)
  is-decidable-is-nonsurjective-has-decidable-equality-codomain-has-decidable-∃
    h hA d =
    is-decidable-is-nonsurjective-is-de-morgan-map-has-decidable-∃
      h
      ( is-de-morgan-map-is-inhabited-or-empty-map
        ( is-inhabited-or-empty-map-has-decidable-∃-Level hA d f))

  is-nonsurjective-is-not-surjective-is-inhabited-or-empty-map-has-decidable-∃ :
    has-decidable-∃-Level (l1 ⊔ l2) B →
    is-inhabited-or-empty-map f →
    ¬ is-surjective f → is-nonsurjective f
  is-nonsurjective-is-not-surjective-is-inhabited-or-empty-map-has-decidable-∃
    h Hf H =
    rec-coproduct
      ( id)
      ( ex-falso ∘
        H ∘
        is-surjective-is-not-nonsurjective-is-inhabited-or-empty-map Hf)
      ( is-decidable-is-nonsurjective-is-de-morgan-map-has-decidable-∃ h
        ( is-de-morgan-map-is-inhabited-or-empty-map Hf))

  is-nonsurjective-is-not-surjective-has-decidable-∃-Level :
    has-decidable-∃-Level (l1 ⊔ l2) B →
    has-decidable-∃-Level l2 A →
    has-decidable-equality B →
    ¬ is-surjective f → is-nonsurjective f
  is-nonsurjective-is-not-surjective-has-decidable-∃-Level
    h hA d =
    is-nonsurjective-is-not-surjective-is-inhabited-or-empty-map-has-decidable-∃
      h
      ( is-inhabited-or-empty-map-has-decidable-∃-Level hA d f)
```

### Assuming excluded middle, not surjective maps are nonsurjective

```agda
module _
  {l1 l2 : Level}
  (lem : level-LEM (l1 ⊔ l2))
  {A : UU l1} {B : UU l2} {f : A → B}
  where abstract

  is-nonsurjective-is-not-surjective-LEM :
    ¬ is-surjective f → is-nonsurjective f
  is-nonsurjective-is-not-surjective-LEM H =
    rec-coproduct
      ( id)
      ( ex-falso ∘ H ∘ is-surjective-is-not-nonsurjective-LEM lem)
      ( lem (is-nonsurjective-Prop f))
```

## References

{{#bibliography}}
