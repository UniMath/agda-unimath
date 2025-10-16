# Nonsurjective maps

```agda
module foundation.nonsurjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-maps
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.existential-quantification
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-propositional-truncation
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.negation
open import foundation.postcomposition-dependent-functions
open import foundation.propositional-truncations
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.truncated-types
open import foundation.univalence
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.precomposition-dependent-functions
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.retracts-of-types
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels

open import logic.propositionally-decidable-maps

open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

A map `f : A → B` is {{#concept "nonsurjective"}} if there
[exists](foundation.existential-quantification.md) a
[fiber](foundation-core.fibers-of-maps.md) that is [not](foundation.negation.md)
[inhabited](foundation.inhabited-types.md).

## Definitions

### The nonimage

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  nonim : UU (l1 ⊔ l2)
  nonim = Σ B (λ y → ¬ fiber f y)
```

### Nonsurjectivity

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

## Properties

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
      ( λ (y , q) → y , map-neg (inclusion-fiber-comp g f c (y , q)) np)
      ( c ,_)
      ( H c)

  decide-is-nonsurjective-nonim-comp' :
    is-decidable-map g →
    nonim (g ∘ f) → is-nonsurjective f + is-nonsurjective g
  decide-is-nonsurjective-nonim-comp' H (c , np) =
    map-coproduct
      ( λ (y , q) →
        unit-trunc-Prop (y , map-neg (inclusion-fiber-comp g f c (y , q)) np))
        (λ p → unit-trunc-Prop (c , p))
      ( H c)

  is-nonsurjective-is-nonsurjective-comp' :
    is-decidable-map g →
    is-nonsurjective (g ∘ f) →
    disjunction-type (is-nonsurjective f) (is-nonsurjective g)
  is-nonsurjective-is-nonsurjective-comp' H =
    map-trunc-Prop (decide-is-nonsurjective-nonim-comp' H)

  decide-is-nonsurjective-nonim-comp :
    is-inhabited-or-empty-map g →
    nonim (g ∘ f) → is-nonsurjective f + is-nonsurjective g
  decide-is-nonsurjective-nonim-comp H (c , np) =
    map-coproduct
      ( map-trunc-Prop
        ( λ (y , q) → y , map-neg (inclusion-fiber-comp g f c (y , q)) np))
      ( λ p → unit-trunc-Prop (c , p))
      ( H c)

  is-nonsurjective-is-nonsurjective-comp :
    is-inhabited-or-empty-map g →
    is-nonsurjective (g ∘ f) →
    disjunction-type (is-nonsurjective f) (is-nonsurjective g)
  is-nonsurjective-is-nonsurjective-comp H =
    map-trunc-Prop (decide-is-nonsurjective-nonim-comp H)
```
