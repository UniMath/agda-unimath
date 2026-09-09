# The universal property of propositional truncations with respect to sets

```agda
module foundation.universal-property-propositional-truncation-into-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.weakly-constant-maps

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
```

</details>

## Idea

The propositional truncation of `A` can be thought of as the quotient of `A` by
the full equivalence relation, i.e., the equivalence relation by which all
elements of `A` are considered to be equivalent. This idea leads to the
universal property of the propositional truncations with respect to sets.

## Definition

### The precomposition map that is used to state the universal property

```agda
is-weakly-constant-map-precomp-unit-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : type-trunc-Prop A → B) →
  is-weakly-constant-map (g ∘ unit-trunc-Prop)
is-weakly-constant-map-precomp-unit-trunc-Prop g x y =
  ap g (eq-is-prop is-prop-type-trunc-Prop)

precomp-universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) →
  (type-trunc-Prop A → type-Set B) → Σ (A → type-Set B) is-weakly-constant-map
pr1 (precomp-universal-property-set-quotient-trunc-Prop B g) =
  g ∘ unit-trunc-Prop
pr2 (precomp-universal-property-set-quotient-trunc-Prop B g) =
  is-weakly-constant-map-precomp-unit-trunc-Prop g
```

## Properties

### The image of the propositional truncation into a set is a proposition

```agda
abstract
  all-elements-equal-image-is-weakly-constant-map :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-weakly-constant-map f →
    all-elements-equal (Σ (type-Set B) (λ b → type-trunc-Prop (fiber f b)))
  all-elements-equal-image-is-weakly-constant-map B f H (x , s) (y , t) =
    eq-type-subtype
      ( λ b → trunc-Prop (fiber f b))
      ( apply-universal-property-trunc-Prop s
        ( Id-Prop B x y)
        ( λ u →
          apply-universal-property-trunc-Prop t
            ( Id-Prop B x y)
            ( λ v → inv (pr2 u) ∙ H (pr1 u) (pr1 v) ∙ pr2 v)))

abstract
  is-prop-image-is-weakly-constant-map :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    is-weakly-constant-map f →
    is-prop (Σ (type-Set B) (λ b → type-trunc-Prop (fiber f b)))
  is-prop-image-is-weakly-constant-map B f H =
    is-prop-all-elements-equal
      ( all-elements-equal-image-is-weakly-constant-map B f H)

image-weakly-constant-map-Prop :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f → Prop (l1 ⊔ l2)
pr1 (image-weakly-constant-map-Prop B f H) =
  Σ (type-Set B) (λ b → type-trunc-Prop (fiber f b))
pr2 (image-weakly-constant-map-Prop B f H) =
  is-prop-image-is-weakly-constant-map B f H
```

### The universal property

```agda
map-universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f → type-trunc-Prop A → type-Set B
map-universal-property-set-quotient-trunc-Prop B f H =
  ( pr1) ∘
  ( map-universal-property-trunc-Prop
    ( image-weakly-constant-map-Prop B f H)
    ( λ a → (f a , unit-trunc-Prop (a , refl))))

map-universal-property-set-quotient-trunc-Prop' :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) →
  Σ (A → type-Set B) is-weakly-constant-map → type-trunc-Prop A → type-Set B
map-universal-property-set-quotient-trunc-Prop' B (f , H) =
  map-universal-property-set-quotient-trunc-Prop B f H

abstract
  htpy-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) (f : A → type-Set B) →
    (H : is-weakly-constant-map f) →
    map-universal-property-set-quotient-trunc-Prop B f H ∘ unit-trunc-Prop ~ f
  htpy-universal-property-set-quotient-trunc-Prop B f H a =
    ap
      ( pr1)
      ( eq-is-prop'
        ( is-prop-image-is-weakly-constant-map B f H)
        ( map-universal-property-trunc-Prop
          ( image-weakly-constant-map-Prop B f H)
          ( λ x → (f x , unit-trunc-Prop (x , refl)))
          ( unit-trunc-Prop a))
        ( f a , unit-trunc-Prop (a , refl)))

  is-section-map-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) →
    ( ( precomp-universal-property-set-quotient-trunc-Prop {A = A} B) ∘
      ( map-universal-property-set-quotient-trunc-Prop' B)) ~ id
  is-section-map-universal-property-set-quotient-trunc-Prop B (f , H) =
    eq-type-subtype
      ( is-weakly-constant-map-prop-Set B)
      ( eq-htpy (htpy-universal-property-set-quotient-trunc-Prop B f H))

  is-retraction-map-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) →
    ( ( map-universal-property-set-quotient-trunc-Prop' B) ∘
      ( precomp-universal-property-set-quotient-trunc-Prop {A = A} B)) ~ id
  is-retraction-map-universal-property-set-quotient-trunc-Prop B g =
    eq-htpy
      ( ind-trunc-Prop
        ( λ x →
          Id-Prop B
            ( map-universal-property-set-quotient-trunc-Prop' B
              ( precomp-universal-property-set-quotient-trunc-Prop B g)
              ( x))
            ( g x))
        ( htpy-universal-property-set-quotient-trunc-Prop B
          ( g ∘ unit-trunc-Prop)
          ( is-weakly-constant-map-precomp-unit-trunc-Prop g)))

  universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) →
    is-equiv (precomp-universal-property-set-quotient-trunc-Prop {A = A} B)
  universal-property-set-quotient-trunc-Prop B =
    is-equiv-is-invertible
      ( map-universal-property-set-quotient-trunc-Prop' B)
      ( is-section-map-universal-property-set-quotient-trunc-Prop B)
      ( is-retraction-map-universal-property-set-quotient-trunc-Prop B)
```
