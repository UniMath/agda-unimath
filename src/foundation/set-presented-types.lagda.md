# Set presented types

```agda
module foundation.set-presented-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.images
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

A type `A` is said to be {{#concept "set presented" Agda=has-set-presentation}}
if there [exists](foundation.existential-quantification.md) a map `f : X → A`
from a [set](foundation-core.sets.md) `X` such that the composite
`η ∘ f : X → A → ║A║₀` is an [equivalence](foundation.equivalences.md).

## Definitions

### The underlying structure of a set presentation

```agda
is-set-presentation-map :
  {l1 l2 : Level} {A : UU l1} (X : Set l2) → (type-Set X → A) → UU (l1 ⊔ l2)
is-set-presentation-map X f = is-equiv (unit-trunc-Set ∘ f)

set-presentation-structure : {l1 l2 : Level} → UU l1 → Set l2 → UU (l1 ⊔ l2)
set-presentation-structure A X = Σ (type-Set X → A) (is-set-presentation-map X)

module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : set-presentation-structure A X)
  where

  map-set-presentation-structure : type-Set X → A
  map-set-presentation-structure = pr1 f

  is-set-presentation-map-map-set-presentation-structure :
    is-set-presentation-map X map-set-presentation-structure
  is-set-presentation-map-map-set-presentation-structure = pr2 f
```

### The predicate on a set of being a set presentation of a type

```agda
module _
  {l1 l2 : Level} (A : UU l1) (X : Set l2)
  where

  is-set-presentation-Prop : Prop (l1 ⊔ l2)
  is-set-presentation-Prop = trunc-Prop (set-presentation-structure A X)

  is-set-presentation : UU (l1 ⊔ l2)
  is-set-presentation = type-Prop is-set-presentation-Prop

  is-prop-is-set-presentation : is-prop is-set-presentation
  is-prop-is-set-presentation = is-prop-type-Prop is-set-presentation-Prop
```

### The type of set presentations of a type at a universe level

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  set-presentation : UU (l1 ⊔ lsuc l2)
  set-presentation = Σ (Set l2) (is-set-presentation A)

  is-1-type-set-presentation : is-1-type set-presentation
  is-1-type-set-presentation =
    is-1-type-type-subtype (is-set-presentation-Prop A) is-1-type-Set
```

### The predicate of having a set presentation at a universe level

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  has-set-presentation-Prop : Prop (l1 ⊔ lsuc l2)
  has-set-presentation-Prop = trunc-Prop (set-presentation l2 A)

  has-set-presentation : UU (l1 ⊔ lsuc l2)
  has-set-presentation = type-Prop has-set-presentation-Prop

  is-prop-has-set-presentation : is-prop has-set-presentation
  is-prop-has-set-presentation = is-prop-type-Prop has-set-presentation-Prop
```

## Propositions

### Types set presented by coproducts are coproducts

Given a type `A` that is set presented by a coproduct

```text
              A
            ∧   \
         f /     \ η
          /   ~   ∨
  (X1 + X2) -----> ║A║₀,
```

then `A` computes as the coproduct of the images of the restrictions of `f`
along the left and right inclusion of the coproduct `X1 + X2`

```text
  A ≃ im (f ∘ inl) + im (f ∘ inr).
```

```agda
module _
  {l1 l2 l3 : Level} {X1 : UU l1} {X2 : UU l2} {A : UU l3}
  (f : X1 + X2 → A) (e : (X1 + X2) ≃ ║ A ║₀)
  (H : unit-trunc-Set ∘ f ~ map-equiv e)
  where

  map-is-coproduct-codomain : (im (f ∘ inl) + im (f ∘ inr)) → A
  map-is-coproduct-codomain = rec-coproduct pr1 pr1

  triangle-is-coproduct-codomain :
    ( ( map-is-coproduct-codomain) ∘
      ( map-coproduct (map-unit-im (f ∘ inl)) (map-unit-im (f ∘ inr)))) ~ f
  triangle-is-coproduct-codomain (inl x) = refl
  triangle-is-coproduct-codomain (inr x) = refl

  abstract
    is-emb-map-is-coproduct-codomain : is-emb map-is-coproduct-codomain
    is-emb-map-is-coproduct-codomain =
      is-emb-coproduct
        ( is-emb-inclusion-subtype (λ b → trunc-Prop _))
        ( is-emb-inclusion-subtype (λ b → trunc-Prop _))
        ( λ (b1 , u) (b2 , v) →
          apply-twice-universal-property-trunc-Prop u v
            ( function-Prop _ empty-Prop)
            ( λ where
              ( x , refl) (y , refl) r →
                is-empty-eq-coproduct-inl-inr x y
                  ( is-injective-is-equiv
                    ( is-equiv-map-equiv e)
                    ( ( inv (H (inl x))) ∙
                      ( ap unit-trunc-Set r) ∙
                      ( H (inr y))))))

  abstract
    is-surjective-map-is-coproduct-codomain :
      is-surjective map-is-coproduct-codomain
    is-surjective-map-is-coproduct-codomain b =
      map-trunc-Prop
        ( λ p →
          ( map-coproduct
            ( map-unit-im (f ∘ inl))
            ( map-unit-im (f ∘ inr))
            ( a)) ,
          ( triangle-is-coproduct-codomain a ∙ inv p))
        ( apply-effectiveness-unit-trunc-Set
          ( inv (is-section-map-inv-equiv e (unit-trunc-Set b)) ∙ inv (H a)))
      where
      a : X1 + X2
      a = map-inv-equiv e (unit-trunc-Set b)

  is-coproduct-codomain : (im (f ∘ inl) + im (f ∘ inr)) ≃ A
  pr1 is-coproduct-codomain = map-is-coproduct-codomain
  pr2 is-coproduct-codomain =
    is-equiv-is-emb-is-surjective
      is-surjective-map-is-coproduct-codomain
      is-emb-map-is-coproduct-codomain
```
