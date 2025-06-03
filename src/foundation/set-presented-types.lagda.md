# Set presented types

```agda
module foundation.set-presented-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.images
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.set-truncations
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

A type `A` is said to be
{{#concept "set presented" Agda=has-set-presentation-Prop}} if there
[exists](foundation.existential-quantification.md) a map `f : X → A` from a
[set](foundation-core.sets.md) `X` such that the composite
`X → A → type-trunc-Set A` is an [equivalence](foundation.equivalences.md).

## Definitions

### Set presentations of types

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : UU l2)
  where

  has-set-presentation-Prop : Prop (l1 ⊔ l2)
  has-set-presentation-Prop =
    ∃ (type-Set A → B) (λ f → is-equiv-Prop (unit-trunc-Set ∘ f))

  has-set-presentation : UU (l1 ⊔ l2)
  has-set-presentation = type-Prop has-set-presentation-Prop

  is-prop-has-set-presentation : is-prop has-set-presentation
  is-prop-has-set-presentation = is-prop-type-Prop has-set-presentation-Prop
```

## Propositions

### Types set presented by coproducts are coproducts

Given a type `B` that is set presented by a coproduct

```text
              B
            ∧   \
         f /     \ η
          /   ~   ∨
  (A1 + A2) -----> ║B║₀,
```

then `B` computes as the coproduct of the images of the restrictions of `f`
along the left and right inclusion of the coproduct `A1 + A2`

```text
  B ≃ im (f ∘ inl) + im (f ∘ inr).
```

```agda
module _
  {l1 l2 l3 : Level} {A1 : UU l1} {A2 : UU l2} {B : UU l3}
  (f : A1 + A2 → B) (e : (A1 + A2) ≃ ║ B ║₀)
  (H : unit-trunc-Set ∘ f ~ map-equiv e)
  where

  map-is-coproduct-codomain : (im (f ∘ inl) + im (f ∘ inr)) → B
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
          apply-universal-property-trunc-Prop u
            ( function-Prop _ empty-Prop)
            ( λ where
              ( x , refl) →
                apply-universal-property-trunc-Prop v
                  ( function-Prop _ empty-Prop)
                  ( λ where
                    ( y , refl) r →
                      is-empty-eq-coproduct-inl-inr x y
                        ( is-injective-is-equiv
                          ( is-equiv-map-equiv e)
                          ( ( inv (H (inl x))) ∙
                            ( ap unit-trunc-Set r) ∙
                            ( H (inr y)))))))

  abstract
    is-surjective-map-is-coproduct-codomain :
      is-surjective map-is-coproduct-codomain
    is-surjective-map-is-coproduct-codomain b =
      apply-universal-property-trunc-Prop
        ( apply-effectiveness-unit-trunc-Set
          ( inv (is-section-map-inv-equiv e (unit-trunc-Set b)) ∙ inv (H a)))
        ( trunc-Prop (fiber map-is-coproduct-codomain b))
        ( λ p →
          unit-trunc-Prop
            ( ( map-coproduct
                ( map-unit-im (f ∘ inl))
                ( map-unit-im (f ∘ inr))
                ( a)) ,
              ( triangle-is-coproduct-codomain a ∙ inv p)))
      where
      a : A1 + A2
      a = map-inv-equiv e (unit-trunc-Set b)

  is-coproduct-codomain : (im (f ∘ inl) + im (f ∘ inr)) ≃ B
  pr1 is-coproduct-codomain = map-is-coproduct-codomain
  pr2 is-coproduct-codomain =
    is-equiv-is-emb-is-surjective
      is-surjective-map-is-coproduct-codomain
      is-emb-map-is-coproduct-codomain
```
