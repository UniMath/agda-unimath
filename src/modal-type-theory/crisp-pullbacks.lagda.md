# Crisp pullbacks

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-pullbacks
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-cospan-diagrams
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.universe-levels

open import modal-type-theory.action-on-identifications-crisp-functions
open import modal-type-theory.action-on-identifications-flat-modality
open import modal-type-theory.crisp-dependent-pair-types
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-discrete-crisp-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

We say a [pullback](foundation-core.pullbacks.md) is
{{#concept "crisp" Disambiguation="pullback"}} if it is formed in a
[crisp context](modal-type-theory.crisp-types.md).

**Comment.** The results in this file should hold more generally for
[crisp maps defined on crisp elements](modal-type-theory.crisp-function-types.md)
`@♭ f : @♭ A → X` and `@♭ g : @♭ B → X`.

## Properties

### Flat distributes over standard pullbacks

```agda
module _
  {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ X : UU l3}
  (@♭ f : A → X) (@♭ g : B → X)
  where

  map-distributive-flat-standard-pullback :
    ♭ (standard-pullback f g) →
    standard-pullback (action-flat-map f) (action-flat-map g)
  map-distributive-flat-standard-pullback (intro-flat (x , y , p)) =
    ( intro-flat x , intro-flat y , ap-flat p)

  map-inv-distributive-flat-standard-pullback :
    @♭ standard-pullback (action-flat-map f) (action-flat-map g) →
    ♭ (standard-pullback f g)
  map-inv-distributive-flat-standard-pullback
    (intro-flat x , intro-flat y , p) =
    intro-flat (x , y , ap counit-flat p)

  is-crisp-section-map-distributive-flat-standard-pullback :
    (@♭ x : ♭ (standard-pullback f g)) →
    map-inv-distributive-flat-standard-pullback
      ( map-distributive-flat-standard-pullback x) ＝
    ( x)
  is-crisp-section-map-distributive-flat-standard-pullback
    ( intro-flat (x , y , p)) =
    crisp-ap
      ( intro-flat)
      ( eq-pair-eq-fiber
        ( eq-pair-eq-fiber
          ( is-crisp-section-ap-flat p)))

  is-crisp-retraction-map-distributive-flat-standard-pullback :
    (@♭ x : standard-pullback (action-flat-map f) (action-flat-map g)) →
    map-distributive-flat-standard-pullback
      ( map-inv-distributive-flat-standard-pullback x) ＝
    ( x)
  is-crisp-retraction-map-distributive-flat-standard-pullback
    ( intro-flat x , intro-flat y , p) =
      eq-pair-eq-fiber
        ( eq-pair-eq-fiber
          ( crisp-based-ind-Id
            ( λ where
              (intro-flat y) p → crisp-ap intro-flat (ap counit-flat p) ＝ p)
            ( refl)
            ( p)))
```

### Computing the flat counit on a standard pullback

The counit of the flat modality computes as the counit on each component of a
crisp dependent pair type.

```agda
module _
  {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ X : UU l3}
  (@♭ f : A → X) (@♭ g : B → X)
  where

  counit-flat-hom-cospan-diagram :
    hom-cospan-diagram (action-flat-map f) (action-flat-map g) f g
  counit-flat-hom-cospan-diagram =
    ( counit-flat ,
      counit-flat ,
      counit-flat ,
      inv-htpy (naturality-counit-flat f) ,
      inv-htpy (naturality-counit-flat g))

  compute-counit-flat-standard-pullback :
    ( map-standard-pullback
      ( f)
      ( g)
      ( action-flat-map f)
      ( action-flat-map g)
      ( counit-flat-hom-cospan-diagram)) ∘
    ( map-distributive-flat-standard-pullback f g) ~
    counit-flat {A = standard-pullback f g}
  compute-counit-flat-standard-pullback (intro-flat (x , y , p)) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( right-unit ∙ is-crisp-section-ap-flat p))
```

### A crisp standard pullback is flat discrete if its factors are

```agda
module _
  {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ X : UU l3}
  (@♭ f : A → X) (@♭ g : B → X)
  where

  is-flat-discrete-crisp-standard-pullback-is-flat-discrete-crisp-factors :
    is-flat-discrete-crisp X →
    is-flat-discrete-crisp A →
    is-flat-discrete-crisp B →
    is-flat-discrete-crisp (standard-pullback f g)
  is-flat-discrete-crisp-standard-pullback-is-flat-discrete-crisp-factors
    bX bA bB =
    is-flat-discrete-crisp-Σ
      ( bA)
      ( λ a →
        is-flat-discrete-crisp-Σ
        ( bB)
        ( λ b → is-flat-discrete-crisp-Id (is-emb-is-equiv bX)))
```

### A crisp pullback is flat discrete if its factors are

```agda
module _
  {@♭ l1 l2 l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {@♭ X : UU l3}
  (@♭ f : A → X) (@♭ g : B → X)
  where

  is-flat-discrete-crisp-pullback-is-flat-discrete-crisp-factors :
    {@♭ l4 : Level} {@♭ C : UU l4} (@♭ c : cone f g C) →
    @♭ is-pullback f g c →
    is-flat-discrete-crisp X →
    is-flat-discrete-crisp A →
    is-flat-discrete-crisp B →
    is-flat-discrete-crisp C
  is-flat-discrete-crisp-pullback-is-flat-discrete-crisp-factors c H bX bA bB =
    is-flat-discrete-crisp-equiv'
      ( gap f g c , H)
      ( is-flat-discrete-crisp-standard-pullback-is-flat-discrete-crisp-factors
        ( f)
        ( g)
        ( bX)
        ( bA)
        ( bB))
```

## References

{{#bibliography}} {{#reference Shu18}}
