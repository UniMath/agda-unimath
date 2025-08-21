# Set coequalizers

```agda
module foundation.set-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.freely-generated-equivalence-relations
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Any pair of [maps](foundation-core.function-types.md) between
[sets](foundation-core.sets.md) `f g : A → B` has a
{{#concept "coequalizer" Disambiguation="of maps between sets" Agda=coequalizer-Set WD="coequalizer" WDID=Q5140810}}
`B/A` given by the [quotient](foundation.set-quotients.md) of the set `B` by the
[relation](foundation.binary-relations.md)
[generated](foundation.freely-generated-equivalence-relations.md) by `x ~ y` if
there is some `z : A` with `f(z) = x` and `g(z) = y`. This quotient `B/A` has
the _universal property_ that any map `h : B → C` which satisfies the equation
`h ∘ f ~ h ∘ g` factors uniquely through the quotient map `B → B/A`.

## Definitions

```agda
module _
  {l : Level} (A B : Set l) (f g : type-Set A → type-Set B)
  where

  relation-coequalizer-Set : Relation l (type-Set B)
  relation-coequalizer-Set x y = Σ (type-Set A) (λ z → (f z ＝ x) × (g z ＝ y))

  path-relation-coequalizer-Set : Relation-Prop l (type-Set B)
  path-relation-coequalizer-Set = path-Relation-Prop relation-coequalizer-Set

  equivalence-relation-coequalizer-Set : equivalence-relation l (type-Set B)
  equivalence-relation-coequalizer-Set =
    ( path-relation-coequalizer-Set) ,
    ( is-equivalence-relation-path-Relation-Prop _)

  coequalizer-Set : Set l
  coequalizer-Set = quotient-Set equivalence-relation-coequalizer-Set

  class-coequalizer-Set :
    type-Set B → equivalence-class equivalence-relation-coequalizer-Set
  class-coequalizer-Set = class equivalence-relation-coequalizer-Set

  type-coequalizer-Set : UU l
  type-coequalizer-Set = type-Set coequalizer-Set

  map-coequalizer-Set : type-Set B → type-coequalizer-Set
  map-coequalizer-Set = quotient-map equivalence-relation-coequalizer-Set

  htpy-coequalizer-Set : map-coequalizer-Set ∘ f ~ map-coequalizer-Set ∘ g
  htpy-coequalizer-Set x =
    ap
      ( set-quotient-equivalence-class equivalence-relation-coequalizer-Set)
      ( eq-share-common-element-equivalence-class
        ( equivalence-relation-coequalizer-Set)
        ( class-coequalizer-Set (f x))
        ( class-coequalizer-Set (g x))
        ( intro-exists
          ( g x)
          ( ( unit-trunc-Prop
              ( 1 ,
                ( finite-path-edge-Relation relation-coequalizer-Set (f x) (g x)
                  ( inl (x , (refl , refl)))))) ,
            ( is-reflexive-path-Relation-Prop _ (g x)))))
```

## Properties

### Every map factors uniquely through the coequalizer map

When given a map `h : B → C` for `C` a set, `h` descends to the quotient
`h' : B/A → C` exactly when we have a homotopy `h ∘ f ~ h ∘ g`.

```agda
module _
  {l : Level} (A B : Set l) (f g : type-Set A → type-Set B)
  (C : Set l)
  (h : type-Set B → type-Set C)
  where

  htpy-descent-coequalizer-Set : UU l
  htpy-descent-coequalizer-Set = h ∘ f ~ h ∘ g
```

If we have a homotopy `H : h ∘ f ~ h ∘ g` and given `x, y : B` and `z : A` with
`f(z) = x` and `g(z) = y`, then `h(x) = h(y)`; thus, given `H`, `h` respects the
coequalizer equivalence relation.

```agda
  generator-reflecting-descent-coequalizer-Set :
    (H : htpy-descent-coequalizer-Set)
    (x y : type-Set B) →
    relation-coequalizer-Set A B f g x y →
    h x ＝ h y
  generator-reflecting-descent-coequalizer-Set H x y (z , p , q) =
    ( inv (ap h p)) ∙
    ( H z) ∙
    ( ap h q)

  reflecting-descent-coequalizer-Set :
    htpy-descent-coequalizer-Set →
    reflects-equivalence-relation
      ( equivalence-relation-coequalizer-Set A B f g)
      ( h)
  reflecting-descent-coequalizer-Set H =
    reflects-path-Relation-Prop (relation-coequalizer-Set A B f g) C
      ( h)
      ( generator-reflecting-descent-coequalizer-Set H)

  descent-reflecting-coequalizer-Set :
    reflects-equivalence-relation
      ( equivalence-relation-coequalizer-Set A B f g) h →
    htpy-descent-coequalizer-Set
  descent-reflecting-coequalizer-Set r x =
    r (unit-trunc-Prop (1 , (f x) , map-raise refl , inl (x , (refl , refl))))

  is-retraction-reflecting-descent-coequalizer-Set :
    descent-reflecting-coequalizer-Set ∘ reflecting-descent-coequalizer-Set ~
    id
  is-retraction-reflecting-descent-coequalizer-Set H =
    eq-is-prop (is-prop-Π (λ x → is-set-type-Set C _ _))

  is-section-reflecting-descent-coequalizer-Set :
    reflecting-descent-coequalizer-Set ∘ descent-reflecting-coequalizer-Set ~
    id
  is-section-reflecting-descent-coequalizer-Set H =
    eq-is-prop
      ( is-prop-implicit-Π
        ( λ x →
          is-prop-implicit-Π
          ( λ y →
            is-prop-Π
            ( λ z →
              is-set-type-Set C _ _))))

  is-equiv-reflecting-descent-coequalizer-Set :
    is-equiv reflecting-descent-coequalizer-Set
  is-equiv-reflecting-descent-coequalizer-Set =
    ( ( descent-reflecting-coequalizer-Set) ,
      ( is-section-reflecting-descent-coequalizer-Set)) ,
    ( ( descent-reflecting-coequalizer-Set) ,
      ( is-retraction-reflecting-descent-coequalizer-Set))

  equiv-reflecting-descent-coequalizer-Set :
    htpy-descent-coequalizer-Set ≃
    reflects-equivalence-relation
      ( equivalence-relation-coequalizer-Set A B f g) h
  equiv-reflecting-descent-coequalizer-Set =
    ( reflecting-descent-coequalizer-Set) ,
    ( is-equiv-reflecting-descent-coequalizer-Set)

  map-quotient-descent-coequalizer-Set :
    htpy-descent-coequalizer-Set → type-coequalizer-Set A B f g → type-Set C
  map-quotient-descent-coequalizer-Set H =
    inv-precomp-set-quotient
      ( equivalence-relation-coequalizer-Set A B f g)
      ( C)
      ( h , reflecting-descent-coequalizer-Set H)

  htpy-quotient-descent-coequalizer-Set :
    (H : htpy-descent-coequalizer-Set) →
    (map-quotient-descent-coequalizer-Set H) ∘ (map-coequalizer-Set A B f g) ~
    h
  htpy-quotient-descent-coequalizer-Set H =
    is-section-inv-precomp-set-quotient
      ( equivalence-relation-coequalizer-Set A B f g)
      ( C)
      ( h , (reflecting-descent-coequalizer-Set H))

module _
  {l : Level} (A B : Set l) (f g : type-Set A → type-Set B)
  (C : Set l)
  where

  descent-coequalizer-Set : UU l
  descent-coequalizer-Set =
    Σ (type-Set B → type-Set C) (λ h → htpy-descent-coequalizer-Set A B f g C h)

  equiv-descent-coequalizer-Set :
    descent-coequalizer-Set ≃
    reflecting-map-equivalence-relation
      ( equivalence-relation-coequalizer-Set A B f g)
      ( type-Set C)
  equiv-descent-coequalizer-Set =
    equiv-tot (equiv-reflecting-descent-coequalizer-Set A B f g C)
```

## See also

- [Set quotients](foundation.set-quotients.md) for the construction used here.
