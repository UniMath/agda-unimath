# Retracts of maps

```agda
module orthogonal-factorization-systems.retracts-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.monomorphisms
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **retract** of `f : X → Y` is a map `g : A → B` that is a retract in the arrow
category of types. Hence, it consists of
[retracts](foundation-core.retractions.md) `A` of `X` and `B` of `Y` that fit
into a commutative diagram

```text
       s         r
  A ------> X ------> A
  |         |         |
  g    S    f    R    g
  v         v         v
  B ------> Y ------> B
       s'        r'
```

with coherences

```text
  S : s' ∘ g ~ f ∘ s  and   R : r' ∘ f ~ g ∘ r'
```

and a higher coherence

```text
                  R ·r s
       r' ∘ f ∘ s ------ g ∘ r ∘ s
            |                |
            |                |
  r' ·l S⁻¹ |        L       | g ·l H
            |                |
            |                |
      r' ∘ s' ∘ g ---------- g
                  H' ·r g
```

Where `H` and `H'` are the retracting homotopies of `r ∘ s` and `r' ∘ s'`
respectively.

## Definition

### The predicate of being a predicate of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (r' : B retract-of Y)
  where

  statement-coherence-is-retract-of-map :
    coherence-square-maps (section-retract-of r) g f (section-retract-of r') →
    coherence-square-maps
      ( retraction-retract-of r) f g (retraction-retract-of r') →
    UU (l1 ⊔ l2)
  statement-coherence-is-retract-of-map S R =
    coherence-square-homotopies
      ( R ·r section-retract-of r)
      ( retraction-retract-of r' ·l inv-htpy S)
      ( g ·l is-retraction-retract-of r)
      ( is-retraction-retract-of r' ·r g)

  is-retract-of-map : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-retract-of-map =
    Σ ( coherence-square-maps
        ( section-retract-of r) g f (section-retract-of r'))
      ( λ S →
        Σ ( coherence-square-maps
            ( retraction-retract-of r) f g (retraction-retract-of r'))
          ( statement-coherence-is-retract-of-map S))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (r' : B retract-of Y)
  (k : is-retract-of-map f g r r')
  where

  coherence-section-is-retract-of-map :
    coherence-square-maps (section-retract-of r) g f (section-retract-of r')
  coherence-section-is-retract-of-map = pr1 k

  coherence-retraction-is-retract-of-map :
    coherence-square-maps
      ( retraction-retract-of r) f g (retraction-retract-of r')
  coherence-retraction-is-retract-of-map = pr1 (pr2 k)

  coherence-is-retract-of-map :
    statement-coherence-is-retract-of-map f g r r'
      coherence-section-is-retract-of-map
      coherence-retraction-is-retract-of-map
  coherence-is-retract-of-map = pr2 (pr2 k)
```

### The type of retracts of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (g : A → B) (f : X → Y)
  where

  _retract-of-map_ : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  _retract-of-map_ =
    Σ (A retract-of X) (λ r → Σ (B retract-of Y) (is-retract-of-map f g r))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f)
  where

  retract-of-domain-retract-of-map : A retract-of X
  retract-of-domain-retract-of-map = pr1 k

  retract-of-codomain-retract-of-map : B retract-of Y
  retract-of-codomain-retract-of-map = pr1 (pr2 k)

  is-retract-of-map-retract-of-map :
    is-retract-of-map f g
      retract-of-domain-retract-of-map
      retract-of-codomain-retract-of-map
  is-retract-of-map-retract-of-map = pr2 (pr2 k)

  section-of-domain-retract-of-map : A → X
  section-of-domain-retract-of-map =
    section-retract-of retract-of-domain-retract-of-map

  retraction-of-domain-retract-of-map : X → A
  retraction-of-domain-retract-of-map =
    retraction-retract-of retract-of-domain-retract-of-map

  is-retraction-of-domain-retract-of-map :
    retraction-of-domain-retract-of-map ∘ section-of-domain-retract-of-map ~ id
  is-retraction-of-domain-retract-of-map =
    is-retraction-retract-of retract-of-domain-retract-of-map

  section-of-codomain-retract-of-map : B → Y
  section-of-codomain-retract-of-map =
    section-retract-of retract-of-codomain-retract-of-map

  retraction-of-codomain-retract-of-map : Y → B
  retraction-of-codomain-retract-of-map =
    retraction-retract-of retract-of-codomain-retract-of-map

  is-retraction-of-codomain-retract-of-map :
    retraction-of-codomain-retract-of-map ∘ section-of-codomain-retract-of-map ~
    id
  is-retraction-of-codomain-retract-of-map =
    is-retraction-retract-of retract-of-codomain-retract-of-map

  coherence-section-retract-of-map :
    coherence-square-maps
      ( section-of-domain-retract-of-map)
      ( g)
      ( f)
      ( section-of-codomain-retract-of-map)
  coherence-section-retract-of-map =
    coherence-section-is-retract-of-map f g
      ( retract-of-domain-retract-of-map)
      ( retract-of-codomain-retract-of-map)
      ( is-retract-of-map-retract-of-map)

  coherence-retraction-retract-of-map :
    coherence-square-maps
      ( retraction-of-domain-retract-of-map)
      ( f)
      ( g)
      ( retraction-of-codomain-retract-of-map)
  coherence-retraction-retract-of-map =
    coherence-retraction-is-retract-of-map f g
      ( retract-of-domain-retract-of-map)
      ( retract-of-codomain-retract-of-map)
      ( is-retract-of-map-retract-of-map)

  coherence-retract-of-map :
    statement-coherence-is-retract-of-map f g
      retract-of-domain-retract-of-map
      retract-of-codomain-retract-of-map
      coherence-section-retract-of-map
      coherence-retraction-retract-of-map
  coherence-retract-of-map =
    coherence-is-retract-of-map f g
      ( retract-of-domain-retract-of-map)
      ( retract-of-codomain-retract-of-map)
      ( is-retract-of-map-retract-of-map)
```

## Properties

### If `g` is a retract of `f`, then the fibers of `g` are retracts of the fibers of `f`

This remains to be formalized.

Note that none of the following results require the higher order coherence.

### If `f` has a section, then retracts of `f` have a section

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (r' : B retract-of Y)
  (S : coherence-square-maps (section-retract-of r) g f (section-retract-of r'))
  (R :
    coherence-square-maps
      ( retraction-retract-of r) f g (retraction-retract-of r'))
  (section-f : section f)
  where

  map-has-section-is-retract-of-has-section' : B → A
  map-has-section-is-retract-of-has-section' =
    retraction-retract-of r ∘
    map-section f section-f ∘
    section-retract-of r'

  is-section-map-has-section-is-retract-of-has-section' :
    g ∘ map-has-section-is-retract-of-has-section' ~ id
  is-section-map-has-section-is-retract-of-has-section' =
    ( inv-htpy R ·r (map-section f section-f ∘ section-retract-of r')) ∙h
    ( ( retraction-retract-of r') ·l
      ( is-section-map-section f section-f ·r section-retract-of r')) ∙h
    ( is-retraction-retract-of r')

  has-section-is-retract-of-has-section' : section g
  pr1 has-section-is-retract-of-has-section' =
    map-has-section-is-retract-of-has-section'
  pr2 has-section-is-retract-of-has-section' =
    is-section-map-has-section-is-retract-of-has-section'

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f)
  where

  has-section-retract-of-has-section : section f → section g
  has-section-retract-of-has-section =
    has-section-is-retract-of-has-section' f g
      ( retract-of-domain-retract-of-map f g k)
      ( retract-of-codomain-retract-of-map f g k)
      ( coherence-section-retract-of-map f g k)
      ( coherence-retraction-retract-of-map f g k)
```

### If `f` has a retraction, then retracts of `f` have a retraction

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (r' : B retract-of Y)
  (S : coherence-square-maps (section-retract-of r) g f (section-retract-of r'))
  (R :
    coherence-square-maps
      ( retraction-retract-of r) f g (retraction-retract-of r'))
  (retraction-f : retraction f)
  where

  map-has-retraction-is-retract-of-has-retraction' : B → A
  map-has-retraction-is-retract-of-has-retraction' =
    retraction-retract-of r ∘
    map-retraction f retraction-f ∘
    section-retract-of r'

  is-retraction-map-has-retraction-is-retract-of-has-retraction' :
    map-has-retraction-is-retract-of-has-retraction' ∘ g ~ id
  is-retraction-map-has-retraction-is-retract-of-has-retraction' =
    ( ( retraction-retract-of r ∘ map-retraction f retraction-f) ·l S) ∙h
    ( ( retraction-retract-of r) ·l
      ( is-retraction-map-retraction f retraction-f ·r section-retract-of r)) ∙h
    ( is-retraction-retract-of r)

  has-retraction-is-retract-of-has-retraction' : retraction g
  pr1 has-retraction-is-retract-of-has-retraction' =
    map-has-retraction-is-retract-of-has-retraction'
  pr2 has-retraction-is-retract-of-has-retraction' =
    is-retraction-map-has-retraction-is-retract-of-has-retraction'

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f)
  where

  has-retraction-retract-of-has-retraction : retraction f → retraction g
  has-retraction-retract-of-has-retraction =
    has-retraction-is-retract-of-has-retraction' f g
      ( retract-of-domain-retract-of-map f g k)
      ( retract-of-codomain-retract-of-map f g k)
      ( coherence-section-retract-of-map f g k)
      ( coherence-retraction-retract-of-map f g k)
```

### Equivalences are closed under retracts of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (r' : B retract-of Y)
  (S : coherence-square-maps (section-retract-of r) g f (section-retract-of r'))
  (R :
    coherence-square-maps
      ( retraction-retract-of r) f g (retraction-retract-of r'))
  (is-equiv-f : is-equiv f)
  where

  is-equiv-is-retract-of-is-equiv' : is-equiv g
  pr1 is-equiv-is-retract-of-is-equiv' =
    has-section-is-retract-of-has-section' f g r r' S R
      ( section-is-equiv is-equiv-f)
  pr2 is-equiv-is-retract-of-is-equiv' =
    has-retraction-is-retract-of-has-retraction' f g r r' S R
      ( retraction-is-equiv is-equiv-f)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f) (is-equiv-f : is-equiv f)
  where

  is-equiv-retract-of-is-equiv : is-equiv g
  pr1 is-equiv-retract-of-is-equiv =
    has-section-retract-of-has-section f g k
      ( section-is-equiv is-equiv-f)
  pr2 is-equiv-retract-of-is-equiv =
    has-retraction-retract-of-has-retraction f g k
      ( retraction-is-equiv is-equiv-f)
```

## References

1. Section 4.7 of Univalent Foundations Project, _Homotopy Type Theory –
   Univalent Foundations of Mathematics_ (2013)
   ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729))

## External links

- [retract#In arrow categories](https://ncatlab.org/nlab/show/retract#in_arrow_categories)
  at nlab

A wikidata identifier was not available for this concept.
