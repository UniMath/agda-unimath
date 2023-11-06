# Retracts of maps

```agda
module orthogonal-factorization-systems.retracts-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies
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
  S : s' ∘ g ~ f ∘ s  and   R : r' ∘ f ~ g ∘ r
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

### The predicate of being a retract of maps

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
      ( g ·l is-retract-retract-of r)
      ( is-retract-retract-of r' ·r g)

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

  is-retract-of-domain-retract-of-map :
    retraction-of-domain-retract-of-map ∘ section-of-domain-retract-of-map ~ id
  is-retract-of-domain-retract-of-map =
    is-retract-retract-of retract-of-domain-retract-of-map

  section-of-codomain-retract-of-map : B → Y
  section-of-codomain-retract-of-map =
    section-retract-of retract-of-codomain-retract-of-map

  retraction-of-codomain-retract-of-map : Y → B
  retraction-of-codomain-retract-of-map =
    retraction-retract-of retract-of-codomain-retract-of-map

  is-retract-of-codomain-retract-of-map :
    retraction-of-codomain-retract-of-map ∘ section-of-codomain-retract-of-map ~
    id
  is-retract-of-codomain-retract-of-map =
    is-retract-retract-of retract-of-codomain-retract-of-map

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

```text
      s''        r''
 g⁻¹x -> f⁻¹(s'x) -> g⁻¹x
  |         |         |
  |    S'   |    R'   |
  v         v         v
  A -- s -> X -- r -> A
  |         |         |
  g    S    f    R    g
  v         v         v
  B ------> Y ------> B
       s'        r'
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f)
  where

  map-section-fiber-retract-of-map :
    (y : B) → fiber g y → fiber f (section-of-codomain-retract-of-map f g k y)
  map-section-fiber-retract-of-map =
    map-fiber-square
      ( section-of-domain-retract-of-map f g k)
      ( g)
      ( f)
      ( section-of-codomain-retract-of-map f g k)
      ( coherence-section-retract-of-map f g k)

  map-retraction-fiber-retract-of-map' :
    (y : Y) →
    fiber f y → fiber g (retraction-of-codomain-retract-of-map f g k y)
  map-retraction-fiber-retract-of-map' =
    map-fiber-square
      ( retraction-of-domain-retract-of-map f g k)
      ( f)
      ( g)
      ( retraction-of-codomain-retract-of-map f g k)
      ( coherence-retraction-retract-of-map f g k)

  map-retraction-fiber-retract-of-map :
    (y : B) → fiber f (section-of-codomain-retract-of-map f g k y) → fiber g y
  pr1 (map-retraction-fiber-retract-of-map y (x , p)) =
    retraction-of-domain-retract-of-map f g k x
  pr2 (map-retraction-fiber-retract-of-map y (x , p)) =
    ( inv (coherence-retraction-retract-of-map f g k x)) ∙
    ( ap (retraction-of-codomain-retract-of-map f g k) p) ∙
    ( is-retract-of-codomain-retract-of-map f g k y)

  abstract
    coherence-is-retraction-fiber-retract-of-map :
      (y : B) ((x , p) : fiber g y) →
      (g ·l is-retract-of-domain-retract-of-map f g k) x ＝
      ( inv
        ( coherence-retraction-retract-of-map f g k
          ( pr1 (map-section-fiber-retract-of-map y (x , p))))) ∙
      ( ap
        ( retraction-of-codomain-retract-of-map f g k)
        ( pr2 (map-section-fiber-retract-of-map y (x , p)))) ∙
      ( is-retract-of-codomain-retract-of-map f g k y) ∙
      ( inv p)
    coherence-is-retraction-fiber-retract-of-map y (x , refl) =
      ( ( ( left-transpose-htpy-concat
            ( coherence-retraction-retract-of-map f g k ·r
              section-of-domain-retract-of-map f g k)
            ( g ·l is-retract-of-domain-retract-of-map f g k)
            ( ( retraction-of-codomain-retract-of-map f g k ·l
                inv-htpy (coherence-section-retract-of-map f g k)) ∙h
              ( is-retract-of-codomain-retract-of-map f g k ·r g))
            ( inv-htpy (coherence-retract-of-map f g k))) ∙h
          ( inv-htpy-assoc-htpy
            ( inv-htpy
              ( coherence-retraction-retract-of-map f g k ·r
                section-of-domain-retract-of-map f g k))
            ( retraction-of-codomain-retract-of-map f g k ·l
              inv-htpy (coherence-section-retract-of-map f g k))
            ( is-retract-of-codomain-retract-of-map f g k ·r g)))
        ( x)) ∙
      ( ap
        ( λ p →
          ( inv
            ( coherence-retraction-retract-of-map f g k
              ( section-of-domain-retract-of-map f g k x))) ∙
          ( ap (retraction-of-codomain-retract-of-map f g k) p) ∙
          ( is-retract-of-codomain-retract-of-map f g k y))
        ( inv right-unit)) ∙
      ( inv right-unit)

  is-retraction-fiber-retract-of-map :
    (y : B) →
    ( map-retraction-fiber-retract-of-map y ∘
      map-section-fiber-retract-of-map y) ~
    id
  is-retraction-fiber-retract-of-map y (x , p) =
    map-inv-fiber-ap-eq-fiber g
      ( map-retraction-fiber-retract-of-map y
        ( map-section-fiber-retract-of-map y (x , p)))
      ( x , p)
      ( ( is-retract-of-domain-retract-of-map f g k x) ,
        ( coherence-is-retraction-fiber-retract-of-map y (x , p)))

  retract-of-fiber-retract-of-map :
    (y : B) →
    ( fiber g y) retract-of
    ( fiber f (section-of-codomain-retract-of-map f g k y))
  pr1 (retract-of-fiber-retract-of-map y) =
    map-section-fiber-retract-of-map y
  pr1 (pr2 (retract-of-fiber-retract-of-map y)) =
    map-retraction-fiber-retract-of-map y
  pr2 (pr2 (retract-of-fiber-retract-of-map y)) =
    is-retraction-fiber-retract-of-map y
```

### If `g` is a retract of `f`, then the fiber projections of `g` are retracts of the fiber projections of `f`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f) (y : B)
  where

  is-retract-of-map-fiber-retract-of-map :
    is-retract-of-map
      ( pr1)
      ( pr1)
      ( retract-of-fiber-retract-of-map f g k y)
      ( retract-of-domain-retract-of-map f g k)
  pr1 is-retract-of-map-fiber-retract-of-map = refl-htpy
  pr1 (pr2 is-retract-of-map-fiber-retract-of-map) = refl-htpy
  pr2 (pr2 is-retract-of-map-fiber-retract-of-map) (x , p) =
    inv (ap-pr1-map-inv-fiber-ap-eq-fiber g _ (x , p) _)

  retract-of-map-fiber-retract-of-map : pr1 retract-of-map pr1
  pr1 retract-of-map-fiber-retract-of-map =
    retract-of-fiber-retract-of-map f g k y
  pr1 (pr2 retract-of-map-fiber-retract-of-map) =
    retract-of-domain-retract-of-map f g k
  pr2 (pr2 retract-of-map-fiber-retract-of-map) =
    is-retract-of-map-fiber-retract-of-map
```

### If `f` has a section, then retracts of `f` have a section

In fact, we only need the following data to show this:

```text
                 r
            X ------> A
            |         |
            f    R    g
            v         v
  B ------> Y ------> B.
       s'   H'   r'
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : X → A) (r' : B retract-of Y)
  (R : coherence-square-maps r f g (retraction-retract-of r'))
  (section-f : section f)
  where

  map-has-section-is-retract-of-has-section' : B → A
  map-has-section-is-retract-of-has-section' =
    r ∘ map-section f section-f ∘ section-retract-of r'

  is-section-map-has-section-is-retract-of-has-section' :
    g ∘ map-has-section-is-retract-of-has-section' ~ id
  is-section-map-has-section-is-retract-of-has-section' =
    ( inv-htpy R ·r (map-section f section-f ∘ section-retract-of r')) ∙h
    ( ( retraction-retract-of r') ·l
      ( is-section-map-section f section-f ·r section-retract-of r')) ∙h
    ( is-retract-retract-of r')

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
      ( retraction-of-domain-retract-of-map f g k)
      ( retract-of-codomain-retract-of-map f g k)
      ( coherence-retraction-retract-of-map f g k)
```

### If `f` has a retraction, then retracts of `f` have a retraction

In fact, we only need the following data to show this:

```text
       s    H    r
  A ------> X ------> A
  |         |
  g    S    f
  v         v
  B ------> Y.
       s'
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (s' : B → Y)
  (S : coherence-square-maps (section-retract-of r) g f s')
  (retraction-f : retraction f)
  where

  map-has-retraction-is-retract-of-has-retraction' : B → A
  map-has-retraction-is-retract-of-has-retraction' =
    retraction-retract-of r ∘ map-retraction f retraction-f ∘ s'

  is-retraction-map-has-retraction-is-retract-of-has-retraction' :
    map-has-retraction-is-retract-of-has-retraction' ∘ g ~ id
  is-retraction-map-has-retraction-is-retract-of-has-retraction' =
    ( ( retraction-retract-of r ∘ map-retraction f retraction-f) ·l S) ∙h
    ( ( retraction-retract-of r) ·l
      ( is-retraction-map-retraction f retraction-f ·r section-retract-of r)) ∙h
    ( is-retract-retract-of r)

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
      ( section-of-codomain-retract-of-map f g k)
      ( coherence-section-retract-of-map f g k)
```

### Equivalences are closed under retracts of maps

Note that the higher coherence of a retract of maps is not needed.

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
    has-section-is-retract-of-has-section' f g
      ( retraction-retract-of r)
      ( r')
      ( R)
      ( section-is-equiv is-equiv-f)
  pr2 is-equiv-is-retract-of-is-equiv' =
    has-retraction-is-retract-of-has-retraction' f g
      ( r)
      ( section-retract-of r')
      ( S)
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

- [Retracts in arrow categories](https://ncatlab.org/nlab/show/retract#in_arrow_categories)
  at nlab

A wikidata identifier was not available for this concept.
