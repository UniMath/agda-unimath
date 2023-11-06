# Retracts of maps

```agda
module foundation.retracts-of-maps where
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
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies
```

</details>

## Idea

A **retract** of a map `f : X → Y` is a map `g : A → B` that is a retract in the
arrow category of types. Hence, it consists of
[retracts](foundation-core.retractions.md) `A` of `X` and `B` of `Y` that fit
into a commutative diagram

```text
         i         r
    A ------> X ------> A
    |         |         |
  g |    I    | f   R   | g
    v         v         v
    B ------> Y ------> B
         i'        r'
```

with coherences

```text
  I : i' ∘ g ~ f ∘ i  and   R : r' ∘ f ~ g ∘ r
```

witnessing that the left and right
[squares commute](foundation-core.commuting-squares-of-maps.md), and a higher
coherence

```text
                   R ·r i
       r' ∘ f ∘ i --------> g ∘ r ∘ i
            |                |
            |                |
  r' ·l I⁻¹ |        L       | g ·l H
            |                |
            V                V
      r' ∘ i' ∘ g ---------> g
                   H' ·r g
```

witnessing that the
[square of homotopies](foundation.commuting-squares-of-homotopies.md) commutes,
where `H` and `H'` are the retracting homotopies of `r ∘ i` and `r' ∘ i'`
respectively.

## Definition

### The higher coherence in the definition of retracts of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (r' : B retract-of Y)
  where

  coherence-retract-of-map :
    coherence-square-maps (inclusion-retract r) g f (inclusion-retract r') →
    coherence-square-maps
      ( map-retraction-retract r) f g (map-retraction-retract r') →
    UU (l1 ⊔ l2)
  coherence-retract-of-map S R =
    coherence-square-homotopies
      ( R ·r inclusion-retract r)
      ( map-retraction-retract r' ·l inv-htpy S)
      ( g ·l is-retraction-map-retraction-retract r)
      ( is-retraction-map-retraction-retract r' ·r g)
```

### The predicate of being a retract of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (r' : B retract-of Y)
  where

  is-retract-of-map : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-retract-of-map =
    Σ ( coherence-square-maps (inclusion-retract r) g f (inclusion-retract r'))
      ( λ S →
        Σ ( coherence-square-maps
            ( map-retraction-retract r)
            ( f)
            ( g)
            ( map-retraction-retract r'))
          ( coherence-retract-of-map f g r r' S))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (r' : B retract-of Y)
  (k : is-retract-of-map f g r r')
  where

  coh-inclusion-is-retract-of-map :
    coherence-square-maps (inclusion-retract r) g f (inclusion-retract r')
  coh-inclusion-is-retract-of-map = pr1 k

  coh-retraction-is-retract-of-map :
    coherence-square-maps
      ( map-retraction-retract r) f g (map-retraction-retract r')
  coh-retraction-is-retract-of-map = pr1 (pr2 k)

  coh-is-retract-of-map :
    coherence-retract-of-map f g r r'
      coh-inclusion-is-retract-of-map
      coh-retraction-is-retract-of-map
  coh-is-retract-of-map = pr2 (pr2 k)
```

### The predicate that a map is a retract of a map `f`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  retract-map : (X → Y) → (A → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  retract-map f g =
    Σ (retract X A) (λ r → Σ (retract Y B) (is-retract-of-map f g r))
```

### The binary relation `g f ↦ g retract-of-map f` asserting that `g` is a retract of the map `f`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (g : A → B) (f : X → Y)
  where

  infix 6 _retract-of-map_

  _retract-of-map_ : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  _retract-of-map_ = retract-map f g

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f)
  where

  retract-domain-retract-map : A retract-of X
  retract-domain-retract-map = pr1 k

  retract-codomain-retract-map : B retract-of Y
  retract-codomain-retract-map = pr1 (pr2 k)

  is-retract-of-map-retract-map :
    is-retract-of-map f g
      retract-domain-retract-map
      retract-codomain-retract-map
  is-retract-of-map-retract-map = pr2 (pr2 k)

  inclusion-domain-retract-map : A → X
  inclusion-domain-retract-map =
    inclusion-retract retract-domain-retract-map

  retraction-domain-retract-map :
    retraction inclusion-domain-retract-map
  retraction-domain-retract-map =
    retraction-retract retract-domain-retract-map

  map-retraction-domain-retract-map : X → A
  map-retraction-domain-retract-map =
    map-retraction-retract retract-domain-retract-map

  is-retraction-map-retraction-domain-retract-map :
    is-retraction
      inclusion-domain-retract-map
      map-retraction-domain-retract-map
  is-retraction-map-retraction-domain-retract-map =
    is-retraction-map-retraction-retract retract-domain-retract-map

  inclusion-codomain-retract-map : B → Y
  inclusion-codomain-retract-map =
    inclusion-retract retract-codomain-retract-map

  retraction-codomain-retract-map :
    retraction inclusion-codomain-retract-map
  retraction-codomain-retract-map =
    retraction-retract retract-codomain-retract-map

  map-retraction-codomain-retract-map : Y → B
  map-retraction-codomain-retract-map =
    map-retraction-retract retract-codomain-retract-map

  is-retraction-map-retraction-codomain-retract-map :
    is-retraction
      inclusion-codomain-retract-map
      map-retraction-codomain-retract-map
  is-retraction-map-retraction-codomain-retract-map =
    is-retraction-map-retraction-retract retract-codomain-retract-map

  coh-inclusion-retract-map :
    coherence-square-maps
      ( inclusion-domain-retract-map)
      ( g)
      ( f)
      ( inclusion-codomain-retract-map)
  coh-inclusion-retract-map =
    coh-inclusion-is-retract-of-map f g
      ( retract-domain-retract-map)
      ( retract-codomain-retract-map)
      ( is-retract-of-map-retract-map)

  coh-map-retraction-retract-map :
    coherence-square-maps
      ( map-retraction-domain-retract-map)
      ( f)
      ( g)
      ( map-retraction-codomain-retract-map)
  coh-map-retraction-retract-map =
    coh-retraction-is-retract-of-map f g
      ( retract-domain-retract-map)
      ( retract-codomain-retract-map)
      ( is-retract-of-map-retract-map)

  coh-retract-map :
    coherence-retract-of-map f g
      retract-domain-retract-map
      retract-codomain-retract-map
      coh-inclusion-retract-map
      coh-map-retraction-retract-map
  coh-retract-map =
    coh-is-retract-of-map f g
      ( retract-domain-retract-map)
      ( retract-codomain-retract-map)
      ( is-retract-of-map-retract-map)
```

## Properties

### If `g` is a retract of `f`, then the fibers of `g` are retracts of the fibers of `f`

```text
           i''                 r''
  fib g x -----> fib f (i' x) -----> fib g x
     |               |                  |
     |       I'      |          R'      |
     v               v                  v
     A ----- i ----> X ------ r ------> A
     |               |                  |
   g |       I       f          R       | g
     v               v                  v
     B ------------> Y ---------------> B
             i'               r'
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f)
  where

  inclusion-fiber-retract-map :
    (y : B) → fiber g y → fiber f (inclusion-codomain-retract-map f g k y)
  inclusion-fiber-retract-map =
    map-fiber-square
      ( inclusion-domain-retract-map f g k)
      ( g)
      ( f)
      ( inclusion-codomain-retract-map f g k)
      ( coh-inclusion-retract-map f g k)

  map-retraction-fiber-retract-map' :
    (y : Y) →
    fiber f y → fiber g (map-retraction-codomain-retract-map f g k y)
  map-retraction-fiber-retract-map' =
    map-fiber-square
      ( map-retraction-domain-retract-map f g k)
      ( f)
      ( g)
      ( map-retraction-codomain-retract-map f g k)
      ( coh-map-retraction-retract-map f g k)

  map-retraction-fiber-retract-map :
    (y : B) → fiber f (inclusion-codomain-retract-map f g k y) → fiber g y
  pr1 (map-retraction-fiber-retract-map y (x , p)) =
    map-retraction-domain-retract-map f g k x
  pr2 (map-retraction-fiber-retract-map y (x , p)) =
    ( inv (coh-map-retraction-retract-map f g k x)) ∙
    ( ap (map-retraction-codomain-retract-map f g k) p) ∙
    ( is-retraction-map-retraction-codomain-retract-map f g k y)

  coherence-is-retraction-fiber-retract-map :
    (y : B) (z : fiber g y) →
    ( g ·l is-retraction-map-retraction-domain-retract-map f g k)
      ( inclusion-fiber g z) ＝
    ( inv
      ( coh-map-retraction-retract-map f g k
        ( inclusion-fiber f (inclusion-fiber-retract-map y z)))) ∙
    ( ap
      ( map-retraction-codomain-retract-map f g k)
      ( compute-value-inclusion-fiber f (inclusion-fiber-retract-map y z))) ∙
    ( is-retraction-map-retraction-codomain-retract-map f g k y) ∙
    ( inv (compute-value-inclusion-fiber g z))
  coherence-is-retraction-fiber-retract-map y (x , refl) =
    ( ( ( left-transpose-htpy-concat
          ( coh-map-retraction-retract-map f g k ·r
            inclusion-domain-retract-map f g k)
          ( g ·l is-retraction-map-retraction-domain-retract-map f g k)
          ( ( map-retraction-codomain-retract-map f g k ·l
              inv-htpy (coh-inclusion-retract-map f g k)) ∙h
            ( is-retraction-map-retraction-codomain-retract-map f g k ·r g))
          ( inv-htpy (coh-retract-map f g k))) ∙h
        ( inv-htpy-assoc-htpy
          ( inv-htpy
            ( coh-map-retraction-retract-map f g k ·r
              inclusion-domain-retract-map f g k))
          ( map-retraction-codomain-retract-map f g k ·l
            inv-htpy (coh-inclusion-retract-map f g k))
          ( is-retraction-map-retraction-codomain-retract-map f g k ·r g)))
      ( x)) ∙
    ( ap
      ( λ p →
        ( inv
          ( coh-map-retraction-retract-map f g k
            ( inclusion-domain-retract-map f g k x))) ∙
        ( ap (map-retraction-codomain-retract-map f g k) p) ∙
        ( is-retraction-map-retraction-codomain-retract-map f g k y))
      ( inv right-unit)) ∙
    ( inv right-unit)

  is-retraction-fiber-retract-map :
    (y : B) →
    is-retraction
      ( inclusion-fiber-retract-map y)
      ( map-retraction-fiber-retract-map y)
  is-retraction-fiber-retract-map y z =
    map-inv-fiber-ap-eq-fiber g
      ( map-retraction-fiber-retract-map y
        ( inclusion-fiber-retract-map y z))
      ( z)
      ( ( is-retraction-map-retraction-domain-retract-map f g k
          ( inclusion-fiber g z)) ,
        ( coherence-is-retraction-fiber-retract-map y z))

  retract-fiber-retract-map :
    (y : B) →
    ( fiber g y) retract-of
    ( fiber f (inclusion-codomain-retract-map f g k y))
  pr1 (retract-fiber-retract-map y) =
    inclusion-fiber-retract-map y
  pr1 (pr2 (retract-fiber-retract-map y)) =
    map-retraction-fiber-retract-map y
  pr2 (pr2 (retract-fiber-retract-map y)) =
    is-retraction-fiber-retract-map y
```

### If `g` is a retract of `f`, then the fiber inclusions of `g` are retracts of the fiber inclusions of `f`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f) (y : B)
  where

  is-retract-map-fiber-retract-map :
    is-retract-of-map
      ( inclusion-fiber f)
      ( inclusion-fiber g)
      ( retract-fiber-retract-map f g k y)
      ( retract-domain-retract-map f g k)
  pr1 is-retract-map-fiber-retract-map =
    refl-htpy
  pr1 (pr2 is-retract-map-fiber-retract-map) =
    refl-htpy
  pr2 (pr2 is-retract-map-fiber-retract-map) z =
    inv (ap-pr1-map-inv-fiber-ap-eq-fiber g _ z _)

  retract-map-fiber-retract-map :
    (inclusion-fiber g) retract-of-map (inclusion-fiber f)
  pr1 retract-map-fiber-retract-map =
    retract-fiber-retract-map f g k y
  pr1 (pr2 retract-map-fiber-retract-map) =
    retract-domain-retract-map f g k
  pr2 (pr2 retract-map-fiber-retract-map) =
    is-retract-map-fiber-retract-map
```

### If `f` has a section, then retracts of `f` have a section

In fact, we only need the following data to show this:

```text
                 r
            X ------> A
            |         |
          f |    R    | g
            v         v
  B ------> Y ------> B.
       s'   H'   r'
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : X → A) (r' : B retract-of Y)
  (R : coherence-square-maps r f g (map-retraction-retract r'))
  (section-f : section f)
  where

  map-section-is-retract-of-section' : B → A
  map-section-is-retract-of-section' =
    r ∘ map-section f section-f ∘ inclusion-retract r'

  is-section-map-section-is-retract-of-section' :
    is-section g map-section-is-retract-of-section'
  is-section-map-section-is-retract-of-section' =
    ( inv-htpy R ·r (map-section f section-f ∘ inclusion-retract r')) ∙h
    ( ( map-retraction-retract r') ·l
      ( is-section-map-section f section-f ·r inclusion-retract r')) ∙h
    ( is-retraction-map-retraction-retract r')

  section-is-retract-of-section' : section g
  pr1 section-is-retract-of-section' =
    map-section-is-retract-of-section'
  pr2 section-is-retract-of-section' =
    is-section-map-section-is-retract-of-section'

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f)
  where

  section-retract-section : section f → section g
  section-retract-section =
    section-is-retract-of-section' f g
      ( map-retraction-domain-retract-map f g k)
      ( retract-codomain-retract-map f g k)
      ( coh-map-retraction-retract-map f g k)
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
  (S : coherence-square-maps (inclusion-retract r) g f s')
  (retraction-f : retraction f)
  where

  map-has-retraction-is-retract-of-has-retraction' : B → A
  map-has-retraction-is-retract-of-has-retraction' =
    map-retraction-retract r ∘ map-retraction f retraction-f ∘ s'

  is-retraction-map-has-retraction-is-retract-of-has-retraction' :
    map-has-retraction-is-retract-of-has-retraction' ∘ g ~ id
  is-retraction-map-has-retraction-is-retract-of-has-retraction' =
    ( ( map-retraction-retract r ∘ map-retraction f retraction-f) ·l S) ∙h
    ( ( map-retraction-retract r) ·l
      ( is-retraction-map-retraction f retraction-f ·r inclusion-retract r)) ∙h
    ( is-retraction-map-retraction-retract r)

  has-retraction-is-retract-of-has-retraction' : retraction g
  pr1 has-retraction-is-retract-of-has-retraction' =
    map-has-retraction-is-retract-of-has-retraction'
  pr2 has-retraction-is-retract-of-has-retraction' =
    is-retraction-map-has-retraction-is-retract-of-has-retraction'

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f)
  where

  has-map-retraction-retract-has-retraction : retraction f → retraction g
  has-map-retraction-retract-has-retraction =
    has-retraction-is-retract-of-has-retraction' f g
      ( retract-domain-retract-map f g k)
      ( inclusion-codomain-retract-map f g k)
      ( coh-inclusion-retract-map f g k)
```

### Equivalences are closed under retracts of maps

Note that the higher coherence of a retract of maps is not needed.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (r : A retract-of X) (r' : B retract-of Y)
  (S : coherence-square-maps (inclusion-retract r) g f (inclusion-retract r'))
  (R :
    coherence-square-maps
      ( map-retraction-retract r)
      ( f)
      ( g)
      ( map-retraction-retract r'))
  (H : is-equiv f)
  where

  is-equiv-is-retract-of-is-equiv' : is-equiv g
  pr1 is-equiv-is-retract-of-is-equiv' =
    section-is-retract-of-section' f g
      ( map-retraction-retract r)
      ( r')
      ( R)
      ( section-is-equiv H)
  pr2 is-equiv-is-retract-of-is-equiv' =
    has-retraction-is-retract-of-has-retraction' f g
      ( r)
      ( inclusion-retract r')
      ( S)
      ( retraction-is-equiv H)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : X → Y) (g : A → B) (k : g retract-of-map f) (H : is-equiv f)
  where

  section-retract-of-is-equiv : section g
  section-retract-of-is-equiv =
    section-retract-section f g k (section-is-equiv H)

  retraction-retract-of-is-equiv : retraction g
  retraction-retract-of-is-equiv =
    has-map-retraction-retract-has-retraction f g k (retraction-is-equiv H)

  is-equiv-retract-of-is-equiv : is-equiv g
  pr1 is-equiv-retract-of-is-equiv = section-retract-of-is-equiv
  pr2 is-equiv-retract-of-is-equiv = retraction-retract-of-is-equiv
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
