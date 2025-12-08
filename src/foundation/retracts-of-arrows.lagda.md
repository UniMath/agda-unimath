# Retracts of arrows

```agda
module foundation.retracts-of-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-prisms-of-maps
open import foundation.commuting-triangles-of-morphisms-arrows
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.function-extensionality
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies-morphisms-arrows
open import foundation.homotopy-algebra
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.constant-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.retracts-of-types
open import foundation-core.sections
```

</details>

## Idea

A map `f : A → B` is said to be a
{{#concept "retract" Disambiguation="of arrows of types" Agda=retract-arrow}} of
a map `g : X → Y` if it is a retract in the arrow category of types. In other
words, `f` is a retract of `g` if there are
[morphisms of arrows](foundation.morphisms-arrows.md) `i : f → g` and
`r : g → f` equipped with a homotopy of morphisms of arrows `r ∘ i ~ id`.

More explicitly, it consists of [retracts](foundation-core.retractions.md) `A`
of `X` and `B` of `Y` that fit into a commutative diagram

```text
         i₀        r₀
    A ------> X ------> A
    |         |         |
  f |    i    | g   r   | f
    ∨         ∨         ∨
    B ------> Y ------> B
         i₁        r₁
```

with coherences

```text
  i : i₁ ∘ f ~ g ∘ i₀  and   r : r₁ ∘ g ~ f ∘ r₀
```

witnessing that the left and right
[squares commute](foundation-core.commuting-squares-of-maps.md), and a higher
coherence

```text
                     r ·r i₀
       r₁ ∘ g ∘ i₀ ----------> f ∘ r₀ ∘ i₀
            |                      |
            |                      |
  r₁ ·l i⁻¹ |          L           | f ·l H₀
            |                      |
            ∨                      ∨
      r₁ ∘ i₁ ∘ f ---------------> f
                       H₁ ·r f
```

witnessing that the
[square of homotopies](foundation.commuting-squares-of-homotopies.md) commutes,
where `H₀` and `H₁` are the retracting homotopies of `r₀ ∘ i₀` and `r₁ ∘ i₁`
respectively.

This coherence requirement arises from the implicit requirement that the total
pasting of the retraction square should restrict to the reflexivity homotopy on
the square

```text
    A ========= A
    |           |
  f | refl-htpy | f
    ∨           ∨
    B ========= B,
```

as we are asking for the morphisms to compose to the identity morphism of
arrows.

## Definition

### The predicate of being a retraction of a morphism of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (i : hom-arrow f g) (r : hom-arrow g f)
  where

  is-retraction-hom-arrow : UU (l1 ⊔ l2)
  is-retraction-hom-arrow = coherence-triangle-hom-arrow' f g f id-hom-arrow r i
```

### The type of retractions of a morphism of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (i : hom-arrow f g)
  where

  retraction-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  retraction-hom-arrow = Σ (hom-arrow g f) (is-retraction-hom-arrow f g i)

  module _
    (r : retraction-hom-arrow)
    where

    hom-retraction-hom-arrow : hom-arrow g f
    hom-retraction-hom-arrow = pr1 r

    is-retraction-hom-retraction-hom-arrow :
      is-retraction-hom-arrow f g i hom-retraction-hom-arrow
    is-retraction-hom-retraction-hom-arrow = pr2 r
```

### The predicate that a morphism `f` is a retract of a morphism `g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  retract-arrow : (g : X → Y) (f : A → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  retract-arrow g f = Σ (hom-arrow f g) (retraction-hom-arrow f g)
```

### The higher coherence in the definition of retracts of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (i : hom-arrow f g) (r : hom-arrow g f)
  (H : is-retraction (map-domain-hom-arrow f g i) (map-domain-hom-arrow g f r))
  (H' :
    is-retraction
      ( map-codomain-hom-arrow f g i)
      ( map-codomain-hom-arrow g f r))
  where

  coherence-retract-arrow : UU (l1 ⊔ l2)
  coherence-retract-arrow =
    coherence-htpy-hom-arrow f f (comp-hom-arrow f g f r i) id-hom-arrow H H'
```

### The binary relation `f g ↦ f retract-of-arrow g` asserting that `f` is a retract of the map `g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  infix 6 _retract-of-map_

  _retract-of-map_ : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  _retract-of-map_ = retract-arrow g f

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-arrow g)
  where

  inclusion-retract-arrow : hom-arrow f g
  inclusion-retract-arrow = pr1 R

  map-domain-inclusion-retract-arrow : A → X
  map-domain-inclusion-retract-arrow =
    map-domain-hom-arrow f g inclusion-retract-arrow

  map-codomain-inclusion-retract-arrow : B → Y
  map-codomain-inclusion-retract-arrow =
    map-codomain-hom-arrow f g inclusion-retract-arrow

  coh-inclusion-retract-arrow :
    coherence-square-maps
      ( map-domain-inclusion-retract-arrow)
      ( f)
      ( g)
      ( map-codomain-inclusion-retract-arrow)
  coh-inclusion-retract-arrow =
    coh-hom-arrow f g inclusion-retract-arrow

  retraction-retract-arrow : retraction-hom-arrow f g inclusion-retract-arrow
  retraction-retract-arrow = pr2 R

  hom-retraction-retract-arrow : hom-arrow g f
  hom-retraction-retract-arrow =
    hom-retraction-hom-arrow f g inclusion-retract-arrow retraction-retract-arrow

  map-domain-hom-retraction-retract-arrow : X → A
  map-domain-hom-retraction-retract-arrow =
    map-domain-hom-arrow g f hom-retraction-retract-arrow

  map-codomain-hom-retraction-retract-arrow : Y → B
  map-codomain-hom-retraction-retract-arrow =
    map-codomain-hom-arrow g f hom-retraction-retract-arrow

  coh-hom-retraction-retract-arrow :
    coherence-square-maps
      ( map-domain-hom-retraction-retract-arrow)
      ( g)
      ( f)
      ( map-codomain-hom-retraction-retract-arrow)
  coh-hom-retraction-retract-arrow =
    coh-hom-arrow g f hom-retraction-retract-arrow

  is-retraction-hom-retraction-retract-arrow :
    is-retraction-hom-arrow f g inclusion-retract-arrow hom-retraction-retract-arrow
  is-retraction-hom-retraction-retract-arrow =
    is-retraction-hom-retraction-hom-arrow f g
      ( inclusion-retract-arrow)
      ( retraction-retract-arrow)

  is-retraction-map-domain-hom-retraction-retract-arrow :
    is-retraction
      ( map-domain-inclusion-retract-arrow)
      ( map-domain-hom-retraction-retract-arrow)
  is-retraction-map-domain-hom-retraction-retract-arrow =
    htpy-domain-htpy-hom-arrow f f
      ( comp-hom-arrow f g f hom-retraction-retract-arrow inclusion-retract-arrow)
      ( id-hom-arrow)
      ( is-retraction-hom-retraction-retract-arrow)

  retract-domain-retract-arrow :
    A retract-of X
  pr1 retract-domain-retract-arrow =
    map-domain-inclusion-retract-arrow
  pr1 (pr2 retract-domain-retract-arrow) =
    map-domain-hom-retraction-retract-arrow
  pr2 (pr2 retract-domain-retract-arrow) =
    is-retraction-map-domain-hom-retraction-retract-arrow

  is-retraction-map-codomain-hom-retraction-retract-arrow :
    is-retraction
      ( map-codomain-inclusion-retract-arrow)
      ( map-codomain-hom-retraction-retract-arrow)
  is-retraction-map-codomain-hom-retraction-retract-arrow =
    htpy-codomain-htpy-hom-arrow f f
      ( comp-hom-arrow f g f hom-retraction-retract-arrow inclusion-retract-arrow)
      ( id-hom-arrow)
      ( is-retraction-hom-retraction-retract-arrow)

  retract-codomain-retract-arrow : B retract-of Y
  pr1 retract-codomain-retract-arrow =
    map-codomain-inclusion-retract-arrow
  pr1 (pr2 retract-codomain-retract-arrow) =
    map-codomain-hom-retraction-retract-arrow
  pr2 (pr2 retract-codomain-retract-arrow) =
    is-retraction-map-codomain-hom-retraction-retract-arrow

  coh-retract-arrow :
    coherence-retract-arrow f g
      ( inclusion-retract-arrow)
      ( hom-retraction-retract-arrow)
      ( is-retraction-map-domain-hom-retraction-retract-arrow)
      ( is-retraction-map-codomain-hom-retraction-retract-arrow)
  coh-retract-arrow =
    coh-htpy-hom-arrow f f
      ( comp-hom-arrow f g f hom-retraction-retract-arrow inclusion-retract-arrow)
      ( id-hom-arrow)
      ( is-retraction-hom-retraction-retract-arrow)
```

## Properties

### Retracts of arrows with sections have sections

In fact, we only need the following data to show this:

```text
                 r₀
            X ------> A
            |         |
          g |    r    | f
            ∨         ∨
  B ------> Y ------> B.
       i₁   H₁   r₁
```

**Proof:** Note that `f` is the right map of a triangle

```text
            r₀
       X ------> A
        \       /
  r₁ ∘ g \     / f
          \   /
           ∨ ∨
            B.
```

Since both `r₁` and `g` are assumed to have
[sections](foundation-core.sections.md), it follows that the composite `r₁ ∘ g`
has a section, and therefore `f` has a section.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (r₀ : X → A) (R₁ : B retract-of Y)
  (r : coherence-square-maps r₀ g f (map-retraction-retract R₁))
  (s : section g)
  where

  section-retract-arrow-section' : section f
  section-retract-arrow-section' =
    section-right-map-triangle
      ( map-retraction-retract R₁ ∘ g)
      ( f)
      ( r₀)
      ( r)
      ( section-comp (map-retraction-retract R₁) g s (section-retract R₁))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-arrow g)
  where

  section-retract-arrow-section : section g → section f
  section-retract-arrow-section =
    section-retract-arrow-section' f g
      ( map-domain-hom-retraction-retract-arrow f g R)
      ( retract-codomain-retract-arrow f g R)
      ( coh-hom-retraction-retract-arrow f g R)
```

### Retracts of arrows with retractions have retractions

In fact, we only need the following data to show this:

```text
         i₀   H   r₀
    A ------> X ------> A
    |         |
  f |    i    | g
    ∨         ∨
    B ------> Y.
         i₁
```

**Proof:** Note that `f` is the top map in the triangle

```text
            f
       A ------> B
        \       /
  g ∘ i₀ \     / i₁
          \   /
           ∨ ∨
            Y.
```

Since both `g` and `i₀` are assumed to have retractions, it follows that
`g ∘ i₀` has a retraction, and hence that `f` has a retraction.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R₀ : A retract-of X) (i₁ : B → Y)
  (i : coherence-square-maps (inclusion-retract R₀) f g i₁)
  (s : retraction g)
  where

  retraction-retract-arrow-retraction' : retraction f
  retraction-retract-arrow-retraction' =
    retraction-top-map-triangle'
      ( g ∘ inclusion-retract R₀)
      ( i₁)
      ( f)
      ( i)
      ( retraction-comp g (inclusion-retract R₀) s (retraction-retract R₀))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-arrow g)
  where

  retraction-retract-arrow-retraction : retraction g → retraction f
  retraction-retract-arrow-retraction =
    retraction-retract-arrow-retraction' f g
      ( retract-domain-retract-arrow f g R)
      ( map-codomain-inclusion-retract-arrow f g R)
      ( coh-inclusion-retract-arrow f g R)
```

### Equivalences are closed under retracts of arrows

We may observe that the higher coherence of a retract of maps is not needed.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R₀ : A retract-of X) (R₁ : B retract-of Y)
  (i : coherence-square-maps (inclusion-retract R₀) f g (inclusion-retract R₁))
  (r :
    coherence-square-maps
      ( map-retraction-retract R₀)
      ( g)
      ( f)
      ( map-retraction-retract R₁))
  (H : is-equiv g)
  where

  is-equiv-retract-arrow-is-equiv' : is-equiv f
  pr1 is-equiv-retract-arrow-is-equiv' =
    section-retract-arrow-section' f g
      ( map-retraction-retract R₀)
      ( R₁)
      ( r)
      ( section-is-equiv H)
  pr2 is-equiv-retract-arrow-is-equiv' =
    retraction-retract-arrow-retraction' f g
      ( R₀)
      ( inclusion-retract R₁)
      ( i)
      ( retraction-is-equiv H)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-arrow g) (H : is-equiv g)
  where

  section-retract-arrow-is-equiv : section f
  section-retract-arrow-is-equiv =
    section-retract-arrow-section f g R (section-is-equiv H)

  retraction-retract-arrow-is-equiv : retraction f
  retraction-retract-arrow-is-equiv =
    retraction-retract-arrow-retraction f g R (retraction-is-equiv H)

  is-equiv-retract-arrow-is-equiv : is-equiv f
  pr1 is-equiv-retract-arrow-is-equiv = section-retract-arrow-is-equiv
  pr2 is-equiv-retract-arrow-is-equiv = retraction-retract-arrow-is-equiv
```

### If `f` is a retract of `g`, then the fiber inclusions of `f` are retracts of the fiber inclusions of `g`

Consider a retract `f : A → B` of a map `g : X → Y`, as indicated in the bottom
row of squares in the diagram below.

```text
              j                     s
  fiber f b -----> fiber g (i₁ b) -----> fiber f b
     |                 |                    |
     |       i'        |         r'         |
     ∨                 ∨                    ∨
     A ----- i₀ -----> X ------- r₀ ------> A
     |                 |                    |
   f |       i         | g       r          | f
     ∨                 ∨                    ∨
     B --------------> Y -----------------> B
             i₁                  r₁
```

Then we claim that the [fiber inclusion](foundation-core.fibers-of-maps.md)
`fiber f b → A` is a retract of the fiber inclusion `fiber g (i' x) → X`.

**Proof:** By
[functoriality of fibers of maps](foundation.functoriality-fibers-of-maps.md) we
obtain a commuting diagram

```text
              j                     s                          ≃
  fiber f b -----> fiber g (i₁ b) -----> fiber f (r₀ (i₀ b)) -----> fiber f b
     |                 |                       |                        |
     |       i'        |           r'          |                        |
     ∨                 ∨                       ∨                        ∨
     A --------------> X --------------------> A ---------------------> A
             i₀                    r₀                       id
```

which is homotopic to the identity morphism of arrows. We then finish off the
proof with the following steps:

1. We reassociate the composition of morphisms of fibers, which is associated in
   the above diagram as `□ (□ □)`.
2. Then we use that `hom-arrow-fiber` preserves composition.
3. Next, we apply the action on `htpy-hom-arrow` of `fiber`.
4. Finally, we use that `hom-arrow-fiber` preserves identity morphisms of
   arrows.

While each of these steps are very simple to formalize, the operations that are
involved take a lot of arguments and therefore the code is somewhat lengthy.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-arrow g) (b : B)
  where

  inclusion-retract-arrow-inclusion-fiber-retract-arrow :
    hom-arrow
      ( inclusion-fiber f {b})
      ( inclusion-fiber g {map-codomain-inclusion-retract-arrow f g R b})
  inclusion-retract-arrow-inclusion-fiber-retract-arrow =
    hom-arrow-fiber f g (inclusion-retract-arrow f g R) b

  hom-retraction-retract-arrow-inclusion-fiber-retract-arrow :
    hom-arrow
      ( inclusion-fiber g {map-codomain-inclusion-retract-arrow f g R b})
      ( inclusion-fiber f {b})
  hom-retraction-retract-arrow-inclusion-fiber-retract-arrow =
    comp-hom-arrow
      ( inclusion-fiber g)
      ( inclusion-fiber f)
      ( inclusion-fiber f)
      ( tr-hom-arrow-inclusion-fiber f
        ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R b))
      ( hom-arrow-fiber g f
        ( hom-retraction-retract-arrow f g R)
        ( map-codomain-inclusion-retract-arrow f g R b))

  is-retraction-hom-retraction-retract-arrow-inclusion-fiber-retract-arrow :
    is-retraction-hom-arrow
      ( inclusion-fiber f)
      ( inclusion-fiber g)
      ( inclusion-retract-arrow-inclusion-fiber-retract-arrow)
      ( hom-retraction-retract-arrow-inclusion-fiber-retract-arrow)
  is-retraction-hom-retraction-retract-arrow-inclusion-fiber-retract-arrow =
    concat-htpy-hom-arrow
      ( inclusion-fiber f)
      ( inclusion-fiber f)
      ( comp-hom-arrow
        ( inclusion-fiber f)
        ( inclusion-fiber g)
        ( inclusion-fiber f)
        ( comp-hom-arrow
          ( inclusion-fiber g)
          ( inclusion-fiber f)
          ( inclusion-fiber f)
          ( tr-hom-arrow-inclusion-fiber f
            ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R b))
          ( hom-arrow-fiber g f
            ( hom-retraction-retract-arrow f g R)
            ( map-codomain-inclusion-retract-arrow f g R b)))
        ( inclusion-retract-arrow-inclusion-fiber-retract-arrow))
      ( comp-hom-arrow
        ( inclusion-fiber f)
        ( inclusion-fiber f)
        ( inclusion-fiber f)
        ( tr-hom-arrow-inclusion-fiber f
          ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R b))
        ( comp-hom-arrow
          ( inclusion-fiber f)
          ( inclusion-fiber g)
          ( inclusion-fiber f)
          ( hom-arrow-fiber g f
            ( hom-retraction-retract-arrow f g R)
            ( map-codomain-inclusion-retract-arrow f g R b))
          ( inclusion-retract-arrow-inclusion-fiber-retract-arrow)))
      ( id-hom-arrow)
      ( inv-assoc-comp-hom-arrow
        ( inclusion-fiber f)
        ( inclusion-fiber g)
        ( inclusion-fiber f)
        ( inclusion-fiber f)
        ( tr-hom-arrow-inclusion-fiber f
          ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R b))
        ( hom-arrow-fiber g f
          ( hom-retraction-retract-arrow f g R)
          ( map-codomain-inclusion-retract-arrow f g R b))
        ( inclusion-retract-arrow-inclusion-fiber-retract-arrow))
      ( concat-htpy-hom-arrow
        ( inclusion-fiber f)
        ( inclusion-fiber f)
        ( comp-hom-arrow
          ( inclusion-fiber f)
          ( inclusion-fiber f)
          ( inclusion-fiber f)
          ( tr-hom-arrow-inclusion-fiber f
            ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R b))
          ( comp-hom-arrow
            ( inclusion-fiber f)
            ( inclusion-fiber g)
            ( inclusion-fiber f)
            ( hom-arrow-fiber g f
              ( hom-retraction-retract-arrow f g R)
              ( map-codomain-inclusion-retract-arrow f g R b))
            ( inclusion-retract-arrow-inclusion-fiber-retract-arrow)))
        ( comp-hom-arrow
          ( inclusion-fiber f)
          ( inclusion-fiber f)
          ( inclusion-fiber f)
          ( tr-hom-arrow-inclusion-fiber f
            ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R b))
          ( hom-arrow-fiber f f
            ( comp-hom-arrow f g f
              ( hom-retraction-retract-arrow f g R)
              ( inclusion-retract-arrow f g R))
            ( b)))
        ( id-hom-arrow)
        ( left-whisker-comp-hom-arrow
          ( inclusion-fiber f)
          ( inclusion-fiber f)
          ( inclusion-fiber f)
          ( tr-hom-arrow-inclusion-fiber f
            ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R b))
          ( comp-hom-arrow
            ( inclusion-fiber f)
            ( inclusion-fiber g)
            ( inclusion-fiber f)
            ( hom-arrow-fiber g f
              ( hom-retraction-retract-arrow f g R)
              ( map-codomain-inclusion-retract-arrow f g R b))
            ( hom-arrow-fiber f g (inclusion-retract-arrow f g R) b))
          ( hom-arrow-fiber f f
            ( comp-hom-arrow f g f
              ( hom-retraction-retract-arrow f g R)
              ( inclusion-retract-arrow f g R))
            ( b))
          ( inv-htpy-hom-arrow
            ( inclusion-fiber f)
            ( inclusion-fiber f)
            ( hom-arrow-fiber f f
              ( comp-hom-arrow f g f
                ( hom-retraction-retract-arrow f g R)
                ( inclusion-retract-arrow f g R))
              ( b))
            ( comp-hom-arrow
              ( inclusion-fiber f)
              ( inclusion-fiber g)
              ( inclusion-fiber f)
              ( hom-arrow-fiber g f
                ( hom-retraction-retract-arrow f g R)
                ( map-codomain-inclusion-retract-arrow f g R b))
              ( hom-arrow-fiber f g (inclusion-retract-arrow f g R) b))
            ( preserves-comp-hom-arrow-fiber f g f
              ( hom-retraction-retract-arrow f g R)
              ( inclusion-retract-arrow f g R)
              ( b))))
        ( concat-htpy-hom-arrow
          ( inclusion-fiber f)
          ( inclusion-fiber f)
          ( comp-hom-arrow
            ( inclusion-fiber f)
            ( inclusion-fiber f)
            ( inclusion-fiber f)
            ( tr-hom-arrow-inclusion-fiber f
              ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R b))
            ( hom-arrow-fiber f f
              ( comp-hom-arrow f g f
                ( hom-retraction-retract-arrow f g R)
                ( inclusion-retract-arrow f g R))
              ( b)))
          ( hom-arrow-fiber f f id-hom-arrow b)
          ( id-hom-arrow)
          ( htpy-hom-arrow-fiber f f
            ( comp-hom-arrow f g f
              ( hom-retraction-retract-arrow f g R)
              ( inclusion-retract-arrow f g R))
            ( id-hom-arrow)
            ( is-retraction-hom-retraction-retract-arrow f g R)
            ( b))
          ( preserves-id-hom-arrow-fiber f b)))

  retract-arrow-inclusion-fiber-retract-arrow :
    retract-arrow
      ( inclusion-fiber g {map-codomain-inclusion-retract-arrow f g R b})
      ( inclusion-fiber f {b})
  pr1 retract-arrow-inclusion-fiber-retract-arrow =
    inclusion-retract-arrow-inclusion-fiber-retract-arrow
  pr1 (pr2 retract-arrow-inclusion-fiber-retract-arrow) =
    hom-retraction-retract-arrow-inclusion-fiber-retract-arrow
  pr2 (pr2 retract-arrow-inclusion-fiber-retract-arrow) =
    is-retraction-hom-retraction-retract-arrow-inclusion-fiber-retract-arrow
```

### If `f` is a retract of `g`, then the fibers of `f` are retracts of the fibers of `g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-arrow g) (b : B)
  where

  retract-fiber-retract-arrow :
    retract
      ( fiber g (map-codomain-inclusion-retract-arrow f g R b))
      ( fiber f b)
  retract-fiber-retract-arrow =
    retract-domain-retract-arrow
      ( inclusion-fiber f)
      ( inclusion-fiber g)
      ( retract-arrow-inclusion-fiber-retract-arrow f g R b)
```

### If `f` is a retract of `g`, then `- ∘ f` is a retract of `- ∘ g`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-arrow g) (S : UU l5)
  where

  inclusion-precomp-retract-arrow : hom-arrow (precomp f S) (precomp g S)
  inclusion-precomp-retract-arrow =
    precomp-hom-arrow g f (hom-retraction-retract-arrow f g R) S

  hom-retraction-precomp-retract-arrow : hom-arrow (precomp g S) (precomp f S)
  hom-retraction-precomp-retract-arrow =
    precomp-hom-arrow f g (inclusion-retract-arrow f g R) S

  is-retraction-map-domain-precomp-retract-arrow :
    is-retraction
      ( map-domain-hom-arrow
        ( precomp f S)
        ( precomp g S)
        ( inclusion-precomp-retract-arrow))
      ( map-domain-hom-arrow
        ( precomp g S)
        ( precomp f S)
        ( hom-retraction-precomp-retract-arrow))
  is-retraction-map-domain-precomp-retract-arrow =
    htpy-precomp (is-retraction-map-codomain-hom-retraction-retract-arrow f g R) S

  is-retraction-map-codomain-precomp-retract-arrow :
    is-retraction
      ( map-codomain-hom-arrow
        ( precomp f S)
        ( precomp g S)
        ( inclusion-precomp-retract-arrow))
      ( map-codomain-hom-arrow
        ( precomp g S)
        ( precomp f S)
        ( hom-retraction-precomp-retract-arrow))
  is-retraction-map-codomain-precomp-retract-arrow =
    htpy-precomp (is-retraction-map-domain-hom-retraction-retract-arrow f g R) S

  coh-retract-precomp-retract-arrow :
    coherence-retract-arrow
      ( precomp f S)
      ( precomp g S)
      ( inclusion-precomp-retract-arrow)
      ( hom-retraction-precomp-retract-arrow)
      ( is-retraction-map-domain-precomp-retract-arrow)
      ( is-retraction-map-codomain-precomp-retract-arrow)
  coh-retract-precomp-retract-arrow =
    ( precomp-vertical-coherence-prism-inv-triangles-maps
      ( id)
      ( map-domain-hom-retraction-retract-arrow f g R)
      ( map-domain-inclusion-retract-arrow f g R)
      ( id)
      ( map-codomain-hom-retraction-retract-arrow f g R)
      ( map-codomain-inclusion-retract-arrow f g R)
      ( f)
      ( g)
      ( f)
      ( is-retraction-map-domain-hom-retraction-retract-arrow f g R)
      ( refl-htpy)
      ( coh-hom-retraction-retract-arrow f g R)
      ( coh-inclusion-retract-arrow f g R)
      ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R)
      ( coh-retract-arrow f g R)
      ( S)) ∙h
    ( ap-concat-htpy
      ( is-retraction-map-codomain-precomp-retract-arrow ·r precomp f S)
      ( λ x → ap inv (eq-htpy-refl-htpy (precomp f S x))))

  is-retraction-hom-retraction-precomp-retract-arrow :
    is-retraction-hom-arrow
      ( precomp f S)
      ( precomp g S)
      ( inclusion-precomp-retract-arrow)
      ( hom-retraction-precomp-retract-arrow)
  pr1 is-retraction-hom-retraction-precomp-retract-arrow =
    is-retraction-map-domain-precomp-retract-arrow
  pr1 (pr2 is-retraction-hom-retraction-precomp-retract-arrow) =
    is-retraction-map-codomain-precomp-retract-arrow
  pr2 (pr2 is-retraction-hom-retraction-precomp-retract-arrow) =
    coh-retract-precomp-retract-arrow

  retraction-precomp-retract-arrow :
    retraction-hom-arrow
      ( precomp f S)
      ( precomp g S)
      ( inclusion-precomp-retract-arrow)
  pr1 retraction-precomp-retract-arrow =
    hom-retraction-precomp-retract-arrow
  pr2 retraction-precomp-retract-arrow =
    is-retraction-hom-retraction-precomp-retract-arrow

  retract-arrow-precomp-retract-arrow : (precomp f S) retract-of-arrow (precomp g S)
  pr1 retract-arrow-precomp-retract-arrow = inclusion-precomp-retract-arrow
  pr2 retract-arrow-precomp-retract-arrow = retraction-precomp-retract-arrow
```

### If `f` is a retract of `g`, then `f ∘ -` is a retract of `g ∘ -`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (R : f retract-of-arrow g) (S : UU l5)
  where

  inclusion-postcomp-retract-arrow : hom-arrow (postcomp S f) (postcomp S g)
  inclusion-postcomp-retract-arrow =
    postcomp-hom-arrow f g (inclusion-retract-arrow f g R) S

  hom-retraction-postcomp-retract-arrow : hom-arrow (postcomp S g) (postcomp S f)
  hom-retraction-postcomp-retract-arrow =
    postcomp-hom-arrow g f (hom-retraction-retract-arrow f g R) S

  is-retraction-map-domain-postcomp-retract-arrow :
    is-retraction
      ( map-domain-hom-arrow
        ( postcomp S f)
        ( postcomp S g)
        ( inclusion-postcomp-retract-arrow))
      ( map-domain-hom-arrow
        ( postcomp S g)
        ( postcomp S f)
        ( hom-retraction-postcomp-retract-arrow))
  is-retraction-map-domain-postcomp-retract-arrow =
    htpy-postcomp S (is-retraction-map-domain-hom-retraction-retract-arrow f g R)

  is-retraction-map-codomain-postcomp-retract-arrow :
    is-retraction
      ( map-codomain-hom-arrow
        ( postcomp S f)
        ( postcomp S g)
        ( inclusion-postcomp-retract-arrow))
      ( map-codomain-hom-arrow
        ( postcomp S g)
        ( postcomp S f)
        ( hom-retraction-postcomp-retract-arrow))
  is-retraction-map-codomain-postcomp-retract-arrow =
    htpy-postcomp S
      ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R)

  coh-retract-postcomp-retract-arrow :
    coherence-retract-arrow
      ( postcomp S f)
      ( postcomp S g)
      ( inclusion-postcomp-retract-arrow)
      ( hom-retraction-postcomp-retract-arrow)
      ( is-retraction-map-domain-postcomp-retract-arrow)
      ( is-retraction-map-codomain-postcomp-retract-arrow)
  coh-retract-postcomp-retract-arrow =
    ( postcomp-vertical-coherence-prism-inv-triangles-maps
      ( id)
      ( map-domain-hom-retraction-retract-arrow f g R)
      ( map-domain-inclusion-retract-arrow f g R)
      ( id)
      ( map-codomain-hom-retraction-retract-arrow f g R)
      ( map-codomain-inclusion-retract-arrow f g R)
      ( f)
      ( g)
      ( f)
      ( is-retraction-map-domain-hom-retraction-retract-arrow f g R)
      ( refl-htpy)
      ( coh-hom-retraction-retract-arrow f g R)
      ( coh-inclusion-retract-arrow f g R)
      ( is-retraction-map-codomain-hom-retraction-retract-arrow f g R)
      ( coh-retract-arrow f g R)
      ( S)) ∙h
    ( ap-concat-htpy
      ( is-retraction-map-codomain-postcomp-retract-arrow ·r postcomp S f)
      ( eq-htpy-refl-htpy ∘ postcomp S f))

  is-retraction-hom-retraction-postcomp-retract-arrow :
    is-retraction-hom-arrow
      ( postcomp S f)
      ( postcomp S g)
      ( inclusion-postcomp-retract-arrow)
      ( hom-retraction-postcomp-retract-arrow)
  pr1 is-retraction-hom-retraction-postcomp-retract-arrow =
    is-retraction-map-domain-postcomp-retract-arrow
  pr1 (pr2 is-retraction-hom-retraction-postcomp-retract-arrow) =
    is-retraction-map-codomain-postcomp-retract-arrow
  pr2 (pr2 is-retraction-hom-retraction-postcomp-retract-arrow) =
    coh-retract-postcomp-retract-arrow

  retraction-postcomp-retract-arrow :
    retraction-hom-arrow
      ( postcomp S f)
      ( postcomp S g)
      ( inclusion-postcomp-retract-arrow)
  pr1 retraction-postcomp-retract-arrow =
    hom-retraction-postcomp-retract-arrow
  pr2 retraction-postcomp-retract-arrow =
    is-retraction-hom-retraction-postcomp-retract-arrow

  retract-arrow-postcomp-retract-arrow :
    (postcomp S f) retract-of-arrow (postcomp S g)
  pr1 retract-arrow-postcomp-retract-arrow = inclusion-postcomp-retract-arrow
  pr2 retract-arrow-postcomp-retract-arrow = retraction-postcomp-retract-arrow
```

### If `A` is a retract of `B` and `S` is a retract of `T` then `diagonal-exponential A S` is a retract of `diagonal-exponential B T`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {S : UU l3} {T : UU l4}
  (R : A retract-of B) (Q : S retract-of T)
  where

  inclusion-diagonal-exponential-retract :
    hom-arrow (diagonal-exponential A S) (diagonal-exponential B T)
  inclusion-diagonal-exponential-retract =
    ( inclusion-retract R ,
      precomp (map-retraction-retract Q) B ∘ postcomp S (inclusion-retract R) ,
      refl-htpy)

  hom-retraction-diagonal-exponential-retract :
    hom-arrow (diagonal-exponential B T) (diagonal-exponential A S)
  hom-retraction-diagonal-exponential-retract =
    ( map-retraction-retract R ,
      postcomp S (map-retraction-retract R) ∘ precomp (inclusion-retract Q) B ,
      refl-htpy)

  coh-retract-arrow-diagonal-exponential-retract :
    coherence-retract-arrow
      ( diagonal-exponential A S)
      ( diagonal-exponential B T)
      ( inclusion-diagonal-exponential-retract)
      ( hom-retraction-diagonal-exponential-retract)
      ( is-retraction-map-retraction-retract R)
      ( horizontal-concat-htpy
        ( htpy-postcomp S (is-retraction-map-retraction-retract R))
        ( htpy-precomp (is-retraction-map-retraction-retract Q) A))
  coh-retract-arrow-diagonal-exponential-retract x =
    ( compute-eq-htpy-ap-diagonal-exponential S
      ( map-retraction-retract R (inclusion-retract R x))
      ( x)
      ( is-retraction-map-retraction-retract R x)) ∙
    ( ap
      ( λ p →
        ( ap (λ f a → map-retraction-retract R (inclusion-retract R (f a))) p) ∙
        ( eq-htpy (λ _ → is-retraction-map-retraction-retract R x)))
      ( inv
        ( ( ap
            ( eq-htpy)
            ( eq-htpy (ap-const x ·r is-retraction-map-retraction-retract Q))) ∙
          ( eq-htpy-refl-htpy (diagonal-exponential A S x))))) ∙
      ( inv right-unit)

  is-retraction-hom-retraction-diagonal-exponential-retract :
    is-retraction-hom-arrow
      ( diagonal-exponential A S)
      ( diagonal-exponential B T)
      ( inclusion-diagonal-exponential-retract)
      ( hom-retraction-diagonal-exponential-retract)
  is-retraction-hom-retraction-diagonal-exponential-retract =
    ( ( is-retraction-map-retraction-retract R) ,
      ( horizontal-concat-htpy
        ( htpy-postcomp S (is-retraction-map-retraction-retract R))
        ( htpy-precomp (is-retraction-map-retraction-retract Q) A)) ,
      ( coh-retract-arrow-diagonal-exponential-retract))

  retract-arrow-diagonal-exponential-retract :
    (diagonal-exponential A S) retract-of-arrow (diagonal-exponential B T)
  retract-arrow-diagonal-exponential-retract =
    ( inclusion-diagonal-exponential-retract ,
      hom-retraction-diagonal-exponential-retract ,
      is-retraction-hom-retraction-diagonal-exponential-retract)
```

## References

{{#bibliography}} {{#reference UF13}}

## External links

- [Retracts in arrow categories](https://ncatlab.org/nlab/show/retract#in_arrow_categories)
  at $n$Lab

A wikidata identifier was not available for this concept.
