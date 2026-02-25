# Lifting structures on commuting squares of maps

```agda
module orthogonal-factorization-systems.lifting-structures-on-squares where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-tetrahedra-of-homotopies
open import foundation.commuting-triangles-of-homotopies
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.higher-homotopies-morphisms-arrows
open import foundation.homotopies
open import foundation.homotopies-morphisms-arrows
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.lifts-maps
open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

A
{{#concept "lifting structure" Disambiguation="commuting square of maps" Agda=lifting-structure-square}}
of a commuting square

```text
       h
  A ------> X
  |         |
 f|         |g
  |         |
  ∨         ∨
  B ------> Y
       i
```

consists of a
{{#concept "diagonal lift" Disambiguation="commuting square of maps" Agda=is-diagonal-lift-square}}
`j : B → X` such that the complete diagram

```text
         h
   A --------> X
   |        ∧  |
 f |   j  /    | g
   |    /      |
   ∨  /        ∨
   B --------> Y
         i
```

commutes. We refer to a square equipped with a lifting structure as a
{{#concept "lifting square"}}. Observe that there is a canonical map

```text
  pullback-hom f g : (B → X) → hom-arrow f g.
```

Therefore we see that a lifting square consists of a
[morphism of arrows](foundation.morphisms-arrows.md) `α : hom-arrow f g` from
`f` to `g`, a map `j : B → X`, and a
[homotopy of morphisms of arrows](foundation.homotopies-morphisms-arrows.md)
`pullback-hom f g j ~ α`.

**Terminology.** In the literature, a lifting structure on a square is commonly
referred to as a _solution to the lifting problem_ `α`.

## Definitions

### The predicate of being a diagonal lift of a square

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g) (j : B → X)
  where

  is-diagonal-lift-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-diagonal-lift-square = htpy-hom-arrow f g α (pullback-hom f g j)

  is-extension-is-diagonal-lift-square :
    is-diagonal-lift-square →
    is-extension-of-map f (map-domain-hom-arrow f g α) j
  is-extension-is-diagonal-lift-square = pr1

  is-lift-is-diagonal-lift-square :
    is-diagonal-lift-square → is-lift-of-map g (map-codomain-hom-arrow f g α) j
  is-lift-is-diagonal-lift-square = pr1 ∘ pr2

  coherence-is-diagonal-lift-square :
    (l : is-diagonal-lift-square) →
    coherence-square-homotopies
      ( is-lift-is-diagonal-lift-square l ·r f)
      ( coh-hom-arrow f g α)
      ( coh-pullback-hom f g j)
      ( g ·l is-extension-is-diagonal-lift-square l)
  coherence-is-diagonal-lift-square = pr2 ∘ pr2
```

### Lifting structures on squares

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  lifting-structure-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  lifting-structure-square = Σ (B → X) (is-diagonal-lift-square f g α)

  diagonal-map-lifting-structure-square : lifting-structure-square → (B → X)
  diagonal-map-lifting-structure-square = pr1

  is-lifting-diagonal-map-lifting-structure-square :
    (l : lifting-structure-square) →
    is-diagonal-lift-square f g α (diagonal-map-lifting-structure-square l)
  is-lifting-diagonal-map-lifting-structure-square = pr2

  is-extension-diagonal-map-lifting-structure-square :
    (l : lifting-structure-square) →
    is-extension-of-map f
      ( map-domain-hom-arrow f g α)
      ( diagonal-map-lifting-structure-square l)
  is-extension-diagonal-map-lifting-structure-square = pr1 ∘ pr2

  extension-lifting-structure-square :
    lifting-structure-square → extension-map f (map-domain-hom-arrow f g α)
  pr1 (extension-lifting-structure-square L) =
    diagonal-map-lifting-structure-square L
  pr2 (extension-lifting-structure-square L) =
    is-extension-diagonal-map-lifting-structure-square L

  is-lift-diagonal-map-lifting-structure-square :
    (l : lifting-structure-square) →
    is-lift-of-map g
      ( map-codomain-hom-arrow f g α)
      ( diagonal-map-lifting-structure-square l)
  is-lift-diagonal-map-lifting-structure-square = pr1 ∘ (pr2 ∘ pr2)

  lift-lifting-structure-square :
    lifting-structure-square → lift-map g (map-codomain-hom-arrow f g α)
  pr1 (lift-lifting-structure-square L) =
    diagonal-map-lifting-structure-square L
  pr2 (lift-lifting-structure-square L) =
    is-lift-diagonal-map-lifting-structure-square L

  coherence-lifting-structure-square :
    (l : lifting-structure-square) →
    coherence-square-homotopies
      ( is-lift-diagonal-map-lifting-structure-square l ·r f)
      ( coh-hom-arrow f g α)
      ( coh-pullback-hom f g (diagonal-map-lifting-structure-square l))
      ( g ·l is-extension-diagonal-map-lifting-structure-square l)
  coherence-lifting-structure-square = pr2 ∘ (pr2 ∘ pr2)
```

### Homotopies of lifting squares

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  (k l : lifting-structure-square f g α)
  where

  coherence-htpy-lifting-structure-square :
    diagonal-map-lifting-structure-square f g α k ~
    diagonal-map-lifting-structure-square f g α l →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  coherence-htpy-lifting-structure-square H =
    htpy-htpy-hom-arrow f g α
      ( pullback-hom f g (diagonal-map-lifting-structure-square f g α l))
      ( concat-htpy-hom-arrow f g α
        ( pullback-hom f g (diagonal-map-lifting-structure-square f g α k))
        ( pullback-hom f g (diagonal-map-lifting-structure-square f g α l))
        ( is-lifting-diagonal-map-lifting-structure-square f g α k)
        ( htpy-hom-arrow-htpy f g H))
      ( is-lifting-diagonal-map-lifting-structure-square f g α l)

  htpy-lifting-structure-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-lifting-structure-square =
    Σ ( diagonal-map-lifting-structure-square f g α k ~
        diagonal-map-lifting-structure-square f g α l)
      ( coherence-htpy-lifting-structure-square)

  module _
    (H : htpy-lifting-structure-square)
    where

    htpy-diagonal-map-htpy-lifting-structure-square :
      diagonal-map-lifting-structure-square f g α k ~
      diagonal-map-lifting-structure-square f g α l
    htpy-diagonal-map-htpy-lifting-structure-square = pr1 H

    coh-htpy-lifting-structure-square :
      coherence-htpy-lifting-structure-square
        ( htpy-diagonal-map-htpy-lifting-structure-square)
    coh-htpy-lifting-structure-square = pr2 H
```

### The reflexivity homotopy of a lifting square

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  (k : lifting-structure-square f g α)
  where

  htpy-diagonal-map-refl-htpy-lifting-structure-square :
    diagonal-map-lifting-structure-square f g α k ~
    diagonal-map-lifting-structure-square f g α k
  htpy-diagonal-map-refl-htpy-lifting-structure-square = refl-htpy

  coh-refl-htpy-lifting-structure-square :
    coherence-htpy-lifting-structure-square f g α k k
      ( htpy-diagonal-map-refl-htpy-lifting-structure-square)
  coh-refl-htpy-lifting-structure-square =
    right-unit-law-concat-htpy-hom-arrow f g α
      ( pullback-hom f g (diagonal-map-lifting-structure-square f g α k))
      ( is-lifting-diagonal-map-lifting-structure-square f g α k)

  refl-htpy-lifting-structure-square : htpy-lifting-structure-square f g α k k
  pr1 refl-htpy-lifting-structure-square =
    htpy-diagonal-map-refl-htpy-lifting-structure-square
  pr2 refl-htpy-lifting-structure-square =
    coh-refl-htpy-lifting-structure-square
```

### Trivial lifting squares

The diagram

```text
   A          X
   |        ∧ |
 f |   j  /   |g
   |    /     |
   ∨  /       ∨
   B          Y
```

gives rise to a lifting square

```text
       j ∘ f
    A -------> X
    |        ∧ |
  f |   j  /   | g
    |    /     |
    ∨  /       ∨
    B -------> Y
       g ∘ j
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-diagonal-lift-square-pullback-hom :
    (j : B → X) → is-diagonal-lift-square f g (pullback-hom f g j) j
  is-diagonal-lift-square-pullback-hom j =
    refl-htpy-hom-arrow f g (pullback-hom f g j)
```

## Properties

### The types of lifting squares are equivalent to the fibers of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  inv-compute-fiber-pullback-hom :
    fiber (pullback-hom f g) h ≃ lifting-structure-square f g h
  inv-compute-fiber-pullback-hom =
    equiv-tot
      ( λ j →
        extensionality-hom-arrow f g _ _ ∘e
        equiv-inv (pullback-hom f g j) h)

  compute-fiber-pullback-hom :
    lifting-structure-square f g h ≃ fiber (pullback-hom f g) h
  compute-fiber-pullback-hom = inv-equiv inv-compute-fiber-pullback-hom
```

### Characterization of identifications of lifting squares

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  (l : lifting-structure-square f g α)
  where

  htpy-eq-lifting-structure-square :
    (k : lifting-structure-square f g α) →
    l ＝ k → htpy-lifting-structure-square f g α l k
  htpy-eq-lifting-structure-square .l refl =
    refl-htpy-lifting-structure-square f g α l

  is-torsorial-htpy-lifting-structure-square :
    is-torsorial (htpy-lifting-structure-square f g α l)
  is-torsorial-htpy-lifting-structure-square =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy _)
      ( diagonal-map-lifting-structure-square f g α l , refl-htpy)
      ( is-torsorial-htpy-htpy-hom-arrow f g α
        ( pullback-hom f g (diagonal-map-lifting-structure-square f g α l))
        ( _))

  is-equiv-htpy-eq-lifting-structure-square :
    (k : lifting-structure-square f g α) →
    is-equiv (htpy-eq-lifting-structure-square k)
  is-equiv-htpy-eq-lifting-structure-square =
    fundamental-theorem-id
      ( is-torsorial-htpy-lifting-structure-square)
      ( htpy-eq-lifting-structure-square)

  extensionality-lifting-structure-square :
    (k : lifting-structure-square f g α) →
    (l ＝ k) ≃ htpy-lifting-structure-square f g α l k
  pr1 (extensionality-lifting-structure-square k) =
    htpy-eq-lifting-structure-square k
  pr2 (extensionality-lifting-structure-square k) =
    is-equiv-htpy-eq-lifting-structure-square k

  eq-htpy-lifting-structure-square :
    (k : lifting-structure-square f g α) →
    htpy-lifting-structure-square f g α l k → l ＝ k
  eq-htpy-lifting-structure-square k =
    map-inv-equiv (extensionality-lifting-structure-square k)
```

## External links

- [lift](https://ncatlab.org/nlab/show/lift) at $n$Lab.
