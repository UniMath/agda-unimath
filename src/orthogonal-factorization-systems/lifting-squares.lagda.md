# Lifting squares

```agda
module orthogonal-factorization-systems.lifting-squares where
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

open import orthogonal-factorization-systems.extensions-of-maps
open import orthogonal-factorization-systems.lifts-of-maps
open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

A **lifting square** of a commuting square

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

consists of a diagonal map `j : B → B` such that the complete diagram

```text
       h
  A --------> X
  |        ∧  |
 f|   j  /    |g
  |    /      |
  ∨  /        ∨
  B --------> Y
       i
```

commutes. We note that there is a canonical map

```text
  pullback-hom : (B → X) → hom-arrow f g.
```

Therefore we see that a lifting square consists of a morphism
`α : hom-arrow f g` of arrows from `f` to `g`, a map `j : B → X`, and a homotopy
of morphisms of arrow `pullback-hom f ~ α`.

## Definitions

### The predicate of being a lifting square

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g) (j : B → X)
  where

  is-lifting-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-lifting-square = htpy-hom-arrow f g α (pullback-hom f g j)

  is-extension-is-lifting-square :
    is-lifting-square →
    is-extension f (map-domain-hom-arrow f g α) j
  is-extension-is-lifting-square = pr1

  is-lift-is-lifting-square :
    is-lifting-square → is-lift g (map-codomain-hom-arrow f g α) j
  is-lift-is-lifting-square = pr1 ∘ pr2

  coherence-is-lifting-square :
    (l : is-lifting-square) →
    coherence-square-homotopies
      ( is-lift-is-lifting-square l ·r f)
      ( coh-hom-arrow f g α)
      ( coh-pullback-hom f g j)
      ( g ·l is-extension-is-lifting-square l)
  coherence-is-lifting-square = pr2 ∘ pr2
```

### Lifting squares

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  lifting-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  lifting-square = Σ (B → X) (is-lifting-square f g α)

  diagonal-map-lifting-square : lifting-square → (B → X)
  diagonal-map-lifting-square = pr1

  is-lifting-diagonal-map-lifting-square :
    (l : lifting-square) →
    is-lifting-square f g α (diagonal-map-lifting-square l)
  is-lifting-diagonal-map-lifting-square = pr2

  is-extension-lifting-square :
    (l : lifting-square) →
    is-extension f (map-domain-hom-arrow f g α) (diagonal-map-lifting-square l)
  is-extension-lifting-square = pr1 ∘ pr2

  extension-lifting-square :
    lifting-square → extension f (map-domain-hom-arrow f g α)
  pr1 (extension-lifting-square L) = diagonal-map-lifting-square L
  pr2 (extension-lifting-square L) = is-extension-lifting-square L

  is-lift-lifting-square :
    (l : lifting-square) →
    is-lift g (map-codomain-hom-arrow f g α) (diagonal-map-lifting-square l)
  is-lift-lifting-square = pr1 ∘ (pr2 ∘ pr2)

  lift-lifting-square : lifting-square → lift g (map-codomain-hom-arrow f g α)
  pr1 (lift-lifting-square L) = diagonal-map-lifting-square L
  pr2 (lift-lifting-square L) = is-lift-lifting-square L

  coherence-lifting-square :
    (l : lifting-square) →
    coherence-square-homotopies
      ( is-lift-lifting-square l ·r f)
      ( coh-hom-arrow f g α)
      ( coh-pullback-hom f g (diagonal-map-lifting-square l))
      ( g ·l is-extension-lifting-square l)
  coherence-lifting-square = pr2 ∘ (pr2 ∘ pr2)
```

### Homotopies of lifting squares

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  (k l : lifting-square f g α)
  where

  coherence-htpy-lifting-square :
    diagonal-map-lifting-square f g α k ~ diagonal-map-lifting-square f g α l →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  coherence-htpy-lifting-square H =
    htpy-htpy-hom-arrow f g α
      ( pullback-hom f g (diagonal-map-lifting-square f g α l))
      ( concat-htpy-hom-arrow f g α
        ( pullback-hom f g (diagonal-map-lifting-square f g α k))
        ( pullback-hom f g (diagonal-map-lifting-square f g α l))
        ( is-lifting-diagonal-map-lifting-square f g α k)
        ( htpy-hom-arrow-htpy f g H))
      ( is-lifting-diagonal-map-lifting-square f g α l)

  htpy-lifting-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-lifting-square =
    Σ ( diagonal-map-lifting-square f g α k ~
        diagonal-map-lifting-square f g α l)
      ( coherence-htpy-lifting-square)

  module _
    (H : htpy-lifting-square)
    where

    htpy-diagonal-map-htpy-lifting-square :
      diagonal-map-lifting-square f g α k ~ diagonal-map-lifting-square f g α l
    htpy-diagonal-map-htpy-lifting-square = pr1 H

    coh-htpy-lifting-square :
      coherence-htpy-lifting-square htpy-diagonal-map-htpy-lifting-square
    coh-htpy-lifting-square = pr2 H
```

### The reflexivity homotopy of a lifting square

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  (k : lifting-square f g α)
  where

  htpy-diagonal-map-refl-htpy-lifting-square :
    diagonal-map-lifting-square f g α k ~ diagonal-map-lifting-square f g α k
  htpy-diagonal-map-refl-htpy-lifting-square = refl-htpy

  coh-refl-htpy-lifting-square :
    coherence-htpy-lifting-square f g α k k
      ( htpy-diagonal-map-refl-htpy-lifting-square)
  coh-refl-htpy-lifting-square =
    right-unit-law-concat-htpy-hom-arrow f g α
      ( pullback-hom f g (diagonal-map-lifting-square f g α k))
      ( is-lifting-diagonal-map-lifting-square f g α k)

  refl-htpy-lifting-square : htpy-lifting-square f g α k k
  pr1 refl-htpy-lifting-square = htpy-diagonal-map-refl-htpy-lifting-square
  pr2 refl-htpy-lifting-square = coh-refl-htpy-lifting-square
```

### Trivial lifting squares

The diagram

```text
  A         X
  |       ^ |
 f|   j  /  |g
  |    /    |
  V  /      V
  B         Y
```

gives rise to a lifting square

```text
       j ∘ f
    A ------> X
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

  is-lifting-square-pullback-hom :
    (j : B → X) → is-lifting-square f g (pullback-hom f g j) j
  is-lifting-square-pullback-hom j = refl-htpy-hom-arrow f g (pullback-hom f g j)
```

## Properties

### The types of lifting squares are equivalent to the fibers of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  inv-compute-fiber-pullback-hom :
    fiber (pullback-hom f g) h ≃ lifting-square f g h
  inv-compute-fiber-pullback-hom =
    equiv-tot
      ( λ j →
        extensionality-hom-arrow f g _ _ ∘e
        equiv-inv (pullback-hom f g j) h)

  compute-fiber-pullback-hom :
    lifting-square f g h ≃ fiber (pullback-hom f g) h
  compute-fiber-pullback-hom = inv-equiv inv-compute-fiber-pullback-hom
```

### Characterization of identifications of lifting squares

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g) (l : lifting-square f g α)
  where

  htpy-eq-lifting-square :
    (k : lifting-square f g α) → l ＝ k → htpy-lifting-square f g α l k
  htpy-eq-lifting-square .l refl = refl-htpy-lifting-square f g α l

  is-torsorial-htpy-lifting-square :
    is-torsorial (htpy-lifting-square f g α l)
  is-torsorial-htpy-lifting-square =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy _)
      ( diagonal-map-lifting-square f g α l , refl-htpy)
      ( is-torsorial-htpy-htpy-hom-arrow f g α
        ( pullback-hom f g (diagonal-map-lifting-square f g α l))
        ( _))

  is-equiv-htpy-eq-lifting-square :
    (k : lifting-square f g α) → is-equiv (htpy-eq-lifting-square k)
  is-equiv-htpy-eq-lifting-square =
    fundamental-theorem-id
      ( is-torsorial-htpy-lifting-square)
      ( htpy-eq-lifting-square)

  extensionality-lifting-square :
    (k : lifting-square f g α) → (l ＝ k) ≃ htpy-lifting-square f g α l k
  pr1 (extensionality-lifting-square k) = htpy-eq-lifting-square k
  pr2 (extensionality-lifting-square k) = is-equiv-htpy-eq-lifting-square k

  eq-htpy-lifting-square :
    (k : lifting-square f g α) → htpy-lifting-square f g α l k → l ＝ k
  eq-htpy-lifting-square k = map-inv-equiv (extensionality-lifting-square k)
```
