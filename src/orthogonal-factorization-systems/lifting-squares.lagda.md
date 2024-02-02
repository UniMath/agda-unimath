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
open import foundation.fibered-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import orthogonal-factorization-systems.extensions-of-maps
open import orthogonal-factorization-systems.lifts-of-maps
open import orthogonal-factorization-systems.morphisms-arrows-from-diagonal-maps
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
  hom-arrow-map : (B → X) → hom-arrow f g.
```

Therefore we see that a lifting square consists of a morphism `α : hom-arrow f g` of arrows from `f` to `g`, a map `j : B → X`, and a homotopy of morphisms of arrow `hom-arrow-map f ~ α`.  

## Definitions

### The predicate of being a lifting square

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g) (j : B → X)
  where

  is-lifting-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-lifting-square = htpy-hom-arrow f g α (hom-arrow-map f g j)

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
      ( coh-hom-arrow-map f g j)
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

  map-diagonal-lifting-square : lifting-square → (B → X)
  map-diagonal-lifting-square = pr1

  is-extension-lifting-square :
    (l : lifting-square) →
    is-extension f (map-domain-hom-arrow f g α) (map-diagonal-lifting-square l)
  is-extension-lifting-square = pr1 ∘ pr2

  extension-lifting-square :
    lifting-square → extension f (map-domain-hom-arrow f g α)
  pr1 (extension-lifting-square L) = map-diagonal-lifting-square L
  pr2 (extension-lifting-square L) = is-extension-lifting-square L

  is-lift-lifting-square :
    (l : lifting-square) →
    is-lift g (map-codomain-hom-arrow f g α) (map-diagonal-lifting-square l)
  is-lift-lifting-square = pr1 ∘ (pr2 ∘ pr2)

  lift-lifting-square : lifting-square → lift g (map-codomain-hom-arrow f g α)
  pr1 (lift-lifting-square L) = map-diagonal-lifting-square L
  pr2 (lift-lifting-square L) = is-lift-lifting-square L

  coherence-lifting-square :
    (l : lifting-square) →
    coherence-square-homotopies
      ( is-lift-lifting-square l ·r f)
      ( coh-hom-arrow f g α)
      ( coh-hom-arrow-map f g (map-diagonal-lifting-square l))
      ( g ·l is-extension-lifting-square l)
  coherence-lifting-square = pr2 ∘ (pr2 ∘ pr2)
```

## Properties

### Characterization of identifications of lifting squares

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  coherence-htpy-lifting-square :
    {j k : B → X} → j ~ k → UU {!!}
  coherence-htpy-lifting-square = {!!}

```

```text
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (h : A → X) (f : A → B) (g : X → Y) (i : B → Y)
  (H : coherence-square-maps h f g i)
  where

  coherence-htpy-lifting-square :
    (l l' : lifting-square h f g i H)
    (K :
      ( map-diagonal-lifting-square l) ~
      ( map-diagonal-lifting-square l'))
    (E :
      ( is-extension-lifting-square l') ~
      ( is-extension-lifting-square l ∙h (K ·r f)))
    (L :
      ( is-lift-lifting-square l') ~
      ( is-lift-lifting-square l ∙h (g ·l K))) →
    UU (l1 ⊔ l4)
  coherence-htpy-lifting-square l l' K E L =
    coherence-tetrahedron-homotopies
      ( is-lift-lifting-square l ·r f)
      ( H)
      ( g ·l (K ·r f))
      ( g ·l is-extension-lifting-square l')
      ( g ·l is-extension-lifting-square l)
      ( is-lift-lifting-square l' ·r f)
      ( coherence-lifting-square l)
      ( right-whisker-comp-coherence-triangle-homotopies (K ·r f) g E)
      ( left-whisker-comp-coherence-triangle-homotopies (g ·l K) L f)
      ( coherence-lifting-square l')

  htpy-lifting-square :
    (l l' : lifting-square h f g i H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-lifting-square l l' =
    Σ ( ( map-diagonal-lifting-square l) ~
        ( map-diagonal-lifting-square l'))
      ( λ K →
        Σ ( ( is-extension-lifting-square l') ~
            ( is-extension-lifting-square l ∙h (K ·r f)))
          ( λ E →
            Σ ( ( is-lift-lifting-square l') ~
                ( is-lift-lifting-square l ∙h (g ·l K)))
              ( coherence-htpy-lifting-square l l' K E)))

  refl-htpy-lifting-square :
    (l : lifting-square h f g i H) → htpy-lifting-square l l
  pr1 (refl-htpy-lifting-square l) = refl-htpy
  pr1 (pr2 (refl-htpy-lifting-square l)) = inv-htpy-right-unit-htpy
  pr1 (pr2 (pr2 (refl-htpy-lifting-square l))) = inv-htpy-right-unit-htpy
  pr2 (pr2 (pr2 (refl-htpy-lifting-square l))) x = {!!}
  {-
    ( inv (assoc (inv right-unit) (β) (α))) ∙
    ( ( right-whisker-concat
        ( ( left-whisker-concat
            ( inv right-unit)
            ( ( right-transpose-eq-concat _ _ _
                ( inv
                  ( compute-refl-right-whisker-concat
                    ( coherence-lifting-square l x)))) ∙
              ( assoc
                ( right-unit)
                ( coherence-lifting-square l x)
                ( inv right-unit)))) ∙
          ( is-retraction-inv-concat
            ( right-unit)
            ( coherence-lifting-square l x ∙ inv right-unit)))
        ( α)) ∙
      ( ( assoc (coherence-lifting-square l x) (inv right-unit) (α)) ∙
        ( ( left-whisker-concat
            ( coherence-lifting-square l x)
            ( ( left-whisker-concat
                ( inv right-unit)
                ( right-unit-law-assoc
                  ( H x)
                  ( ap g (is-extension-lifting-square l x)))) ∙
              ( ( is-retraction-inv-concat
                  ( right-unit)
                  ( left-whisker-concat (H x) (inv right-unit))) ∙
                ( inv
                  ( is-section-inv-concat' α
                    ( left-whisker-concat (H x) (inv right-unit))))))) ∙
          ( ( inv
              ( assoc
                ( coherence-lifting-square l x)
                ( left-whisker-concat (H x) (inv right-unit) ∙ inv α)
                ( α))) ∙
            ( ap
              ( λ r →
                ( ( coherence-lifting-square l x) ∙
                  ( left-whisker-concat (H x) r ∙ inv α)) ∙
                ( α))
              ( compute-refl-right-map-coherence-triangle-identifications
                ( g)
                ( is-extension-lifting-square l x))))))) -}
    where
      α = assoc (H x) (ap g (is-extension-lifting-square l x)) refl
      β = right-whisker-concat (coherence-lifting-square l x) refl

  htpy-eq-lifting-square :
    (l l' : lifting-square h f g i H) → l ＝ l' → htpy-lifting-square l l'
  htpy-eq-lifting-square l .l refl = refl-htpy-lifting-square l
```

It remains to show that `coherence-htpy-lifting-square` indeed is a
characterization of identifications of lifting squares.

### Diagonal maps give lifting squares

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
  |       ^ |
 f|   j  /  |g
  |    /    |
  V  /      V
  B ------> Y
     g ∘ j
```

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-lifting-square-diagonal :
    (j : B → X) → is-lifting-square (j ∘ f) f g (g ∘ j) refl-htpy j
  pr1 (is-lifting-square-diagonal j) = refl-htpy
  pr1 (pr2 (is-lifting-square-diagonal j)) = refl-htpy
  pr2 (pr2 (is-lifting-square-diagonal j)) = refl-htpy
```

### The lifting square associated to a fibered map

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  lifting-square-fibered-map :
    (h : fibered-map f g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  lifting-square-fibered-map h =
    lifting-square
      ( map-total-fibered-map f g h)
      ( f)
      ( g)
      ( map-base-fibered-map f g h)
      ( is-map-over-map-total-fibered-map f g h)
```

