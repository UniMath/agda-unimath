# Standard pullbacks

```agda
module foundation.standard-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.diagonal-maps-cartesian-products-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.universal-property-pullbacks
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

Given a [cospan of types](foundation.cospans.md)

```text
  f : A → X ← B : g,
```

we can form the
{{#concept "standard pullback" Disambiguation="types" Agda=standard-pullback}}
`A ×_X B` satisfying
[the universal property of the pullback](foundation-core.universal-property-pullbacks.md)
of the cospan, completing the diagram

```text
  A ×_X B ------> B
     | ⌟          |
     |            | g
     |            |
     v            v
     A ---------> X.
           f
```

The standard pullback consists of [pairs](foundation.dependent-pair-types.md)
`a : A` and `b : B` such that `f a` and `g b` agree:

```text
  A ×_X B := Σ (a : A) (b : B), (f a ＝ g b),
```

thus the standard [cone](foundation.cones-over-cospan-diagrams.md) consists of
the canonical projections.

## Definitions

### The standard pullback of a cospan

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  standard-pullback : UU (l1 ⊔ l2 ⊔ l3)
  standard-pullback = Σ A (λ x → Σ B (λ y → f x ＝ g y))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {f : A → X} {g : B → X}
  where

  vertical-map-standard-pullback : standard-pullback f g → A
  vertical-map-standard-pullback = pr1

  horizontal-map-standard-pullback : standard-pullback f g → B
  horizontal-map-standard-pullback t = pr1 (pr2 t)

  coherence-square-standard-pullback :
    coherence-square-maps
      ( horizontal-map-standard-pullback)
      ( vertical-map-standard-pullback)
      ( g)
      ( f)
  coherence-square-standard-pullback t = pr2 (pr2 t)
```

### The cone at the standard pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  cone-standard-pullback : cone f g (standard-pullback f g)
  pr1 cone-standard-pullback = vertical-map-standard-pullback
  pr1 (pr2 cone-standard-pullback) = horizontal-map-standard-pullback
  pr2 (pr2 cone-standard-pullback) = coherence-square-standard-pullback
```

### The gap map into the standard pullback

The {{#concept "standard gap map" Disambiguation="cone over a cospan" Agda=gap}}
of a [commuting square](foundation-core.commuting-squares-of-maps.md) is the map
from the domain of the cone into the standard pullback.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  gap : cone f g C → C → standard-pullback f g
  pr1 (gap c z) = vertical-map-cone f g c z
  pr1 (pr2 (gap c z)) = horizontal-map-cone f g c z
  pr2 (pr2 (gap c z)) = coherence-square-cone f g c z
```

#### The standard ternary pullback

Given two cospans with a shared vertex `B`:

```text
      f       g       h       i
  A ----> X <---- B ----> Y <---- C,
```

we call the standard limit of the diagram the
{{#concept "standard ternary pullback" Disambiguation="of types" Agda=standard-ternary-pullback}}.
It is defined as the sum

```text
  standard-ternary-pullback f g h i :=
    Σ (a : A) (b : B) (c : C), ((f a ＝ g b) × (h b ＝ i c)).
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4} {C : UU l5}
  (f : A → X) (g : B → X) (h : B → Y) (i : C → Y)
  where

  standard-ternary-pullback : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  standard-ternary-pullback =
    Σ A (λ a → Σ B (λ b → Σ C (λ c → (f a ＝ g b) × (h b ＝ i c))))
```

## Properties

### Characterization of the identity type of the standard pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  Eq-standard-pullback : (t t' : standard-pullback f g) → UU (l1 ⊔ l2 ⊔ l3)
  Eq-standard-pullback (a , b , p) (a' , b' , p') =
    Σ (a ＝ a') (λ α → Σ (b ＝ b') (λ β → ap f α ∙ p' ＝ p ∙ ap g β))

  refl-Eq-standard-pullback :
    (t : standard-pullback f g) → Eq-standard-pullback t t
  pr1 (refl-Eq-standard-pullback (a , b , p)) = refl
  pr1 (pr2 (refl-Eq-standard-pullback (a , b , p))) = refl
  pr2 (pr2 (refl-Eq-standard-pullback (a , b , p))) = inv right-unit

  Eq-eq-standard-pullback :
    (s t : standard-pullback f g) → s ＝ t → Eq-standard-pullback s t
  Eq-eq-standard-pullback s .s refl = refl-Eq-standard-pullback s

  extensionality-standard-pullback :
    (t t' : standard-pullback f g) → (t ＝ t') ≃ Eq-standard-pullback t t'
  extensionality-standard-pullback (a , b , p) =
    extensionality-Σ
      ( λ bp' α → Σ (b ＝ pr1 bp') (λ β → ap f α ∙ pr2 bp' ＝ p ∙ ap g β))
      ( refl)
      ( refl , inv right-unit)
      ( λ x → id-equiv)
      ( extensionality-Σ
        ( λ p' β → p' ＝ p ∙ ap g β)
        ( refl)
        ( inv right-unit)
        ( λ y → id-equiv)
        ( λ p' → equiv-concat' p' (inv right-unit) ∘e equiv-inv p p'))

  map-extensionality-standard-pullback :
    { s t : standard-pullback f g}
    ( α : vertical-map-standard-pullback s ＝ vertical-map-standard-pullback t)
    ( β :
      horizontal-map-standard-pullback s ＝
      horizontal-map-standard-pullback t) →
    ( ( ap f α ∙ coherence-square-standard-pullback t) ＝
      ( coherence-square-standard-pullback s ∙ ap g β)) →
    s ＝ t
  map-extensionality-standard-pullback {s} {t} α β γ =
    map-inv-equiv (extensionality-standard-pullback s t) (α , β , γ)
```

### The standard pullback satisfies the universal property of pullbacks

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  abstract
    universal-property-standard-pullback :
      universal-property-pullback f g (cone-standard-pullback f g)
    universal-property-standard-pullback C =
      is-equiv-comp
        ( tot (λ _ → map-distributive-Π-Σ))
        ( mapping-into-Σ)
        ( is-equiv-mapping-into-Σ)
        ( is-equiv-tot-is-fiberwise-equiv (λ _ → is-equiv-map-distributive-Π-Σ))
```

### A cone is equal to the value of `cone-map` at its own gap map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  htpy-cone-up-pullback-standard-pullback :
    (c : cone f g C) →
    htpy-cone f g (cone-map f g (cone-standard-pullback f g) (gap f g c)) c
  pr1 (htpy-cone-up-pullback-standard-pullback c) = refl-htpy
  pr1 (pr2 (htpy-cone-up-pullback-standard-pullback c)) = refl-htpy
  pr2 (pr2 (htpy-cone-up-pullback-standard-pullback c)) = right-unit-htpy
```

### Standard pullbacks are symmetric

The standard pullback of `f : A -> X <- B : g` is equivalent to the standard
pullback of `g : B -> X <- A : f`.

```agda
map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → standard-pullback f g → standard-pullback g f
pr1 (map-commutative-standard-pullback f g x) =
  horizontal-map-standard-pullback x
pr1 (pr2 (map-commutative-standard-pullback f g x)) =
  vertical-map-standard-pullback x
pr2 (pr2 (map-commutative-standard-pullback f g x)) =
  inv (coherence-square-standard-pullback x)

inv-inv-map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  ( map-commutative-standard-pullback f g ∘
    map-commutative-standard-pullback g f) ~ id
inv-inv-map-commutative-standard-pullback f g x =
  eq-pair-eq-fiber
    ( eq-pair-eq-fiber
      ( inv-inv (coherence-square-standard-pullback x)))

abstract
  is-equiv-map-commutative-standard-pullback :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-commutative-standard-pullback f g)
  is-equiv-map-commutative-standard-pullback f g =
    is-equiv-is-invertible
      ( map-commutative-standard-pullback g f)
      ( inv-inv-map-commutative-standard-pullback f g)
      ( inv-inv-map-commutative-standard-pullback g f)

commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  standard-pullback f g ≃ standard-pullback g f
pr1 (commutative-standard-pullback f g) =
  map-commutative-standard-pullback f g
pr2 (commutative-standard-pullback f g) =
  is-equiv-map-commutative-standard-pullback f g
```

#### The gap map of the swapped cone computes as the underlying gap map followed by a swap

```agda
triangle-map-commutative-standard-pullback :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  gap g f (swap-cone f g c) ~
  map-commutative-standard-pullback f g ∘ gap f g c
triangle-map-commutative-standard-pullback f g c = refl-htpy
```

### Standard pullbacks are associative

Consider two cospans with a shared vertex `B`:

```text
      f       g       h       i
  A ----> X <---- B ----> Y <---- C,
```

then we can construct their limit using standard pullbacks in two equivalent
ways. We can construct it by first forming the standard pullback of `f` and `g`,
and then forming the standard pullback of the resulting `h ∘ f'` and `i`

```text
  (A ×_X B) ×_Y C ---------------------> C
         | ⌟                             |
         |                               | i
         ∨                               ∨
      A ×_X B ---------> B ------------> Y
         | ⌟     f'      |       h
         |               | g
         ∨               ∨
         A ------------> X,
                 f
```

or we can first form the pullback of `h` and `i`, and then form the pullback of
`f` and the resulting `g ∘ i'`:

```text
  A ×_X (B ×_Y C) --> B ×_Y C ---------> C
         | ⌟             | ⌟             |
         |               | i'            | i
         |               ∨               ∨
         |               B ------------> Y
         |               |       h
         |               | g
         ∨               ∨
         A ------------> X.
                 f
```

We show that both of these constructions are equivalent by showing they are
equivalent to the standard ternary pullback.

**Note:** Associativity with respect to ternary cospans

```text
              B
              |
              | g
              ∨
    A ------> X <------ C
         f         h
```

is a special case of what we consider here that is recovered by using

```text
      f       g       g       h
  A ----> X <---- B ----> X <---- C.
```

- See also the following relevant stack exchange question:
  [Associativity of pullbacks](https://math.stackexchange.com/questions/2046276/associativity-of-pullbacks).

#### Computing the left associated iterated standard pullback

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4} {C : UU l5}
  (f : A → X) (g : B → X) (h : B → Y) (i : C → Y)
  where

  map-left-associative-standard-pullback :
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i →
    standard-ternary-pullback f g h i
  map-left-associative-standard-pullback ((a , b , p) , c , q) =
    ( a , b , c , p , q)

  map-inv-left-associative-standard-pullback :
    standard-ternary-pullback f g h i →
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i
  map-inv-left-associative-standard-pullback (a , b , c , p , q) =
    ( ( a , b , p) , c , q)

  is-equiv-map-left-associative-standard-pullback :
    is-equiv map-left-associative-standard-pullback
  is-equiv-map-left-associative-standard-pullback =
    is-equiv-is-invertible
      ( map-inv-left-associative-standard-pullback)
      ( refl-htpy)
      ( refl-htpy)

  compute-left-associative-standard-pullback :
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i ≃
    standard-ternary-pullback f g h i
  compute-left-associative-standard-pullback =
    ( map-left-associative-standard-pullback ,
      is-equiv-map-left-associative-standard-pullback)
```

#### Computing the right associated iterated dependent pullback

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4} {C : UU l5}
  (f : A → X) (g : B → X) (h : B → Y) (i : C → Y)
  where

  map-right-associative-standard-pullback :
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i}) →
    standard-ternary-pullback f g h i
  map-right-associative-standard-pullback (a , (b , c , p) , q) =
    ( a , b , c , q , p)

  map-inv-right-associative-standard-pullback :
    standard-ternary-pullback f g h i →
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i})
  map-inv-right-associative-standard-pullback (a , b , c , p , q) =
    ( a , (b , c , q) , p)

  is-equiv-map-right-associative-standard-pullback :
    is-equiv map-right-associative-standard-pullback
  is-equiv-map-right-associative-standard-pullback =
    is-equiv-is-invertible
      ( map-inv-right-associative-standard-pullback)
      ( refl-htpy)
      ( refl-htpy)

  compute-right-associative-standard-pullback :
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i}) ≃
    standard-ternary-pullback f g h i
  compute-right-associative-standard-pullback =
    ( map-right-associative-standard-pullback ,
      is-equiv-map-right-associative-standard-pullback)
```

#### Standard pullbacks are associative

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4} {C : UU l5}
  (f : A → X) (g : B → X) (h : B → Y) (i : C → Y)
  where

  associative-standard-pullback :
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i ≃
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i})
  associative-standard-pullback =
    ( inv-equiv (compute-right-associative-standard-pullback f g h i)) ∘e
    ( compute-left-associative-standard-pullback f g h i)

  map-associative-standard-pullback :
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i →
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i})
  map-associative-standard-pullback = map-equiv associative-standard-pullback

  map-inv-associative-standard-pullback :
    standard-pullback f (g ∘ vertical-map-standard-pullback {f = h} {g = i}) →
    standard-pullback (h ∘ horizontal-map-standard-pullback {f = f} {g = g}) i
  map-inv-associative-standard-pullback =
    map-inv-equiv associative-standard-pullback
```

### Pullbacks can be "folded"

Given a standard pullback square

```text
         f'
    C -------> B
    | ⌟        |
  g'|          | g
    v          v
    A -------> X
         f
```

we can "fold" the vertical edge onto the horizontal one and get a new pullback
square

```text
            C ---------> X
            | ⌟          |
  (f' , g') |            |
            v            v
          A × B -----> X × X,
                f × g
```

moreover, this folded square is a pullback if and only if the original one is.

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  fold-cone :
    {l4 : Level} {C : UU l4} →
    cone f g C → cone (map-product f g) (diagonal-product X) C
  pr1 (pr1 (fold-cone c) z) = vertical-map-cone f g c z
  pr2 (pr1 (fold-cone c) z) = horizontal-map-cone f g c z
  pr1 (pr2 (fold-cone c)) = g ∘ horizontal-map-cone f g c
  pr2 (pr2 (fold-cone c)) z = eq-pair (coherence-square-cone f g c z) refl

  map-fold-cone-standard-pullback :
    standard-pullback f g →
    standard-pullback (map-product f g) (diagonal-product X)
  pr1 (pr1 (map-fold-cone-standard-pullback x)) =
    vertical-map-standard-pullback x
  pr2 (pr1 (map-fold-cone-standard-pullback x)) =
    horizontal-map-standard-pullback x
  pr1 (pr2 (map-fold-cone-standard-pullback x)) =
    g (horizontal-map-standard-pullback x)
  pr2 (pr2 (map-fold-cone-standard-pullback x)) =
    eq-pair (coherence-square-standard-pullback x) refl

  map-inv-fold-cone-standard-pullback :
    standard-pullback (map-product f g) (diagonal-product X) →
    standard-pullback f g
  pr1 (map-inv-fold-cone-standard-pullback ((a , b) , x , α)) = a
  pr1 (pr2 (map-inv-fold-cone-standard-pullback ((a , b) , x , α))) = b
  pr2 (pr2 (map-inv-fold-cone-standard-pullback ((a , b) , x , α))) =
    ap pr1 α ∙ inv (ap pr2 α)

  abstract
    is-section-map-inv-fold-cone-standard-pullback :
      is-section
        ( map-fold-cone-standard-pullback)
        ( map-inv-fold-cone-standard-pullback)
    is-section-map-inv-fold-cone-standard-pullback ((a , b) , (x , α)) =
      map-extensionality-standard-pullback
        ( map-product f g)
        ( diagonal-product X)
        ( refl)
        ( ap pr2 α)
        ( ( inv (is-section-pair-eq α)) ∙
          ( ap
            ( λ t → eq-pair t (ap pr2 α))
            ( ( inv right-unit) ∙
              ( inv
                ( left-whisker-concat
                  ( ap pr1 α)
                  ( left-inv (ap pr2 α)))) ∙
              ( inv (assoc (ap pr1 α) (inv (ap pr2 α)) (ap pr2 α))))) ∙
          ( eq-pair-concat
            ( ap pr1 α ∙ inv (ap pr2 α))
            ( ap pr2 α)
            ( refl)
            ( ap pr2 α)) ∙
          ( ap
            ( concat (eq-pair (ap pr1 α ∙ inv (ap pr2 α)) refl) (x , x))
            ( inv (compute-ap-diagonal-product (ap pr2 α)))))

  abstract
    is-retraction-map-inv-fold-cone-standard-pullback :
      is-retraction
        ( map-fold-cone-standard-pullback)
        ( map-inv-fold-cone-standard-pullback)
    is-retraction-map-inv-fold-cone-standard-pullback (a , b , p) =
      map-extensionality-standard-pullback f g
        ( refl)
        ( refl)
        ( inv
          ( ( right-whisker-concat
              ( ( right-whisker-concat
                  ( ap-pr1-eq-pair p refl)
                  ( inv (ap pr2 (eq-pair p refl)))) ∙
                ( ap (λ t → p ∙ inv t) (ap-pr2-eq-pair p refl)) ∙
                ( right-unit))
              ( refl)) ∙
            ( right-unit)))

  abstract
    is-equiv-map-fold-cone-standard-pullback :
      is-equiv map-fold-cone-standard-pullback
    is-equiv-map-fold-cone-standard-pullback =
      is-equiv-is-invertible
        ( map-inv-fold-cone-standard-pullback)
        ( is-section-map-inv-fold-cone-standard-pullback)
        ( is-retraction-map-inv-fold-cone-standard-pullback)

  compute-fold-standard-pullback :
    standard-pullback f g ≃
    standard-pullback (map-product f g) (diagonal-product X)
  compute-fold-standard-pullback =
    map-fold-cone-standard-pullback , is-equiv-map-fold-cone-standard-pullback

  triangle-map-fold-cone-standard-pullback :
    {l4 : Level} {C : UU l4} (c : cone f g C) →
    gap (map-product f g) (diagonal-product X) (fold-cone c) ~
    map-fold-cone-standard-pullback ∘ gap f g c
  triangle-map-fold-cone-standard-pullback c = refl-htpy
```

### The equivalence on standard pullbacks induced by parallel cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  map-equiv-standard-pullback-htpy :
    standard-pullback f' g' → standard-pullback f g
  map-equiv-standard-pullback-htpy =
    tot (λ a → tot (λ b → concat' (f a) (inv (Hg b)) ∘ concat (Hf a) (g' b)))

  abstract
    is-equiv-map-equiv-standard-pullback-htpy :
      is-equiv map-equiv-standard-pullback-htpy
    is-equiv-map-equiv-standard-pullback-htpy =
      is-equiv-tot-is-fiberwise-equiv
        ( λ a →
          is-equiv-tot-is-fiberwise-equiv
            ( λ b →
              is-equiv-comp
                ( concat' (f a) (inv (Hg b)))
                ( concat (Hf a) (g' b))
                ( is-equiv-concat (Hf a) (g' b))
                ( is-equiv-concat' (f a) (inv (Hg b)))))

  equiv-standard-pullback-htpy :
    standard-pullback f' g' ≃ standard-pullback f g
  pr1 equiv-standard-pullback-htpy = map-equiv-standard-pullback-htpy
  pr2 equiv-standard-pullback-htpy = is-equiv-map-equiv-standard-pullback-htpy
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
