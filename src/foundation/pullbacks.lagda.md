# Pullbacks

```agda
module foundation.pullbacks where

open import foundation-core.pullbacks public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.descent-equivalences
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.standard-pullbacks
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.postcomposition-functions
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

Given a [cospan of types](foundation.cospans.md)

```text
  f : A → X ← B : g,
```

we want to pose the question of whether a certain
[cone](foundation.cones-over-cospan-diagrams.md) over it is a
{{#concept "pullback cone" Disambiguation="types" Agda=is-pullback}}. This is
concept is captured by
[the universal property of the pullback](foundation-core.universal-property-pullbacks.md),
however, the universal property is a large proposition so it is not suitable for
all purposes.

As an alternative, given the existence of the
[standard pullback type](foundation-core.standard-pullbacks.md) `A ×_X B`, we
can characterize pullback cones as those for which the gap map from the standard
pullback is an [equivalence](foundation-core.equivalences.md). This predicate is
a small [proposition](foundation-core.propositions.md) that we dub
{{#concept "the small predicate of being a pullback" Agda=is-pullback}}.

## Properties

### Being a pullback is a property

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  is-prop-is-pullback : (c : cone f g C) → is-prop (is-pullback f g c)
  is-prop-is-pullback c = is-property-is-equiv (gap f g c)

  is-pullback-Prop : (c : cone f g C) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 (is-pullback-Prop c) = is-pullback f g c
  pr2 (is-pullback-Prop c) = is-prop-is-pullback c
```

### Pullbacks are closed under exponentiation

Given a pullback square

```text
          f'
    C ---------> B
    | ⌟          |
  g'|            | g
    |            |
    v            v
    A ---------> X
          f
```

then the exponentiated square given by postcomposition

```text
                f' ∘ -
      (S → C) ---------> (S → B)
         |                  |
  g' ∘ - |                  | g ∘ -
         |                  |
         v                  v
      (S → A) ---------> (S → X)
                f ∘ -
```

is a pullback square for any type `S`.

```agda
abstract
  is-pullback-postcomp-is-pullback :
    {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) → is-pullback f g c →
    (T : UU l5) →
    is-pullback (postcomp T f) (postcomp T g) (postcomp-cone T f g c)
  is-pullback-postcomp-is-pullback f g c is-pb-c T =
    is-equiv-top-map-triangle
      ( cone-map f g c)
      ( map-postcomp-cone-standard-pullback f g T)
      ( gap (f ∘_) (g ∘_) (postcomp-cone T f g c))
      ( triangle-map-postcomp-cone-standard-pullback T f g c)
      ( is-equiv-map-postcomp-cone-standard-pullback f g T)
      ( universal-property-pullback-is-pullback f g c is-pb-c T)

abstract
  is-pullback-is-pullback-postcomp :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    ( {l5 : Level} (T : UU l5) →
      is-pullback (postcomp T f) (postcomp T g) (postcomp-cone T f g c)) →
    is-pullback f g c
  is-pullback-is-pullback-postcomp f g c is-pb-postcomp =
    is-pullback-universal-property-pullback f g c
      ( λ T →
        is-equiv-left-map-triangle
          ( cone-map f g c)
          ( map-postcomp-cone-standard-pullback f g T)
          ( gap (f ∘_) (g ∘_) (postcomp-cone T f g c))
          ( triangle-map-postcomp-cone-standard-pullback T f g c)
          ( is-pb-postcomp T)
          ( is-equiv-map-postcomp-cone-standard-pullback f g T))
```

### Identity types can be presented as pullbacks

Identity types fit into pullback squares

```text
 (x ＝ y) ----> 1
    | ⌟         |
    |           | y
    v           v
    1 --------> A.
          x
```

```agda
module _
  {l : Level} {A : UU l} (x y : A)
  where

  cone-Id : cone (point x) (point y) (x ＝ y)
  pr1 cone-Id = terminal-map (x ＝ y)
  pr1 (pr2 cone-Id) = terminal-map (x ＝ y)
  pr2 (pr2 cone-Id) = id

  inv-gap-cone-Id : standard-pullback (point x) (point y) → x ＝ y
  inv-gap-cone-Id (star , star , p) = p

  abstract
    is-section-inv-gap-cone-Id :
      is-section (gap (point x) (point y) cone-Id) (inv-gap-cone-Id)
    is-section-inv-gap-cone-Id (star , star , p) = refl

  abstract
    is-retraction-inv-gap-cone-Id :
      is-retraction (gap (point x) (point y) cone-Id) (inv-gap-cone-Id)
    is-retraction-inv-gap-cone-Id p = refl

  abstract
    is-pullback-cone-Id : is-pullback (point x) (point y) cone-Id
    is-pullback-cone-Id =
      is-equiv-is-invertible
        ( inv-gap-cone-Id)
        ( is-section-inv-gap-cone-Id)
        ( is-retraction-inv-gap-cone-Id)

module _
  {l : Level} {A : UU l} ((x , y) : A × A)
  where

  cone-Id' : cone (point (x , y)) (diagonal A) (x ＝ y)
  pr1 cone-Id' = terminal-map (x ＝ y)
  pr1 (pr2 cone-Id') = const (x ＝ y) A x
  pr2 (pr2 cone-Id') p = eq-pair-eq-fiber (inv p)

  inv-gap-cone-Id' :
    standard-pullback (point (x , y)) (diagonal A) → x ＝ y
  inv-gap-cone-Id' (star , z , p) = ap pr1 p ∙ inv (ap pr2 p)

  abstract
    is-section-inv-gap-cone-Id' :
      gap (point (x , y)) (diagonal A) cone-Id' ∘
      inv-gap-cone-Id' ~ id
    is-section-inv-gap-cone-Id' (star , z , refl) = refl

  abstract
    is-retraction-inv-gap-cone-Id' :
      inv-gap-cone-Id' ∘
      gap (point (x , y)) (diagonal A) cone-Id' ~ id
    is-retraction-inv-gap-cone-Id' refl = refl

  abstract
    is-pullback-cone-Id' :
      is-pullback (point (x , y)) (diagonal A) cone-Id'
    is-pullback-cone-Id' =
      is-equiv-is-invertible
        ( inv-gap-cone-Id')
        ( is-section-inv-gap-cone-Id')
        ( is-retraction-inv-gap-cone-Id')
```

### Parallel pullback squares

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  triangle-is-pullback-htpy :
    {c : cone f g C} {c' : cone f' g' C} (Hc : htpy-parallel-cone Hf Hg c c') →
    gap f g c ~ map-equiv-standard-pullback-htpy Hf Hg ∘ gap f' g' c'
  triangle-is-pullback-htpy {p , q , H} {p' , q' , H'} (Hp , Hq , HH) z =
    map-extensionality-standard-pullback f g
      ( Hp z)
      ( Hq z)
      ( ( inv (assoc (ap f (Hp z)) (Hf (p' z) ∙ H' z) (inv (Hg (q' z))))) ∙
        ( inv
          ( right-transpose-eq-concat
            ( H z ∙ ap g (Hq z))
            ( Hg (q' z))
            ( ap f (Hp z) ∙ (Hf (p' z) ∙ H' z))
            ( ( assoc (H z) (ap g (Hq z)) (Hg (q' z))) ∙
              ( HH z) ∙
              ( assoc (ap f (Hp z)) (Hf (p' z)) (H' z))))))

  abstract
    is-pullback-htpy :
      {c : cone f g C} (c' : cone f' g' C)
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f' g' c' → is-pullback f g c
    is-pullback-htpy {c} c' H is-pb-c' =
      is-equiv-left-map-triangle
        ( gap f g c)
        ( map-equiv-standard-pullback-htpy Hf Hg)
        ( gap f' g' c')
        ( triangle-is-pullback-htpy H)
        ( is-pb-c')
        ( is-equiv-map-equiv-standard-pullback-htpy Hf Hg)

  abstract
    is-pullback-htpy' :
      (c : cone f g C) {c' : cone f' g' C}
      (Hc : htpy-parallel-cone Hf Hg c c') →
      is-pullback f g c → is-pullback f' g' c'
    is-pullback-htpy' c {c'} H =
      is-equiv-top-map-triangle
        ( gap f g c)
        ( map-equiv-standard-pullback-htpy Hf Hg)
        ( gap f' g' c')
        ( triangle-is-pullback-htpy H)
        ( is-equiv-map-equiv-standard-pullback-htpy Hf Hg)
```

### Dependent products of pullbacks are pullbacks

Given a family of pullback squares, their dependent product is again a pullback
square.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i))
  where

  triangle-map-standard-pullback-Π :
    map-Π (λ i → gap (f i) (g i) (c i)) ~
    map-standard-pullback-Π f g ∘ gap (map-Π f) (map-Π g) (cone-Π f g c)
  triangle-map-standard-pullback-Π h =
    eq-htpy
      ( λ i →
        map-extensionality-standard-pullback
          ( f i)
          ( g i)
          ( refl)
          ( refl)
          ( htpy-eq (is-section-eq-htpy _) i ∙ inv right-unit))

  abstract
    is-pullback-Π :
      ((i : I) → is-pullback (f i) (g i) (c i)) →
      is-pullback (map-Π f) (map-Π g) (cone-Π f g c)
    is-pullback-Π is-pb-c =
      is-equiv-top-map-triangle
        ( map-Π (λ i → gap (f i) (g i) (c i)))
        ( map-standard-pullback-Π f g)
        ( gap (map-Π f) (map-Π g) (cone-Π f g c))
        ( triangle-map-standard-pullback-Π)
        ( is-equiv-map-standard-pullback-Π f g)
        ( is-equiv-map-Π-is-fiberwise-equiv is-pb-c)
```

### Coproducts of pullbacks are pullbacks

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {C' : UU l4'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  abstract
    is-pullback-coproduct-is-pullback :
      (c : cone f g C) (c' : cone f' g' C') →
      is-pullback f g c →
      is-pullback f' g' c' →
      is-pullback
        ( map-coproduct f f')
        ( map-coproduct g g')
        ( coproduct-cone f g f' g' c c')
    is-pullback-coproduct-is-pullback c c' is-pb-c is-pb-c' =
      is-equiv-left-map-triangle
        ( gap
          ( map-coproduct f f')
          ( map-coproduct g g')
          ( coproduct-cone f g f' g' c c'))
        ( map-coproduct-cone-standard-pullback f g f' g')
        ( map-coproduct (gap f g c) (gap f' g' c'))
        ( triangle-map-coproduct-cone-standard-pullback f g f' g' c c')
        ( is-equiv-map-coproduct is-pb-c is-pb-c')
        ( is-equiv-map-coproduct-cone-standard-pullback f g f' g')
```

### In a commuting cube where the front faces are pullbacks, either back face is a pullback iff the other back face is

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : A → C} {h : B → D} {k : C → D}
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  {f' : A' → B'} {g' : A' → C'} {h' : B' → D'} {k' : C' → D'}
  {hA : A' → A} {hB : B' → B} {hC : C' → C} {hD : D' → D}
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  is-pullback-back-left-is-pullback-back-right-cube :
    is-pullback h hD (hB , h' , front-left) →
    is-pullback k hD (hC , k' , front-right) →
    is-pullback g hC (hA , g' , back-right) →
    is-pullback f hB (hA , f' , back-left)
  is-pullback-back-left-is-pullback-back-right-cube
    is-pb-front-left is-pb-front-right is-pb-back-right =
    is-pullback-left-square-is-pullback-rectangle f h hD
      ( hB , h' , front-left)
      ( hA , f' , back-left)
      ( is-pb-front-left)
      ( is-pullback-htpy
        ( bottom)
        ( refl-htpy)
        ( triple
          ( hA)
          ( k' ∘ g')
          ( rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))
        ( triple
          ( refl-htpy)
          ( top)
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c))
        ( is-pullback-rectangle-is-pullback-left-square g k hD
          ( hC , k' , front-right)
          ( hA , g' , back-right)
          ( is-pb-front-right)
          ( is-pb-back-right)))

  is-pullback-back-right-is-pullback-back-left-cube :
    is-pullback h hD (hB , h' , front-left) →
    is-pullback k hD (hC , k' , front-right) →
    is-pullback f hB (hA , f' , back-left) →
    is-pullback g hC (hA , g' , back-right)
  is-pullback-back-right-is-pullback-back-left-cube
    is-pb-front-left is-pb-front-right is-pb-back-left =
    is-pullback-left-square-is-pullback-rectangle g k hD
      ( hC , k' , front-right)
      ( hA , g' , back-right)
      ( is-pb-front-right)
      ( is-pullback-htpy'
        ( bottom)
        ( refl-htpy)
        ( triple
          ( hA)
          ( h' ∘ f')
          ( rectangle-left-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))
        ( triple
          ( refl-htpy)
          ( top)
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c))
        ( is-pullback-rectangle-is-pullback-left-square f h hD
          ( hB , h' , front-left)
          ( hA , f' , back-left)
          ( is-pb-front-left)
          ( is-pb-back-left)))
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pullback if and only if the top square is a pullback

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  is-pullback-bottom-is-pullback-top-cube-is-equiv :
    is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
    is-pullback h' k' (f' , g' , top) →
    is-pullback h k (f , g , bottom)
  is-pullback-bottom-is-pullback-top-cube-is-equiv
    is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-top =
    descent-is-equiv hB h k
      ( f , g , bottom)
      ( f' , hA , inv-htpy (back-left))
      ( is-equiv-hB)
      ( is-equiv-hA)
      ( is-pullback-htpy
        ( front-left)
        ( refl-htpy' k)
        ( triple
          ( f')
          ( hC ∘ g')
          ( rectangle-top-front-right-cube
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom))
        ( triple
          ( refl-htpy' f')
          ( back-right)
          ( coherence-htpy-parallel-cone-coherence-cube-maps
            f g h k f' g' h' k' hA hB hC hD
            top back-left back-right front-left front-right bottom c))
        ( is-pullback-rectangle-is-pullback-left-square
          ( h')
          ( hD)
          ( k)
          ( k' , hC , inv-htpy front-right)
          ( f' , g' , top)
          ( is-pullback-is-equiv-horizontal-maps hD k
            ( k' , hC , inv-htpy front-right)
            ( is-equiv-hD)
            ( is-equiv-hC))
          ( is-pb-top)))

  is-pullback-top-is-pullback-bottom-cube-is-equiv :
    is-equiv hA → is-equiv hB → is-equiv hC → is-equiv hD →
    is-pullback h k (f , g , bottom) →
    is-pullback h' k' (f' , g' , top)
  is-pullback-top-is-pullback-bottom-cube-is-equiv
    is-equiv-hA is-equiv-hB is-equiv-hC is-equiv-hD is-pb-bottom =
    is-pullback-top-is-pullback-rectangle h hD k'
      ( hB , h' , front-left)
      ( f' , g' , top)
      ( is-pullback-is-equiv-vertical-maps h hD
        ( hB , h' , front-left)
        is-equiv-hD is-equiv-hB)
      ( is-pullback-htpy' refl-htpy front-right
        ( pasting-vertical-cone h k hC
          ( f , g , bottom)
          ( hA , g' , back-right))
        ( triple
          ( back-left)
          ( refl-htpy)
          ( ( assoc-htpy
              ( bottom ·r hA)
              ( k ·l back-right)
              ( front-right ·r g')) ∙h
            ( inv-htpy c) ∙h
            ( assoc-htpy (h ·l back-left) (front-left ·r f') (hD ·l top)) ∙h
            ( ap-concat-htpy'
              ( (front-left ·r f') ∙h (hD ·l top))
              ( inv-htpy-right-unit-htpy {H = h ·l back-left}))))
        ( is-pullback-rectangle-is-pullback-top h k hC
          ( f , g , bottom)
          ( hA , g' , back-right)
          ( is-pb-bottom)
          ( is-pullback-is-equiv-vertical-maps g hC
            ( hA , g' , back-right)
            is-equiv-hC is-equiv-hA)))
```

### In a commuting cube where the maps from back-right to front-left are equivalences, the back-right square is a pullback if and only if the front-left square is a pullback

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : A → C) (h : B → D) (k : C → D)
  {A' : UU l1'} {B' : UU l2'} {C' : UU l3'} {D' : UU l4'}
  (f' : A' → B') (g' : A' → C') (h' : B' → D') (k' : C' → D')
  (hA : A' → A) (hB : B' → B) (hC : C' → C) (hD : D' → D)
  (top : h' ∘ f' ~ k' ∘ g')
  (back-left : f ∘ hA ~ hB ∘ f')
  (back-right : g ∘ hA ~ hC ∘ g')
  (front-left : h ∘ hB ~ hD ∘ h')
  (front-right : k ∘ hC ~ hD ∘ k')
  (bottom : h ∘ f ~ k ∘ g)
  (c :
    coherence-cube-maps
      f g h k f' g' h' k' hA hB hC hD
      top back-left back-right front-left front-right bottom)
  where

  is-pullback-front-left-is-pullback-back-right-cube-is-equiv :
    is-equiv f' → is-equiv f → is-equiv k' → is-equiv k →
    is-pullback g hC (hA , g' , back-right) →
    is-pullback h hD (hB , h' , front-left)
  is-pullback-front-left-is-pullback-back-right-cube-is-equiv
    is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right =
    is-pullback-bottom-is-pullback-top-cube-is-equiv
      hB h' h hD hA g' g hC f' f k' k
      back-right (inv-htpy back-left) top bottom (inv-htpy front-right)
      ( front-left)
      ( coherence-cube-maps-mirror-B f g h k f' g' h' k' hA hB hC hD top
        back-left back-right front-left front-right bottom c)
      is-equiv-f' is-equiv-f is-equiv-k' is-equiv-k is-pb-back-right

  is-pullback-front-right-is-pullback-back-left-cube-is-equiv :
    is-equiv g' → is-equiv h' → is-equiv g → is-equiv h →
    is-pullback f hB (hA , f' , back-left) →
    is-pullback k hD (hC , k' , front-right)
  is-pullback-front-right-is-pullback-back-left-cube-is-equiv
    is-equiv-g' is-equiv-h' is-equiv-g is-equiv-h is-pb-back-left =
    is-pullback-bottom-is-pullback-top-cube-is-equiv
      hC k' k hD hA f' f hB g' g h' h
      back-left (inv-htpy back-right) (inv-htpy top)
      ( inv-htpy bottom) (inv-htpy front-left) front-right
      ( coherence-cube-maps-rotate-120 f g h k f' g' h' k' hA hB hC hD
        top back-left back-right front-left front-right bottom c)
      is-equiv-g' is-equiv-g is-equiv-h' is-equiv-h is-pb-back-left
```

### Identity types commute with pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  cone-ap :
    (c1 c2 : C) →
    cone
      ( λ (α : vertical-map-cone f g c c1 ＝ vertical-map-cone f g c c2) →
        ap f α ∙ coherence-square-cone f g c c2)
      ( λ (β : horizontal-map-cone f g c c1 ＝ horizontal-map-cone f g c c2) →
        coherence-square-cone f g c c1 ∙ ap g β)
      ( c1 ＝ c2)
  pr1 (cone-ap c1 c2) = ap (vertical-map-cone f g c)
  pr1 (pr2 (cone-ap c1 c2)) = ap (horizontal-map-cone f g c)
  pr2 (pr2 (cone-ap c1 c2)) γ =
    ( right-whisker-concat
      ( inv (ap-comp f (vertical-map-cone f g c) γ))
      ( coherence-square-cone f g c c2)) ∙
    ( ( inv-nat-htpy (coherence-square-cone f g c) γ) ∙
      ( left-whisker-concat
        ( coherence-square-cone f g c c1)
        ( ap-comp g (horizontal-map-cone f g c) γ)))

  cone-ap' :
    (c1 c2 : C) →
    cone
      ( λ (α : vertical-map-cone f g c c1 ＝ vertical-map-cone f g c c2) →
        tr
          ( f (vertical-map-cone f g c c1) ＝_)
          ( coherence-square-cone f g c c2)
          ( ap f α))
      ( λ (β : horizontal-map-cone f g c c1 ＝ horizontal-map-cone f g c c2) →
        coherence-square-cone f g c c1 ∙ ap g β)
      ( c1 ＝ c2)
  pr1 (cone-ap' c1 c2) = ap (vertical-map-cone f g c)
  pr1 (pr2 (cone-ap' c1 c2)) = ap (horizontal-map-cone f g c)
  pr2 (pr2 (cone-ap' c1 c2)) γ =
    ( tr-Id-right
      ( coherence-square-cone f g c c2)
      ( ap f (ap (vertical-map-cone f g c) γ))) ∙
    ( ( right-whisker-concat
        ( inv (ap-comp f (vertical-map-cone f g c) γ))
        ( coherence-square-cone f g c c2)) ∙
      ( ( inv-nat-htpy (coherence-square-cone f g c) γ) ∙
        ( left-whisker-concat
          ( coherence-square-cone f g c c1)
          ( ap-comp g (horizontal-map-cone f g c) γ))))

  is-pullback-cone-ap :
    is-pullback f g c →
    (c1 c2 : C) →
    is-pullback
      ( λ (α : vertical-map-cone f g c c1 ＝ vertical-map-cone f g c c2) →
        ap f α ∙ coherence-square-cone f g c c2)
      ( λ (β : horizontal-map-cone f g c c1 ＝ horizontal-map-cone f g c c2) →
        coherence-square-cone f g c c1 ∙ ap g β)
      ( cone-ap c1 c2)
  is-pullback-cone-ap is-pb-c c1 c2 =
    is-pullback-htpy'
      ( λ α → tr-Id-right (coherence-square-cone f g c c2) (ap f α))
      ( refl-htpy)
      ( cone-ap' c1 c2)
      ( refl-htpy , refl-htpy , right-unit-htpy)
      ( is-pullback-family-is-pullback-tot
        ( f (vertical-map-cone f g c c1) ＝_)
        ( λ a → ap f {x = vertical-map-cone f g c c1} {y = a})
        ( λ b β → coherence-square-cone f g c c1 ∙ ap g β)
        ( c)
        ( cone-ap' c1)
        ( is-pb-c)
        ( is-pullback-is-equiv-vertical-maps
          ( map-Σ _ f (λ a α → ap f α))
          ( map-Σ _ g (λ b β → coherence-square-cone f g c c1 ∙ ap g β))
          ( tot-cone-cone-family
            ( f (vertical-map-cone f g c c1) ＝_)
            ( λ a → ap f)
            ( λ b β → coherence-square-cone f g c c1 ∙ ap g β)
            ( c)
            ( cone-ap' c1))
          ( is-equiv-is-contr _
            ( is-torsorial-Id (horizontal-map-cone f g c c1))
            ( is-torsorial-Id (f (vertical-map-cone f g c c1))))
          ( is-equiv-is-contr _
            ( is-torsorial-Id c1)
            ( is-torsorial-Id (vertical-map-cone f g c c1))))
        ( c2))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
