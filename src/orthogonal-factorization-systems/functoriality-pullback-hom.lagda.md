# Functoriality of the pullback-hom

```agda
module orthogonal-factorization-systems.functoriality-pullback-hom where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.bicomposition-functions
open import foundation.composition-algebra
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-pullbacks
open import foundation.homotopies
open import foundation.homotopies-morphisms-cospan-diagrams
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.morphisms-cospan-diagrams
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.retracts-of-maps
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The construction of the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is functorial.
There is a commuting triangle of ∞-categories

```text
  pairs of arrows of types -----> exponentiated cospan diagrams
                    \                 /
                     \               /
                      ∨             ∨
                      arrows of types
```

that maps pairs of arrows to their pullback-hom. We refer to either of the
vertical functors as the pullback-hom functor.

## Definitions

### The functorial map inducing morphisms of the pullback-hom cospan diagrams from morphisms of the arrows

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  where

  map-hom-cospan-diagram-hom-arrows-pullback-hom :
    hom-arrow f' f →
    hom-arrow g g' →
    hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f' g')
  map-hom-cospan-diagram-hom-arrows-pullback-hom F G =
    ( ( bicomp
        ( map-codomain-hom-arrow f' f F)
        ( map-codomain-hom-arrow g g' G)) ,
      ( bicomp
        ( map-domain-hom-arrow f' f F)
        ( map-domain-hom-arrow g g' G)) ,
      ( bicomp
        ( map-domain-hom-arrow f' f F)
        ( map-codomain-hom-arrow g g' G)) ,
      ( λ h →
        htpy-precomp
          ( coh-hom-arrow f' f F)
          ( Y')
          ( map-codomain-hom-arrow g g' G ∘ h)) ,
      ( λ h →
        htpy-postcomp
          ( A')
          ( inv-htpy (coh-hom-arrow g g' G))
          ( h ∘ map-domain-hom-arrow f' f F)))
```

### The functorial action on morphisms of cospan diagrams of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {l1' l2' l3' l4' : Level}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  where

  map-hom-cospan-diagram-pullback-hom :
    hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f' g') →
    hom-arrow f g → hom-arrow f' g'
  map-hom-cospan-diagram-pullback-hom =
    map-is-pullback
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f' g')
      ( cone-hom-arrow-pullback-hom f g)
      ( cone-hom-arrow-pullback-hom f' g')
      ( is-pullback-cone-hom-arrow-pullback-hom f g)
      ( is-pullback-cone-hom-arrow-pullback-hom f' g')
```

### The functorial action on morphisms of arrows of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {l1' l2' l3' l4' : Level}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  where

  map-hom-arrows-pullback-hom :
    hom-arrow f' f → hom-arrow g g' → hom-arrow f g → hom-arrow f' g'
  map-hom-arrows-pullback-hom F G =
    map-hom-cospan-diagram-pullback-hom f g f' g'
      ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f' g' F G)
```

## Properties

### The functorial map inducing morphisms of the pullback-hom cospan diagrams from morphisms of the arrows preserves identities

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  preserves-id-map-hom-cospan-diagram-hom-arrows-pullback-hom :
    htpy-hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f g)
      ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f g
        ( id-hom-arrow)
        ( id-hom-arrow))
      ( id-hom-cospan-diagram (cospan-diagram-pullback-hom f g))
  preserves-id-map-hom-cospan-diagram-hom-arrows-pullback-hom =
    ( refl-htpy ,
      refl-htpy ,
      refl-htpy ,
      right-unit-htpy ∙h compute-htpy-precomp-refl-htpy f Y ,
      right-unit-htpy ∙h compute-htpy-postcomp-refl-htpy A g)
```

### The functorial map inducing morphisms of the pullback-hom cospan diagrams from morphisms of the arrows preserves identities

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' l1'' l2'' l3'' l4'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''} {Y'' : UU l4''}
  (f'' : A'' → B'') (g'' : X'' → Y'')
  where

  left-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom :
    (F : hom-arrow f' f) (F' : hom-arrow f'' f') →
    (G' : hom-arrow g' g'') (G : hom-arrow g g') →
    left-square-coherence-htpy-hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f'' g'')
      ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f'' g''
        ( comp-hom-arrow f'' f' f F F')
        ( comp-hom-arrow g g' g'' G' G))
      ( comp-hom-cospan-diagram
        ( cospan-diagram-pullback-hom f g)
        ( cospan-diagram-pullback-hom f' g')
        ( cospan-diagram-pullback-hom f'' g'')
        ( map-hom-cospan-diagram-hom-arrows-pullback-hom f' g' f'' g'' F' G')
        ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f' g' F G))
      ( refl-htpy)
      ( refl-htpy)
  left-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom
    ( _ , hB , F) (hA' , _ , F') (_ , hY' , _) (_ , hY , _) h =
    equational-reasoning
    htpy-precomp ( hB ·l F' ∙h F ·r hA') Y'' (hY' ∘ hY ∘ h) ∙ refl
    ＝ htpy-precomp ( hB ·l F' ∙h F ·r hA') Y'' (hY' ∘ hY ∘ h)
    by right-unit
    ＝
      ( htpy-precomp (hB ·l F') Y'' ∙h htpy-precomp (F ·r hA') Y'')
      ( hY' ∘ hY ∘ h)
    by
      distributive-htpy-precomp-concat-htpy
        ( hB ·l F')
        ( F ·r hA')
        ( Y'')
        ( hY' ∘ hY ∘ h)
    ＝
      ( htpy-precomp F' Y'' (hY' ∘ hY ∘ h ∘ hB)) ∙
      ( ap
        ( precomp hA' Y'' ∘ postcomp A' hY')
        ( htpy-precomp F Y' (hY ∘ h)))
    by
      ap-binary (_∙_)
        ( distributive-htpy-precomp-left-whisker hB F' Y'' (hY' ∘ hY ∘ h))
        ( distributive-htpy-precomp-right-whisker hA' F Y'' (hY' ∘ hY ∘ h) ∙
          left-whisker-comp²
            ( precomp hA' Y'')
            ( commutative-postcomp-htpy-precomp hY' F)
            ( hY ∘ h) ∙
          preserves-comp-left-whisker-comp
            ( precomp hA' Y'')
            ( postcomp A' hY')
            ( htpy-precomp F Y')
            ( hY ∘ h))

  right-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom :
    (F : hom-arrow f' f) (F' : hom-arrow f'' f') →
    (G' : hom-arrow g' g'') (G : hom-arrow g g') →
    right-square-coherence-htpy-hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f'' g'')
      ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f'' g''
        ( comp-hom-arrow f'' f' f F F')
        ( comp-hom-arrow g g' g'' G' G))
      ( comp-hom-cospan-diagram
        ( cospan-diagram-pullback-hom f g)
        ( cospan-diagram-pullback-hom f' g')
        ( cospan-diagram-pullback-hom f'' g'')
        ( map-hom-cospan-diagram-hom-arrows-pullback-hom f' g' f'' g'' F' G')
        ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f' g' F G))
      ( refl-htpy)
      ( refl-htpy)
  right-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom
    ( hA , _ , _) (hA' , _ , _) (_ , hY' , G') (hX , _ , G) h =
    equational-reasoning
    htpy-postcomp A'' (inv-htpy (hY' ·l G ∙h G' ·r hX)) (h ∘ hA ∘ hA') ∙ refl
    ＝ htpy-postcomp A'' (inv-htpy (hY' ·l G ∙h G' ·r hX)) (h ∘ hA ∘ hA')
    by right-unit
    ＝
      ( htpy-postcomp A'' (inv-htpy (G' ·r hX)) ∙h
        htpy-postcomp A'' (hY' ·l inv-htpy G))
      ( h ∘ hA ∘ hA')
    by
      ( ap
        ( eq-htpy)
        ( eq-htpy
          ( ( distributive-inv-concat-htpy (hY' ·l G) (G' ·r hX) ∙h
              ap-concat-htpy
                ( inv-htpy (G' ·r hX))
                ( inv-htpy (left-whisker-inv-htpy hY' G))) ·r
            ( h ∘ hA ∘ hA')))) ∙
      ( distributive-htpy-postcomp-concat-htpy
        ( inv-htpy (G' ·r hX))
        ( hY' ·l inv-htpy G)
        ( A'')
        ( h ∘ hA ∘ hA'))
    ＝
      ( htpy-postcomp A'' (inv-htpy G') (hX ∘ h ∘ hA ∘ hA')) ∙
      ( ap
        ( postcomp A'' hY' ∘ precomp hA' Y')
        ( htpy-postcomp A' (inv-htpy G) (h ∘ hA)))
    by
      ap
        ( htpy-postcomp A''
          ( inv-htpy (G' ·r hX))
          ( h ∘ hA ∘ hA') ∙_)
        ( ( distributive-htpy-postcomp-left-whisker
            ( hY')
            ( inv-htpy G)
            ( A'')
            ( h ∘ hA ∘ hA')) ∙
          ( left-whisker-comp²
            ( postcomp A'' hY')
            ( commutative-precomp-htpy-postcomp hA' (inv-htpy G))
            ( h ∘ hA)) ∙
          ( preserves-comp-left-whisker-comp
            ( postcomp A'' hY')
            ( precomp hA' Y')
            ( htpy-postcomp A' (inv-htpy G))
            ( h ∘ hA)))

  preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom :
    (F : hom-arrow f' f) (F' : hom-arrow f'' f') →
    (G' : hom-arrow g' g'') (G : hom-arrow g g') →
    htpy-hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f'' g'')
      ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f'' g''
        ( comp-hom-arrow f'' f' f F F')
        ( comp-hom-arrow g g' g'' G' G))
      ( comp-hom-cospan-diagram
        ( cospan-diagram-pullback-hom f g)
        ( cospan-diagram-pullback-hom f' g')
        ( cospan-diagram-pullback-hom f'' g'')
        ( map-hom-cospan-diagram-hom-arrows-pullback-hom f' g' f'' g'' F' G')
        ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f' g' F G))
  preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom
    F F' G' G =
    ( refl-htpy ,
      refl-htpy ,
      refl-htpy ,
      left-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom
        F F' G' G ,
      right-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom
        F F' G' G)
```

### The functorial action of the pullback-hom on cospan diagrams preserves identities

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  preserves-id-map-hom-cospan-diagram-pullback-hom :
    map-hom-cospan-diagram-pullback-hom f g f g
      ( id-hom-cospan-diagram (cospan-diagram-pullback-hom f g)) ~ id
  preserves-id-map-hom-cospan-diagram-pullback-hom =
    preserves-id-map-is-pullback
      ( cospan-diagram-pullback-hom f g)
      ( cone-hom-arrow-pullback-hom f g)
      ( is-pullback-cone-hom-arrow-pullback-hom f g)
```

### The functorial action of the pullback-hom on cospan diagrams preserves composition

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' l1'' l2'' l3'' l4'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''} {Y'' : UU l4''}
  (f'' : A'' → B'') (g'' : X'' → Y'')
  where

  preserves-comp-map-hom-cospan-diagram-pullback-hom :
    (h : hom-cospan-diagram
      ( cospan-diagram-pullback-hom f' g')
      ( cospan-diagram-pullback-hom f'' g'')) →
    (h' : hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f' g')) →
    map-hom-cospan-diagram-pullback-hom f g f'' g''
      ( comp-hom-cospan-diagram
        ( cospan-diagram-pullback-hom f g)
        ( cospan-diagram-pullback-hom f' g')
        ( cospan-diagram-pullback-hom f'' g'')
        ( h)
        ( h')) ~
    map-hom-cospan-diagram-pullback-hom f' g' f'' g'' h ∘
    map-hom-cospan-diagram-pullback-hom f g f' g' h'
  preserves-comp-map-hom-cospan-diagram-pullback-hom =
    preserves-comp-map-is-pullback
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f' g')
      ( cospan-diagram-pullback-hom f'' g'')
      ( cone-hom-arrow-pullback-hom f g)
      ( cone-hom-arrow-pullback-hom f' g')
      ( cone-hom-arrow-pullback-hom f'' g'')
      ( is-pullback-cone-hom-arrow-pullback-hom f g)
      ( is-pullback-cone-hom-arrow-pullback-hom f' g')
      ( is-pullback-cone-hom-arrow-pullback-hom f'' g'')
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
