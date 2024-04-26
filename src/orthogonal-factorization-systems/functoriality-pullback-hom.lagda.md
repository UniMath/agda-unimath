# Functoriality of the pullback-hom

```agda
module orthogonal-factorization-systems.functoriality-pullback-hom where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.bicomposition-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.composition-algebra
open import foundation.functoriality-pullbacks
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.morphisms-cospan-diagrams
open import foundation.homotopies-morphisms-cospan-diagrams
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.retracts-of-maps
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-higher-homotopies-composition

open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The construction of the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is functorial.

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

<!-- TODO Show this is bifunctorial -->

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

  preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom :
    (F : hom-arrow f' f) (F' : hom-arrow f'' f') →
    (G : hom-arrow g' g'') (G' : hom-arrow g g') →
    htpy-hom-cospan-diagram
      ( cospan-diagram-pullback-hom f g)
      ( cospan-diagram-pullback-hom f'' g'')
      ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f'' g''
        ( comp-hom-arrow f'' f' f F F')
        ( comp-hom-arrow g g' g'' G G'))
      ( comp-hom-cospan-diagram
        ( cospan-diagram-pullback-hom f g)
        ( cospan-diagram-pullback-hom f' g')
        ( cospan-diagram-pullback-hom f'' g'')
        ( map-hom-cospan-diagram-hom-arrows-pullback-hom f' g' f'' g'' F' G)
        ( map-hom-cospan-diagram-hom-arrows-pullback-hom f g f' g' F G'))
  preserves-comp-map-hom-cospan-diagram-hom-arrows-pullback-hom F F' G G' =
    ( refl-htpy ,
      refl-htpy ,
      refl-htpy ,
      ( λ h →
        equational-reasoning
        _
        ＝
          htpy-precomp
            ( map-codomain-hom-arrow f' f F ·l coh-hom-arrow f'' f' F' ∙h
              coh-hom-arrow f' f F ·r (map-domain-hom-arrow f'' f' F'))
            ( Y'')
            ( map-codomain-hom-arrow g' g'' G ∘
              map-codomain-hom-arrow g g' G' ∘
              h)
        by right-unit
        ＝
          ( htpy-precomp
            ( map-codomain-hom-arrow f' f F ·l coh-hom-arrow f'' f' F') Y'' ∙h
          htpy-precomp (coh-hom-arrow f' f F ·r map-domain-hom-arrow f'' f' F') Y'')
          ( map-codomain-hom-arrow g' g'' G ∘ map-codomain-hom-arrow g g' G' ∘ h)
        by distributive-htpy-precomp-concat-htpy (map-codomain-hom-arrow f' f F ·l coh-hom-arrow f'' f' F') (coh-hom-arrow f' f F ·r (map-domain-hom-arrow f'' f' F')) (Y'') (map-codomain-hom-arrow g' g'' G ∘ map-codomain-hom-arrow g g' G' ∘ h)
        ＝ _
        by
          ap-binary (_∙_)
            ( distributive-htpy-precomp-left-whisker
              ( map-codomain-hom-arrow f' f F)
              ( coh-hom-arrow f'' f' F')
              ( Y'')
              ( map-codomain-hom-arrow g' g'' G ∘
                map-codomain-hom-arrow g g' G' ∘
                h))
            ( distributive-htpy-precomp-right-whisker
              ( map-domain-hom-arrow f'' f' F')
              ( coh-hom-arrow f' f F)
              ( Y'')
              ( map-codomain-hom-arrow g' g'' G ∘
                map-codomain-hom-arrow g g' G' ∘
                h) ∙
            left-whisker-comp²
              ( precomp (map-domain-hom-arrow f'' f' F') Y'')
              ( commutative-postcomp-htpy-precomp
                ( map-codomain-hom-arrow g' g'' G)
                ( coh-hom-arrow f' f F))
              ( map-codomain-hom-arrow g g' G' ∘ h) ∙
            preserves-comp-left-whisker-comp
              ( precomp (map-domain-hom-arrow f'' f' F') Y'')
              ( postcomp A' (map-codomain-hom-arrow g' g'' G))
              ( htpy-precomp (coh-hom-arrow f' f F)  Y')
              ( map-codomain-hom-arrow g g' G' ∘ h))
        ＝ htpy-precomp
            ( coh-hom-arrow f'' f' F')
            ( Y'')
            ( map-codomain-hom-arrow g' g'' G ∘
              map-codomain-hom-arrow g g' G' ∘
              h ∘
              map-codomain-hom-arrow f' f F) ∙
          ap
            ( precomp (map-domain-hom-arrow f'' f' F') Y'' ∘
              postcomp A' (map-codomain-hom-arrow g' g'' G))
            ( htpy-precomp
              ( coh-hom-arrow f' f F) Y'
              ( map-codomain-hom-arrow g g' G' ∘ h))
        by refl) ,
        ( λ h →
          equational-reasoning
          _
          ＝ eq-htpy (λ x → inv (ap (pr1 (pr2 G)) (coh-hom-arrow g g' G' (h (pr1 F (pr1 F' x)))) ∙ pr2 (pr2 G) (pr1 G' (h (pr1 F (pr1 F' x)))))) by right-unit
          ＝ (htpy-postcomp A'' (inv-htpy (coh-hom-arrow g' g'' G ·r pr1 G')) ∙h htpy-postcomp A'' ( (map-codomain-hom-arrow g' g'' G ·l (inv-htpy (coh-hom-arrow g g' G'))))) (h ∘ pr1 F ∘ pr1 F')
          by
            ap eq-htpy
              ( eq-htpy
                ( ( distributive-inv-concat-htpy
                    ( map-codomain-hom-arrow g' g'' G ·l coh-hom-arrow g g' G')
                    ( ( coh-hom-arrow g' g'' G) ·r
                      ( map-domain-hom-arrow g g' G')) ∙h
                    ap-concat-htpy ((inv-htpy (coh-hom-arrow g' g'' G ·r pr1 G'))) (inv-htpy (left-whisker-inv-htpy (map-codomain-hom-arrow g' g'' G) (coh-hom-arrow g g' G')))) ·r
                  ( h ∘
                    map-domain-hom-arrow f' f F ∘
                    map-domain-hom-arrow f'' f' F'))) ∙
            distributive-htpy-postcomp-concat-htpy
              ( inv-htpy
                ( coh-hom-arrow g' g'' G ·r map-domain-hom-arrow g g' G'))
              ( ( map-codomain-hom-arrow g' g'' G ·l (inv-htpy (coh-hom-arrow g g' G'))))
              ( A'')
              ( h ∘ pr1 F ∘ pr1 F')
          ＝ eq-htpy
              ( inv-htpy (coh-hom-arrow g' g'' G) ·r (pr1 G' ∘ h ∘ pr1 F ∘ pr1 F')) ∙
              ap (postcomp  A'' (map-codomain-hom-arrow g' g'' G) ∘ precomp (pr1 F') Y') (eq-htpy (inv-htpy (coh-hom-arrow g g' G') ·r (h ∘ pr1 F)))
              by
                ap
                  ( htpy-postcomp A''
                    ( inv-htpy (coh-hom-arrow g' g'' G ·r pr1 G'))
                    ( h ∘ pr1 F ∘ pr1 F') ∙_)
                  (distributive-htpy-postcomp-left-whisker
                    ( map-codomain-hom-arrow g' g'' G)
                    ( inv-htpy (coh-hom-arrow g g' G'))
                    ( A'')
                    ( h ∘ map-domain-hom-arrow f' f F ∘ map-domain-hom-arrow f'' f' F') ∙
                    left-whisker-comp² (postcomp A'' (map-codomain-hom-arrow g' g'' G)) (commutative-precomp-htpy-postcomp (pr1 F') (inv-htpy (coh-hom-arrow g g' G'))) (h ∘ pr1 F) ∙
                    preserves-comp-left-whisker-comp
                      ( postcomp A'' (map-codomain-hom-arrow g' g'' G))
                      ( precomp (pr1 F') Y') (htpy-postcomp A' (inv-htpy (coh-hom-arrow g g' G'))) (h  ∘ pr1 F))))
```

### The functorial action of the pullback-hom preserves identities

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

## The functorial action of the pullback-hom preserves composition

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
