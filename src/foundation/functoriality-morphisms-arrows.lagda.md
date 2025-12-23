# Functoriality of morphisms of arrows

```agda
module foundation.functoriality-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.bicomposition-functions
open import foundation.commuting-squares-of-maps
open import foundation.composition-algebra
open import foundation.cones-over-cospan-diagrams
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-pullbacks
open import foundation.homotopies
open import foundation.homotopies-morphisms-arrows
open import foundation.homotopies-morphisms-cospan-diagrams
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.morphisms-cospan-diagrams
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.pullback-cones
open import foundation.pullbacks
open import foundation.retractions
open import foundation.retracts-of-arrows
open import foundation.sections
open import foundation.standard-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition
```

</details>

## Idea

The construction of [morphisms of arrows](foundation.morphisms-arrows.md) is
functorial. We have a functorial action on pairs of
[morphisms of arrows](foundation.morphisms-arrows.md)

```text
  (α : f' ⇒ f, β : g ⇒ g') ↦ α ⇒ β : (f ⇒ g) → (f' ⇒ g')
```

We construct this functorial action as the restriction of a more general action
on morphisms of _exponentiated cospan diagrams_ of the form:

```text
            - ∘ f           g ∘ -
   (B → Y) ------> (A → Y) <------ (A → X)
      |               |               |
      |               |               |
      ∨     - ∘ f'    ∨    g' ∘ -     ∨
  (B' → Y') ----> (A' → Y') <---- (A' → X').
```

In general, such morphisms need not necessarily come from pairs of morphisms of
the underlying arrows.

This gives us a commuting triangle of functors

```text
  [pairs of arrows of types] ---> [exponentiated cospan diagrams]
                     \                 /
                      \               /
                       ∨             ∨
                      [arrows of types]
```

where the functorial action of morphisms of arrows is the left vertical arrow.

## Definitions

### The type of morphisms of arrows as a pullback

Given two maps `f : A → B` and `g : X → Y`, then the type of morphisms of arrows
from `f` to `g` is the pullback

```text
  hom-arrow f g ---------> (A → X)
        | ⌟                   |
        |                     | g ∘ -
        ∨                     ∨
     (B → Y) ------------> (A → Y).
                 - ∘ f
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  cospan-diagram-hom-arrow : cospan-diagram (l2 ⊔ l4) (l1 ⊔ l3) (l1 ⊔ l4)
  cospan-diagram-hom-arrow =
    ( (B → Y) , (A → X) , (A → Y) , precomp f Y , postcomp A g)

  coherence-square-cone-hom-arrow :
    coherence-square-maps
      ( map-domain-hom-arrow f g)
      ( map-codomain-hom-arrow f g)
      ( postcomp A g)
      ( precomp f Y)
  coherence-square-cone-hom-arrow h = eq-htpy (coh-hom-arrow f g h)

  cone-hom-arrow' :
    cone (precomp f Y) (postcomp A g) (hom-arrow f g)
  cone-hom-arrow' =
    ( map-codomain-hom-arrow f g ,
      map-domain-hom-arrow f g ,
      coherence-square-cone-hom-arrow)

  module _
    (h : standard-pullback (precomp f Y) (postcomp A g))
    where

    map-domain-map-inv-gap-hom-arrow : A → X
    map-domain-map-inv-gap-hom-arrow = pr1 (pr2 h)

    map-codomain-map-inv-gap-hom-arrow : B → Y
    map-codomain-map-inv-gap-hom-arrow = pr1 h

    eq-coh-map-inv-gap-hom-arrow :
      precomp f Y map-codomain-map-inv-gap-hom-arrow ＝
      postcomp A g map-domain-map-inv-gap-hom-arrow
    eq-coh-map-inv-gap-hom-arrow = pr2 (pr2 h)

    coh-map-inv-gap-hom-arrow :
      precomp f Y map-codomain-map-inv-gap-hom-arrow ~
      postcomp A g map-domain-map-inv-gap-hom-arrow
    coh-map-inv-gap-hom-arrow = htpy-eq eq-coh-map-inv-gap-hom-arrow

    map-inv-gap-hom-arrow : hom-arrow f g
    map-inv-gap-hom-arrow =
      ( map-domain-map-inv-gap-hom-arrow ,
        map-codomain-map-inv-gap-hom-arrow ,
        coh-map-inv-gap-hom-arrow)

  is-section-map-inv-gap-hom-arrow :
    is-section
      ( gap (precomp f Y) (postcomp A g) cone-hom-arrow')
      ( map-inv-gap-hom-arrow)
  is-section-map-inv-gap-hom-arrow h =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( is-retraction-eq-htpy (eq-coh-map-inv-gap-hom-arrow h)))

  is-retraction-map-inv-gap-hom-arrow :
    is-retraction
      ( gap (precomp f Y) (postcomp A g) cone-hom-arrow')
      ( map-inv-gap-hom-arrow)
  is-retraction-map-inv-gap-hom-arrow h =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( is-section-eq-htpy (coh-hom-arrow f g h)))

  is-pullback-hom-arrow :
    is-pullback (precomp f Y) (postcomp A g) cone-hom-arrow'
  is-pullback-hom-arrow =
    is-equiv-is-invertible
      ( map-inv-gap-hom-arrow)
      ( is-section-map-inv-gap-hom-arrow)
      ( is-retraction-map-inv-gap-hom-arrow)

  pullback-cone-hom-arrow :
    pullback-cone cospan-diagram-hom-arrow (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pullback-cone-hom-arrow =
    ( (hom-arrow f g , cone-hom-arrow') , is-pullback-hom-arrow)
```

### The bifunctorial map on morphisms of arrows inducing morphisms of the associated cospan diagrams of morphisms of arrows

Given morphisms of arrows `F : f' → f` and `G : g → g'`:

```text
            F₀                        G₀
      A' -------> A             X --------> X'
      |           |             |           |
   f' |     F     | f   and   g |     G     | g'
      ∨           ∨             ∨           ∨
      B' -------> B             Y --------> Y',
            F₁                        G₁
```

there is an associated morphism of cospan diagrams

```text
              - ∘ f           g ∘ -
     (B → Y) ------> (A → Y) <------ (A → X)
        |               |               |
        |               |               |
  (F₁ ∘ - ∘ G₁)   (G₁ ∘ - ∘ F₀)   (G₀ ∘ - ∘ F₀)
        |               |               |
        ∨     - ∘ f'    ∨    g' ∘ -     ∨
    (B' → Y') ----> (A' → Y') <---- (A' → X')
```

and this construction is bifunctorial.

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f : A → B) (g : X → Y) (f' : A' → B') (g' : X' → Y')
  where

  map-hom-cospan-diagram-hom-arrows :
    hom-arrow f' f → hom-arrow g g' →
    hom-cospan-diagram
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f' g')
  map-hom-cospan-diagram-hom-arrows (F₀ , F₁ , F) (G₀ , G₁ , G) =
    ( ( bicomp F₁ G₁) ,
      ( bicomp F₀ G₀) ,
      ( bicomp F₀ G₁) ,
      ( htpy-precomp F Y' ·r postcomp B G₁) ,
      ( htpy-postcomp A' (inv-htpy G) ·r precomp F₀ X))
```

### The functorial action on morphisms of cospan diagrams of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f : A → B) (g : X → Y) (f' : A' → B') (g' : X' → Y')
  where

  map-hom-arrow-hom-cospan-diagram :
    hom-cospan-diagram
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f' g') →
    hom-arrow f g →
    hom-arrow f' g'
  map-hom-arrow-hom-cospan-diagram =
    map-pullback-cone
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f' g')
      ( pullback-cone-hom-arrow f g)
      ( pullback-cone-hom-arrow f' g')
```

### The bifunctorial action of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f : A → B) (g : X → Y) (f' : A' → B') (g' : X' → Y')
  where

  map-hom-arrow :
    hom-arrow f' f → hom-arrow g g' → hom-arrow f g → hom-arrow f' g'
  map-hom-arrow F G =
    map-hom-arrow-hom-cospan-diagram f g f' g'
      ( map-hom-cospan-diagram-hom-arrows f g f' g' F G)
```

## Properties

### The bifunctorial map on morphisms of arrows inducing morphisms of the associated cospan diagrams of morphisms of arrows preserves homotopies

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f : A → B) (g : X → Y) (f' : A' → B') (g' : X' → Y')
  where

  htpy-eq-map-hom-cospan-diagram-hom-arrows :
    (F F' : hom-arrow f' f) (G G' : hom-arrow g g') →
    F ＝ F' → G ＝ G' →
    htpy-hom-cospan-diagram
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f' g')
      ( map-hom-cospan-diagram-hom-arrows f g f' g' F G)
      ( map-hom-cospan-diagram-hom-arrows f g f' g' F' G')
  htpy-eq-map-hom-cospan-diagram-hom-arrows F .F G .G refl refl =
    refl-htpy-hom-cospan-diagram
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f' g')
      ( map-hom-cospan-diagram-hom-arrows f g f' g' F G)

  abstract
    preserves-htpy-map-hom-cospan-diagram-hom-arrows :
      (F F' : hom-arrow f' f) (G G' : hom-arrow g g') →
      htpy-hom-arrow f' f F F' → htpy-hom-arrow g g' G G' →
      htpy-hom-cospan-diagram
        ( cospan-diagram-hom-arrow f g)
        ( cospan-diagram-hom-arrow f' g')
        ( map-hom-cospan-diagram-hom-arrows f g f' g' F G)
        ( map-hom-cospan-diagram-hom-arrows f g f' g' F' G')
    preserves-htpy-map-hom-cospan-diagram-hom-arrows
      F F' G G' H K =
      htpy-eq-map-hom-cospan-diagram-hom-arrows F F' G G'
        ( eq-htpy-hom-arrow f' f F F' H)
        ( eq-htpy-hom-arrow g g' G G' K)
```

### The bifunctorial map on morphisms of arrows inducing morphisms of the associated cospan diagrams of morphisms of arrows preserves identities

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  preserves-id-map-hom-cospan-diagram-hom-arrows :
    htpy-hom-cospan-diagram
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f g)
      ( map-hom-cospan-diagram-hom-arrows f g f g
        ( id-hom-arrow)
        ( id-hom-arrow))
      ( id-hom-cospan-diagram (cospan-diagram-hom-arrow f g))
  preserves-id-map-hom-cospan-diagram-hom-arrows =
    ( refl-htpy ,
      refl-htpy ,
      refl-htpy ,
      right-unit-htpy ∙h compute-htpy-precomp-refl-htpy f Y ,
      right-unit-htpy ∙h compute-htpy-postcomp-refl-htpy A g)
```

### The bifunctorial map on morphisms of arrows inducing morphisms of the associated cospan diagrams of morphisms of arrows preserves identities

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' l1'' l2'' l3'' l4'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''} {Y'' : UU l4''}
  (f : A → B) (g : X → Y)
  (f' : A' → B') (g' : X' → Y')
  (f'' : A'' → B'') (g'' : X'' → Y'')
  where

  left-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows :
    (F : hom-arrow f' f) (F' : hom-arrow f'' f') →
    (G' : hom-arrow g' g'') (G : hom-arrow g g') →
    left-square-coherence-htpy-hom-cospan-diagram
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f'' g'')
      ( map-hom-cospan-diagram-hom-arrows f g f'' g''
        ( comp-hom-arrow f'' f' f F F')
        ( comp-hom-arrow g g' g'' G' G))
      ( comp-hom-cospan-diagram
        ( cospan-diagram-hom-arrow f g)
        ( cospan-diagram-hom-arrow f' g')
        ( cospan-diagram-hom-arrow f'' g'')
        ( map-hom-cospan-diagram-hom-arrows f' g' f'' g'' F' G')
        ( map-hom-cospan-diagram-hom-arrows f g f' g' F G))
      ( refl-htpy)
      ( refl-htpy)
  left-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows
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

  right-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows :
    (F : hom-arrow f' f) (F' : hom-arrow f'' f') →
    (G' : hom-arrow g' g'') (G : hom-arrow g g') →
    right-square-coherence-htpy-hom-cospan-diagram
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f'' g'')
      ( map-hom-cospan-diagram-hom-arrows f g f'' g''
        ( comp-hom-arrow f'' f' f F F')
        ( comp-hom-arrow g g' g'' G' G))
      ( comp-hom-cospan-diagram
        ( cospan-diagram-hom-arrow f g)
        ( cospan-diagram-hom-arrow f' g')
        ( cospan-diagram-hom-arrow f'' g'')
        ( map-hom-cospan-diagram-hom-arrows f' g' f'' g'' F' G')
        ( map-hom-cospan-diagram-hom-arrows f g f' g' F G))
      ( refl-htpy)
      ( refl-htpy)
  right-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows
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

  preserves-comp-map-hom-cospan-diagram-hom-arrows :
    (F : hom-arrow f' f) (F' : hom-arrow f'' f') →
    (G' : hom-arrow g' g'') (G : hom-arrow g g') →
    htpy-hom-cospan-diagram
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f'' g'')
      ( map-hom-cospan-diagram-hom-arrows f g f'' g''
        ( comp-hom-arrow f'' f' f F F')
        ( comp-hom-arrow g g' g'' G' G))
      ( comp-hom-cospan-diagram
        ( cospan-diagram-hom-arrow f g)
        ( cospan-diagram-hom-arrow f' g')
        ( cospan-diagram-hom-arrow f'' g'')
        ( map-hom-cospan-diagram-hom-arrows f' g' f'' g'' F' G')
        ( map-hom-cospan-diagram-hom-arrows f g f' g' F G))
  preserves-comp-map-hom-cospan-diagram-hom-arrows
    F F' G' G =
    ( refl-htpy ,
      refl-htpy ,
      refl-htpy ,
      left-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows
        F F' G' G ,
      right-htpy-preserves-comp-map-hom-cospan-diagram-hom-arrows
        F F' G' G)
```

### The functorial action of morphisms of arrows on cospan diagrams preserves identities

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  preserves-id-map-hom-arrow-hom-cospan-diagram :
    map-hom-arrow-hom-cospan-diagram f g f g
      ( id-hom-cospan-diagram (cospan-diagram-hom-arrow f g)) ~ id
  preserves-id-map-hom-arrow-hom-cospan-diagram =
    preserves-id-map-pullback-cone
      ( cospan-diagram-hom-arrow f g)
      ( pullback-cone-hom-arrow f g)
```

### The functorial action of morphisms of arrows on cospan diagrams preserves composition

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' l1'' l2'' l3'' l4'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''} {Y'' : UU l4''}
  (f : A → B) (g : X → Y)
  (f' : A' → B') (g' : X' → Y')
  (f'' : A'' → B'') (g'' : X'' → Y'')
  where

  preserves-comp-map-hom-arrow-hom-cospan-diagram :
    (h :
      hom-cospan-diagram
        ( cospan-diagram-hom-arrow f' g')
        ( cospan-diagram-hom-arrow f'' g'')) →
    (h' :
      hom-cospan-diagram
        ( cospan-diagram-hom-arrow f g)
        ( cospan-diagram-hom-arrow f' g')) →
    map-hom-arrow-hom-cospan-diagram f g f'' g''
      ( comp-hom-cospan-diagram
        ( cospan-diagram-hom-arrow f g)
        ( cospan-diagram-hom-arrow f' g')
        ( cospan-diagram-hom-arrow f'' g'')
        ( h)
        ( h')) ~
    map-hom-arrow-hom-cospan-diagram f' g' f'' g'' h ∘
    map-hom-arrow-hom-cospan-diagram f g f' g' h'
  preserves-comp-map-hom-arrow-hom-cospan-diagram =
    preserves-comp-map-pullback-cone
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f' g')
      ( cospan-diagram-hom-arrow f'' g'')
      ( pullback-cone-hom-arrow f g)
      ( pullback-cone-hom-arrow f' g')
      ( pullback-cone-hom-arrow f'' g'')
```

### The functorial action of morphisms of arrows on cospan diagrams preserves homotopies

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f' : A' → B') (g' : X' → Y')
  where

  preserves-htpy-map-hom-arrow-hom-cospan-diagram :
    ( h h' :
      hom-cospan-diagram
        ( cospan-diagram-hom-arrow f g)
        ( cospan-diagram-hom-arrow f' g'))
    ( H :
      htpy-hom-cospan-diagram
        ( cospan-diagram-hom-arrow f g)
        ( cospan-diagram-hom-arrow f' g')
        ( h)
        ( h')) →
    map-hom-arrow-hom-cospan-diagram f g f' g' h ~
    map-hom-arrow-hom-cospan-diagram f g f' g' h'
  preserves-htpy-map-hom-arrow-hom-cospan-diagram =
    preserves-htpy-map-pullback-cone
      ( cospan-diagram-hom-arrow f g)
      ( cospan-diagram-hom-arrow f' g')
      ( pullback-cone-hom-arrow f g)
      ( pullback-cone-hom-arrow f' g')
```

### The bifunctorial action of morphisms of arrows preserves identities

**Proof.** This follows by the fact that functors compose.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  preserves-id-map-hom-arrow :
    map-hom-arrow f g f g id-hom-arrow id-hom-arrow ~ id
  preserves-id-map-hom-arrow =
    ( preserves-htpy-map-hom-arrow-hom-cospan-diagram f g f g
      ( map-hom-cospan-diagram-hom-arrows f g f g
        ( id-hom-arrow)
        ( id-hom-arrow))
      ( id-hom-cospan-diagram (cospan-diagram-hom-arrow f g))
      ( preserves-id-map-hom-cospan-diagram-hom-arrows f g)) ∙h
    ( preserves-id-map-hom-arrow-hom-cospan-diagram f g)
```

### The bifunctorial action of morphisms of arrows preserves composition

**Proof.** This follows by the fact that functors compose.

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' l1'' l2'' l3'' l4'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''} {Y'' : UU l4''}
  (f : A → B) (g : X → Y)
  (f' : A' → B') (g' : X' → Y')
  (f'' : A'' → B'') (g'' : X'' → Y'')
  where

  preserves-comp-map-hom-arrow :
    (F : hom-arrow f' f) (F' : hom-arrow f'' f') →
    (G' : hom-arrow g' g'') (G : hom-arrow g g') →
    map-hom-arrow f g f'' g''
      ( comp-hom-arrow f'' f' f F F')
      ( comp-hom-arrow g g' g'' G' G) ~
    map-hom-arrow f' g' f'' g'' F' G' ∘
    map-hom-arrow f g f' g' F G
  preserves-comp-map-hom-arrow F F' G' G =
    ( preserves-htpy-map-hom-arrow-hom-cospan-diagram f g f'' g''
      ( map-hom-cospan-diagram-hom-arrows f g f'' g''
        ( comp-hom-arrow f'' f' f F F')
        ( comp-hom-arrow g g' g'' G' G))
      ( comp-hom-cospan-diagram
        ( cospan-diagram-hom-arrow f g)
        ( cospan-diagram-hom-arrow f' g')
        ( cospan-diagram-hom-arrow f'' g'')
        ( map-hom-cospan-diagram-hom-arrows f' g' f'' g'' F' G')
        ( map-hom-cospan-diagram-hom-arrows f g f' g' F G))
      ( preserves-comp-map-hom-cospan-diagram-hom-arrows
          f g f' g' f'' g'' F F' G' G)) ∙h
    ( preserves-comp-map-hom-arrow-hom-cospan-diagram f g f' g' f'' g''
      ( map-hom-cospan-diagram-hom-arrows f' g' f'' g'' F' G')
      ( map-hom-cospan-diagram-hom-arrows f g f' g' F G))
```

### The bifunctorial action of morphisms of arrows preserves homotopies

**Proof.** This follows by the fact that functors compose.

```agda
module _
  {l1 l2 l3 l4 l1' l2' l3' l4' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} {Y' : UU l4'}
  (f : A → B) (g : X → Y) (f' : A' → B') (g' : X' → Y')
  where

  abstract
    preserves-htpy-map-hom-arrow :
      (F F' : hom-arrow f' f) (G G' : hom-arrow g g') →
      htpy-hom-arrow f' f F F' → htpy-hom-arrow g g' G G' →
      map-hom-arrow f g f' g' F G ~
      map-hom-arrow f g f' g' F' G'
    preserves-htpy-map-hom-arrow F F' G G' HF HG =
      preserves-htpy-map-hom-arrow-hom-cospan-diagram f g f' g'
        ( map-hom-cospan-diagram-hom-arrows f g f' g' F G)
        ( map-hom-cospan-diagram-hom-arrows f g f' g' F' G')
        ( preserves-htpy-map-hom-cospan-diagram-hom-arrows
            f g f' g' F F' G G' HF HG)
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
