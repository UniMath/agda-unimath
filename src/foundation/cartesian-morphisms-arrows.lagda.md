# Cartesian morphisms of arrows

```agda
module foundation.cartesian-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.pullbacks
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

A [morphism of arrows](foundation.morphisms-arrows.md) `h : f → g` is said to be
{{#concept "cartesian" Disambiguation="morphism of arrows" Agda=is-cartesian-hom-arrow}}
if the [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
        i
    A -----> X
    |        |
  f |   h    | g
    V        V
    B -----> Y
        j
```

is a [pullback](foundation.pullbacks.md) square. In this instance, we also say
that `f` is a {{#concept "base change" Disambiguation="maps of types"}} of `g`.

## Definitions

### The predicate of being a cartesian morphism of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  is-cartesian-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cartesian-hom-arrow =
    is-pullback (map-codomain-hom-arrow f g h) g (cone-hom-arrow f g h)

  is-prop-is-cartesian-hom-arrow : is-prop is-cartesian-hom-arrow
  is-prop-is-cartesian-hom-arrow =
    is-prop-is-pullback (map-codomain-hom-arrow f g h) g (cone-hom-arrow f g h)

  is-cartesian-hom-arrow-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-cartesian-hom-arrow-Prop = is-cartesian-hom-arrow
  pr2 is-cartesian-hom-arrow-Prop = is-prop-is-cartesian-hom-arrow
```

### The type of cartesian morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  cartesian-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cartesian-hom-arrow = Σ (hom-arrow f g) (is-cartesian-hom-arrow f g)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : cartesian-hom-arrow f g)
  where

  hom-arrow-cartesian-hom-arrow : hom-arrow f g
  hom-arrow-cartesian-hom-arrow = pr1 h

  is-cartesian-cartesian-hom-arrow :
    is-cartesian-hom-arrow f g hom-arrow-cartesian-hom-arrow
  is-cartesian-cartesian-hom-arrow = pr2 h

  map-domain-cartesian-hom-arrow : A → X
  map-domain-cartesian-hom-arrow =
    map-domain-hom-arrow f g hom-arrow-cartesian-hom-arrow

  map-codomain-cartesian-hom-arrow : B → Y
  map-codomain-cartesian-hom-arrow =
    map-codomain-hom-arrow f g hom-arrow-cartesian-hom-arrow

  coh-cartesian-hom-arrow :
    coherence-square-maps
      ( map-domain-cartesian-hom-arrow)
      ( f)
      ( g)
      ( map-codomain-cartesian-hom-arrow)
  coh-cartesian-hom-arrow =
    coh-hom-arrow f g hom-arrow-cartesian-hom-arrow

  cone-cartesian-hom-arrow :
    cone map-codomain-cartesian-hom-arrow g A
  cone-cartesian-hom-arrow =
    cone-hom-arrow f g hom-arrow-cartesian-hom-arrow

  universal-property-cartesian-hom-arrow :
    universal-property-pullback
      ( map-codomain-cartesian-hom-arrow)
      ( g)
      ( cone-cartesian-hom-arrow)
  universal-property-cartesian-hom-arrow =
    universal-property-pullback-is-pullback
      ( map-codomain-cartesian-hom-arrow)
      ( g)
      ( cone-cartesian-hom-arrow)
      ( is-cartesian-cartesian-hom-arrow)
```

## Operations

### The identity cartesian morphism of arrows

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  id-cartesian-hom-arrow : cartesian-hom-arrow f f
  id-cartesian-hom-arrow =
    ( id-hom-arrow ,
      is-pullback-is-equiv-horizontal-maps id f
        ( f , id , refl-htpy)
        ( is-equiv-id)
        ( is-equiv-id))
```

### Composition of cartesian morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V) (b : hom-arrow g h) (a : hom-arrow f g)
  where

  is-cartesian-comp-hom-arrow :
    is-cartesian-hom-arrow g h b →
    is-cartesian-hom-arrow f g a →
    is-cartesian-hom-arrow f h (comp-hom-arrow f g h b a)
  is-cartesian-comp-hom-arrow =
    is-pullback-rectangle-is-pullback-left-square
      ( map-codomain-hom-arrow f g a)
      ( map-codomain-hom-arrow g h b)
      ( h)
      ( cone-hom-arrow g h b)
      ( cone-hom-arrow f g a)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (b : cartesian-hom-arrow g h) (a : cartesian-hom-arrow f g)
  where

  comp-cartesian-hom-arrow : cartesian-hom-arrow f h
  comp-cartesian-hom-arrow =
    ( ( comp-hom-arrow f g h
        ( hom-arrow-cartesian-hom-arrow g h b)
        ( hom-arrow-cartesian-hom-arrow f g a)) ,
      ( is-cartesian-comp-hom-arrow f g h
        ( hom-arrow-cartesian-hom-arrow g h b)
        ( hom-arrow-cartesian-hom-arrow f g a)
        ( is-cartesian-cartesian-hom-arrow g h b)
        ( is-cartesian-cartesian-hom-arrow f g a)))
```

### Left cancellation of cartesian morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V) (b : hom-arrow g h) (a : hom-arrow f g)
  where

  is-cartesian-right-factor-hom-arrow :
    is-cartesian-hom-arrow g h b →
    is-cartesian-hom-arrow f h (comp-hom-arrow f g h b a) →
    is-cartesian-hom-arrow f g a
  is-cartesian-right-factor-hom-arrow =
    is-pullback-left-square-is-pullback-rectangle
      ( map-codomain-hom-arrow f g a)
      ( map-codomain-hom-arrow g h b)
      ( h)
      ( cone-hom-arrow g h b)
      ( cone-hom-arrow f g a)
```

### Cartesian morphisms of arrows arising from fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (y : B)
  where

  fiber-cartesian-hom-arrow :
    cartesian-hom-arrow (terminal-map (fiber f y)) f
  pr1 fiber-cartesian-hom-arrow =
    hom-arrow-cone (point y) f (swap-cone f (point y) (cone-fiber f y))
  pr2 fiber-cartesian-hom-arrow =
    is-pullback-swap-cone f (point y)
      ( cone-fiber f y)
      ( is-pullback-cone-fiber f y)
```

### Transposing cartesian morphisms of arrows

The {{#concept "transposition" Disambiguation="cartesian morphism of arrows"}}
of a cartesian morphism of arrows

```text
        i
    A -----> X
    | ⌟      |
  f |        | g
    V        V
    B -----> Y
        j
```

is the cartesian morphism of arrows

```text
        f
    A -----> B
    | ⌟      |
  i |        | j
    V        V
    X -----> Y.
        g
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : cartesian-hom-arrow f g)
  where

  is-cartesian-transpose-cartesian-hom-arrow :
    is-cartesian-hom-arrow
      ( map-domain-cartesian-hom-arrow f g α)
      ( map-codomain-cartesian-hom-arrow f g α)
      ( transpose-hom-arrow f g (hom-arrow-cartesian-hom-arrow f g α))
  is-cartesian-transpose-cartesian-hom-arrow =
    is-pullback-swap-cone
      ( map-codomain-cartesian-hom-arrow f g α)
      ( g)
      ( cone-cartesian-hom-arrow f g α)
      ( is-cartesian-cartesian-hom-arrow f g α)

  transpose-cartesian-hom-arrow :
    cartesian-hom-arrow
      ( map-domain-cartesian-hom-arrow f g α)
      ( map-codomain-cartesian-hom-arrow f g α)
  transpose-cartesian-hom-arrow =
    ( transpose-hom-arrow f g (hom-arrow-cartesian-hom-arrow f g α) ,
      is-cartesian-transpose-cartesian-hom-arrow)
```

## Properties

### Cartesian morphisms of arrows are preserved under homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  abstract
    is-cartesian-cartesian-hom-arrow-htpy :
      {f f' : A → B} (F' : f' ~ f) {g g' : X → Y} (G : g ~ g') →
      (α : hom-arrow f g) →
      is-cartesian-hom-arrow f g α →
      is-cartesian-hom-arrow f' g' (hom-arrow-htpy F' G α)
    is-cartesian-cartesian-hom-arrow-htpy {f} F' {g} G α =
      is-pullback-htpy
        ( refl-htpy)
        ( inv-htpy G)
        ( cone-hom-arrow f g α)
        ( ( F') ,
          ( refl-htpy) ,
          ( ( assoc-htpy
              ( map-codomain-hom-arrow f g α ·l F' ∙h coh-hom-arrow f g α)
              ( G ·r map-domain-hom-arrow f g α)
              ( inv-htpy (G ·r map-domain-hom-arrow f g α))) ∙h
            ( ap-concat-htpy
              ( map-codomain-hom-arrow f g α ·l F' ∙h coh-hom-arrow f g α)
              ( right-inv-htpy G ·r map-domain-hom-arrow f g α)) ∙h
            ( right-unit-htpy) ∙h
            ( ap-concat-htpy' (coh-hom-arrow f g α) inv-htpy-right-unit-htpy)))

  cartesian-hom-arrow-htpy :
    {f f' : A → B} (F' : f' ~ f) {g g' : X → Y} (G : g ~ g') →
    cartesian-hom-arrow f g → cartesian-hom-arrow f' g'
  cartesian-hom-arrow-htpy F' G (α , H) =
    ( hom-arrow-htpy F' G α , is-cartesian-cartesian-hom-arrow-htpy F' G α H)
```

### If the target of a cartesian morphism is an equivalence then so is the source

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : cartesian-hom-arrow f g)
  where

  is-equiv-source-is-equiv-target-cartesian-hom-arrow : is-equiv g → is-equiv f
  is-equiv-source-is-equiv-target-cartesian-hom-arrow G =
    is-equiv-vertical-map-is-pullback
      ( map-codomain-cartesian-hom-arrow f g α)
      ( g)
      ( cone-cartesian-hom-arrow f g α)
      ( G)
      ( is-cartesian-cartesian-hom-arrow f g α)
```

### If the target and source of a morphism of arrows are equivalences then the morphism is cartesian

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  is-cartesian-hom-arrow-is-equiv-source-is-equiv-target :
    is-equiv g → is-equiv f → is-cartesian-hom-arrow f g α
  is-cartesian-hom-arrow-is-equiv-source-is-equiv-target =
    is-pullback-is-equiv-vertical-maps
      ( map-codomain-hom-arrow f g α)
      ( g)
      ( cone-hom-arrow f g α)
```

## See also

- [Cocartesian morphisms of arrows](synthetic-homotopy-theory.cocartesian-morphisms-arrows.md)
  for the dual.
