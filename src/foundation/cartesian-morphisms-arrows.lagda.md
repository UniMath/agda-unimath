# Cartesian morphisms of arrows

```agda
module foundation.cartesian-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.commuting-triangles-of-morphisms-arrows
open import foundation.cones-over-cospan-diagrams
open import foundation.coproducts-pullbacks
open import foundation.dependent-pair-types
open import foundation.dependent-products-pullbacks
open import foundation.dependent-sums-pullbacks
open import foundation.transport-along-identifications
open import foundation.diagonal-maps-cartesian-products-of-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fibers-of-maps
open import foundation.contractible-types
open import foundation.torsorial-type-families
open import foundation.homotopies
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies-morphisms-arrows
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.postcomposition-pullbacks
open import foundation.products-pullbacks
open import foundation.pullbacks
open import foundation.standard-pullbacks
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
    ∨        ∨
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

## Properties

### Cartesian morphisms of arrows arising from standard pullbacks

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  standard-pullback-cartesian-hom-arrow :
    cartesian-hom-arrow vertical-map-standard-pullback g
  standard-pullback-cartesian-hom-arrow =
    ( hom-arrow-cone f g (cone-standard-pullback f g) , is-equiv-id)
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

### The induced family of equivalences of fibers of cartesian morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : cartesian-hom-arrow f g)
  where

  equiv-fibers-cartesian-hom-arrow :
    (b : B) → fiber f b ≃ fiber g (map-codomain-cartesian-hom-arrow f g h b)
  equiv-fibers-cartesian-hom-arrow b =
    ( map-fiber-vertical-map-cone
      ( map-codomain-cartesian-hom-arrow f g h)
      ( g)
      ( cone-cartesian-hom-arrow f g h)
      ( b)) ,
    ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
      ( map-codomain-cartesian-hom-arrow f g h)
      ( g)
      ( cone-cartesian-hom-arrow f g h)
      ( is-cartesian-cartesian-hom-arrow f g h)
      ( b))
```

### Transposing cartesian morphisms of arrows

The {{#concept "transposition" Disambiguation="cartesian morphism of arrows"}}
of a cartesian morphism of arrows

```text
        i
    A -----> X
    | ⌟      |
  f |        | g
    ∨        ∨
    B -----> Y
        j
```

is the cartesian morphism of arrows

```text
        f
    A -----> B
    | ⌟      |
  i |        | j
    ∨        ∨
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

### If the transpose is cartesian then so is the original

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  is-cartesian-is-cartesian-transpose-cartesian-hom-arrow :
    is-cartesian-hom-arrow
      ( map-domain-hom-arrow f g α)
      ( map-codomain-hom-arrow f g α)
      ( transpose-hom-arrow f g α) →
    is-cartesian-hom-arrow f g α
  is-cartesian-is-cartesian-transpose-cartesian-hom-arrow =
    is-pullback-swap-cone'
      ( map-codomain-hom-arrow f g α)
      ( g)
      ( cone-hom-arrow f g α)
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

### Cartesian morphisms of arrows are preserved under homotopies of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  abstract
    is-cartesian-hom-arrow-htpy :
      {f f' : A → B} (F' : f' ~ f) {g g' : X → Y} (G : g ~ g')
      (α : hom-arrow f g) →
      is-cartesian-hom-arrow f g α →
      is-cartesian-hom-arrow f' g' (hom-arrow-htpy F' G α)
    is-cartesian-hom-arrow-htpy {f} F' {g} G α =
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
    ( hom-arrow-htpy F' G α , is-cartesian-hom-arrow-htpy F' G α H)
```

### Cartesian morphisms of arrows are preserved under homotopies of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  abstract
    is-cartesian-htpy-hom-arrow :
      (α β : hom-arrow f g)
      (H : htpy-hom-arrow f g β α) →
      is-cartesian-hom-arrow f g α →
      is-cartesian-hom-arrow f g β
    is-cartesian-htpy-hom-arrow α β H =
      is-pullback-htpy
        ( htpy-codomain-htpy-hom-arrow f g β α H)
        ( refl-htpy)
        ( cone-hom-arrow f g α)
        ( htpy-parallell-cone-htpy-hom-arrow f g β α H)
```

### The identity cartesian morphism of arrows

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-cartesian-id-hom-arrow : is-cartesian-hom-arrow f f id-hom-arrow
  is-cartesian-id-hom-arrow =
    is-pullback-is-equiv-horizontal-maps id f
      ( f , id , refl-htpy)
      ( is-equiv-id)
      ( is-equiv-id)

  id-cartesian-hom-arrow : cartesian-hom-arrow f f
  id-cartesian-hom-arrow = (id-hom-arrow , is-cartesian-id-hom-arrow)
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

  is-cartesian-hom-arrow-right-factor :
    is-cartesian-hom-arrow g h b →
    is-cartesian-hom-arrow f h (comp-hom-arrow f g h b a) →
    is-cartesian-hom-arrow f g a
  is-cartesian-hom-arrow-right-factor =
    is-pullback-left-square-is-pullback-rectangle
      ( map-codomain-hom-arrow f g a)
      ( map-codomain-hom-arrow g h b)
      ( h)
      ( cone-hom-arrow g h b)
      ( cone-hom-arrow f g a)
```

### The left morphism in a commuting triangle of morphisms of arrows is cartesian if the other two are

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (left : hom-arrow f h) (right : hom-arrow g h) (top : hom-arrow f g)
  (H : coherence-triangle-hom-arrow f g h left right top)
  where

  abstract
    is-cartesian-left-hom-arrow-triangle :
      is-cartesian-hom-arrow g h right →
      is-cartesian-hom-arrow f g top →
      is-cartesian-hom-arrow f h left
    is-cartesian-left-hom-arrow-triangle R T =
      is-cartesian-htpy-hom-arrow f h
        ( comp-hom-arrow f g h right top)
        ( left)
        ( H)
        ( is-cartesian-comp-hom-arrow f g h right top R T)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (top : cartesian-hom-arrow f g)
  (left : hom-arrow f h)
  (right : cartesian-hom-arrow g h)
  (H :
    coherence-triangle-hom-arrow f g h
      ( left)
      ( hom-arrow-cartesian-hom-arrow g h right)
      ( hom-arrow-cartesian-hom-arrow f g top))
  where

  abstract
    is-cartesian-left-cartesian-hom-arrow-triangle :
      is-cartesian-hom-arrow f h left
    is-cartesian-left-cartesian-hom-arrow-triangle =
      is-cartesian-left-hom-arrow-triangle f g h
        ( left)
        ( hom-arrow-cartesian-hom-arrow g h right)
        ( hom-arrow-cartesian-hom-arrow f g top)
        ( H)
        ( is-cartesian-cartesian-hom-arrow g h right)
        ( is-cartesian-cartesian-hom-arrow f g top)
```

### The top morphism in a commuting triangle of morphisms of arrows is cartesian if the other two are

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (left : hom-arrow f h) (right : hom-arrow g h) (top : hom-arrow f g)
  where

  abstract
    is-cartesian-top-hom-arrow-triangle' :
      (H : coherence-triangle-hom-arrow' f g h left right top) →
      is-cartesian-hom-arrow g h right →
      is-cartesian-hom-arrow f h left →
      is-cartesian-hom-arrow f g top
    is-cartesian-top-hom-arrow-triangle' H R L =
      is-cartesian-hom-arrow-right-factor f g h right top R
        ( is-cartesian-htpy-hom-arrow f h
          ( left)
          ( comp-hom-arrow f g h right top)
          ( H)
          ( L))

  abstract
    is-cartesian-top-hom-arrow-triangle :
      (H : coherence-triangle-hom-arrow f g h left right top) →
      is-cartesian-hom-arrow g h right →
      is-cartesian-hom-arrow f h left →
      is-cartesian-hom-arrow f g top
    is-cartesian-top-hom-arrow-triangle H =
      is-cartesian-top-hom-arrow-triangle'
        ( inv-htpy-hom-arrow f h left (comp-hom-arrow f g h right top) H)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (top : hom-arrow f g)
  (left : cartesian-hom-arrow f h)
  (right : cartesian-hom-arrow g h)
  where

  abstract
    is-cartesian-top-cartesian-hom-arrow-triangle' :
      (H :
        coherence-triangle-hom-arrow' f g h
          ( hom-arrow-cartesian-hom-arrow f h left)
          ( hom-arrow-cartesian-hom-arrow g h right)
          ( top)) →
      is-cartesian-hom-arrow f g top
    is-cartesian-top-cartesian-hom-arrow-triangle' H =
      is-cartesian-top-hom-arrow-triangle' f g h
        ( hom-arrow-cartesian-hom-arrow f h left)
        ( hom-arrow-cartesian-hom-arrow g h right)
        ( top)
        ( H)
        ( is-cartesian-cartesian-hom-arrow g h right)
        ( is-cartesian-cartesian-hom-arrow f h left)

  abstract
    is-cartesian-top-cartesian-hom-arrow-triangle :
      (H :
        coherence-triangle-hom-arrow f g h
          ( hom-arrow-cartesian-hom-arrow f h left)
          ( hom-arrow-cartesian-hom-arrow g h right)
          ( top)) →
      is-cartesian-hom-arrow f g top
    is-cartesian-top-cartesian-hom-arrow-triangle H =
      is-cartesian-top-hom-arrow-triangle f g h
        ( hom-arrow-cartesian-hom-arrow f h left)
        ( hom-arrow-cartesian-hom-arrow g h right)
        ( top)
        ( H)
        ( is-cartesian-cartesian-hom-arrow g h right)
        ( is-cartesian-cartesian-hom-arrow f h left)
```

### Dependent products of cartesian morphisms of arrows

Given a family of cartesian morphisms of arrows `αᵢ : fᵢ → gᵢ`, then there is a
cartesian morphism of arrows `map-Π f → map-Π g`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l5} {A : I → UU l1} {B : I → UU l2} {X : I → UU l3} {Y : I → UU l4}
  (f : (i : I) → A i → B i) (g : (i : I) → X i → Y i)
  (α : (i : I) → cartesian-hom-arrow (f i) (g i))
  where

  hom-arrow-Π-cartesian-hom-arrow :
    hom-arrow (map-Π f) (map-Π g)
  hom-arrow-Π-cartesian-hom-arrow =
    Π-hom-arrow f g (λ i → hom-arrow-cartesian-hom-arrow (f i) (g i) (α i))

  is-cartesian-Π-cartesian-hom-arrow :
    is-cartesian-hom-arrow (map-Π f) (map-Π g) hom-arrow-Π-cartesian-hom-arrow
  is-cartesian-Π-cartesian-hom-arrow =
    is-pullback-Π
      ( λ i → map-codomain-cartesian-hom-arrow (f i) (g i) (α i))
      ( g)
      ( λ i → cone-cartesian-hom-arrow (f i) (g i) (α i))
      ( λ i → is-cartesian-cartesian-hom-arrow (f i) (g i) (α i))

  Π-cartesian-hom-arrow :
    cartesian-hom-arrow (map-Π f) (map-Π g)
  pr1 Π-cartesian-hom-arrow = hom-arrow-Π-cartesian-hom-arrow
  pr2 Π-cartesian-hom-arrow = is-cartesian-Π-cartesian-hom-arrow
```

### Dependent sums of cartesian morphisms of arrows

Given a family of cartesian morphisms of arrows `αᵢ : fᵢ → gᵢ`, then there is a
cartesian morphism of arrows `tot f → tot g`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l5} {A : I → UU l1} {B : I → UU l2} {X : I → UU l3} {Y : I → UU l4}
  (f : (i : I) → A i → B i) (g : (i : I) → X i → Y i)
  (α : (i : I) → cartesian-hom-arrow (f i) (g i))
  where

  hom-arrow-tot-cartesian-hom-arrow :
    hom-arrow (tot f) (tot g)
  hom-arrow-tot-cartesian-hom-arrow =
    tot-hom-arrow f g (λ i → hom-arrow-cartesian-hom-arrow (f i) (g i) (α i))

  is-cartesian-tot-cartesian-hom-arrow :
    is-cartesian-hom-arrow (tot f) (tot g) hom-arrow-tot-cartesian-hom-arrow
  is-cartesian-tot-cartesian-hom-arrow =
    is-pullback-tot-is-pullback-family-id-cone
      ( λ i → map-codomain-cartesian-hom-arrow (f i) (g i) (α i))
      ( g)
      ( λ i → cone-cartesian-hom-arrow (f i) (g i) (α i))
      ( λ i → is-cartesian-cartesian-hom-arrow (f i) (g i) (α i))

  tot-cartesian-hom-arrow :
    cartesian-hom-arrow (tot f) (tot g)
  pr1 tot-cartesian-hom-arrow = hom-arrow-tot-cartesian-hom-arrow
  pr2 tot-cartesian-hom-arrow = is-cartesian-tot-cartesian-hom-arrow
```

### Cartesian morphisms of arrows are preserved under products

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {C : UU l5} {D : UU l6} {Z : UU l7} {W : UU l8}
  (f : A → B) (g : X → Y) (h : C → D) (i : Z → W)
  (α : cartesian-hom-arrow f g) (β : cartesian-hom-arrow h i)
  where

  is-cartesian-product-cartesian-hom-arrow :
    is-cartesian-hom-arrow
      ( map-product f h)
      ( map-product g i)
      ( product-hom-arrow f g h i
        ( hom-arrow-cartesian-hom-arrow f g α)
        ( hom-arrow-cartesian-hom-arrow h i β))
  is-cartesian-product-cartesian-hom-arrow =
    is-pullback-product-is-pullback
      ( map-codomain-hom-arrow f g (hom-arrow-cartesian-hom-arrow f g α))
      ( g)
      ( map-codomain-hom-arrow h i (hom-arrow-cartesian-hom-arrow h i β))
      ( i)
      ( cone-cartesian-hom-arrow f g α)
      ( cone-cartesian-hom-arrow h i β)
      ( is-cartesian-cartesian-hom-arrow f g α)
      ( is-cartesian-cartesian-hom-arrow h i β)

  product-cartesian-hom-arrow :
    cartesian-hom-arrow (map-product f h) (map-product g i)
  product-cartesian-hom-arrow =
    ( ( product-hom-arrow f g h i
        ( hom-arrow-cartesian-hom-arrow f g α)
        ( hom-arrow-cartesian-hom-arrow h i β)) ,
      ( is-cartesian-product-cartesian-hom-arrow))
```

### Cartesian morphisms of arrows are preserved under coproducts

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {C : UU l5} {D : UU l6} {Z : UU l7} {W : UU l8}
  (f : A → B) (g : X → Y) (h : C → D) (i : Z → W)
  (α : cartesian-hom-arrow f g) (β : cartesian-hom-arrow h i)
  where

  is-cartesian-coproduct-cartesian-hom-arrow :
    is-cartesian-hom-arrow
      ( map-coproduct f h)
      ( map-coproduct g i)
      ( coproduct-hom-arrow f g h i
        ( hom-arrow-cartesian-hom-arrow f g α)
        ( hom-arrow-cartesian-hom-arrow h i β))
  is-cartesian-coproduct-cartesian-hom-arrow =
    is-pullback-coproduct-is-pullback
      ( map-codomain-hom-arrow f g (hom-arrow-cartesian-hom-arrow f g α))
      ( g)
      ( map-codomain-hom-arrow h i (hom-arrow-cartesian-hom-arrow h i β))
      ( i)
      ( cone-cartesian-hom-arrow f g α)
      ( cone-cartesian-hom-arrow h i β)
      ( is-cartesian-cartesian-hom-arrow f g α)
      ( is-cartesian-cartesian-hom-arrow h i β)

  coproduct-cartesian-hom-arrow :
    cartesian-hom-arrow (map-coproduct f h) (map-coproduct g i)
  coproduct-cartesian-hom-arrow =
    ( ( coproduct-hom-arrow f g h i
        ( hom-arrow-cartesian-hom-arrow f g α)
        ( hom-arrow-cartesian-hom-arrow h i β)) ,
      ( is-cartesian-coproduct-cartesian-hom-arrow))
```

### Cartesian morphisms of arrows are preserved under postcomposition exponentiation

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : cartesian-hom-arrow f g) (S : UU l5)
  where

  hom-arrow-postcomp-cartesian-hom-arrow :
    hom-arrow (postcomp S f) (postcomp S g)
  hom-arrow-postcomp-cartesian-hom-arrow =
    postcomp-hom-arrow f g (hom-arrow-cartesian-hom-arrow f g α) S

  is-cartesian-postcomp-cartesian-hom-arrow :
    is-cartesian-hom-arrow
      ( postcomp S f)
      ( postcomp S g)
      ( hom-arrow-postcomp-cartesian-hom-arrow)
  is-cartesian-postcomp-cartesian-hom-arrow =
    is-pullback-postcomp-is-pullback
      ( map-codomain-cartesian-hom-arrow f g α)
      ( g)
      ( cone-cartesian-hom-arrow f g α)
      ( is-cartesian-cartesian-hom-arrow f g α)
      ( S)

  postcomp-cartesian-hom-arrow :
    cartesian-hom-arrow (postcomp S f) (postcomp S g)
  pr1 postcomp-cartesian-hom-arrow =
    hom-arrow-postcomp-cartesian-hom-arrow
  pr2 postcomp-cartesian-hom-arrow = is-cartesian-postcomp-cartesian-hom-arrow
```

### A folding operation on cartesian morphisms of arrows

A morphism of arrows

```text
         i
    A ------> X
    |         |
  f |         | g
    ∨         ∨
    B ------> Y
         j
```

is cartesian if and only if either of the folded morphisms

```text
          (f , i)                       (f , i)
        A ------> B × X               A ------> B × X
        |           |                 |           |
  g ∘ i |           | j × g     j ∘ f |           | j × g
        ∨           ∨                 ∨           ∨
        Y ------> Y × Y               Y ------> Y × Y
             Δ                             Δ
```

is cartesian.

> It remains to formalize the right-hand version.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  (α : hom-arrow f g)
  where

  transpose-fold-hom-arrow :
    hom-arrow
      ( λ x → (f x , map-domain-hom-arrow f g α x))
      ( diagonal-product Y)
  transpose-fold-hom-arrow =
    hom-arrow-cone
      ( map-product (map-codomain-hom-arrow f g α) g)
      ( diagonal-product Y)
      ( fold-cone (map-codomain-hom-arrow f g α) g (cone-hom-arrow f g α))

  fold-hom-arrow :
    hom-arrow
      ( g ∘ map-domain-hom-arrow f g α)
      ( map-product (map-codomain-hom-arrow f g α) g)
  fold-hom-arrow =
    transpose-hom-arrow
      ( λ a → f a , map-domain-hom-arrow f g α a)
      ( diagonal-product Y)
      ( transpose-fold-hom-arrow)

  is-cartesian-transpose-fold-hom-arrow :
    is-cartesian-hom-arrow f g α →
    is-cartesian-hom-arrow
      ( λ x → (f x , map-domain-hom-arrow f g α x))
      ( diagonal-product Y)
      ( transpose-fold-hom-arrow)
  is-cartesian-transpose-fold-hom-arrow =
    is-pullback-fold-cone-is-pullback
      ( map-codomain-hom-arrow f g α)
      ( g)
      ( cone-hom-arrow f g α)

  is-cartesian-is-cartesian-transpose-fold-hom-arrow :
    is-cartesian-hom-arrow
      ( λ x → (f x , map-domain-hom-arrow f g α x))
      ( diagonal-product Y)
      ( transpose-fold-hom-arrow) →
    is-cartesian-hom-arrow f g α
  is-cartesian-is-cartesian-transpose-fold-hom-arrow =
    is-pullback-is-pullback-fold-cone
      ( map-codomain-hom-arrow f g α)
      ( g)
      ( cone-hom-arrow f g α)

  is-cartesian-fold-hom-arrow :
    is-cartesian-hom-arrow f g α →
    is-cartesian-hom-arrow
      ( g ∘ map-domain-hom-arrow f g α)
      ( map-product (map-codomain-hom-arrow f g α) g)
      ( fold-hom-arrow)
  is-cartesian-fold-hom-arrow H =
    is-cartesian-transpose-cartesian-hom-arrow
      ( λ x → (f x , map-domain-hom-arrow f g α x))
      ( diagonal-product Y)
      ( transpose-fold-hom-arrow , is-cartesian-transpose-fold-hom-arrow H)

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  (α : cartesian-hom-arrow f g)
  where

  transpose-fold-cartesian-hom-arrow :
    cartesian-hom-arrow
      ( λ x → (f x , map-domain-cartesian-hom-arrow f g α x))
      ( diagonal-product Y)
  pr1 transpose-fold-cartesian-hom-arrow =
    transpose-fold-hom-arrow f g (hom-arrow-cartesian-hom-arrow f g α)
  pr2 transpose-fold-cartesian-hom-arrow =
    is-cartesian-transpose-fold-hom-arrow f g
      ( hom-arrow-cartesian-hom-arrow f g α)
      ( is-cartesian-cartesian-hom-arrow f g α)

  fold-cartesian-hom-arrow :
    cartesian-hom-arrow
      ( g ∘ map-domain-cartesian-hom-arrow f g α)
      ( map-product (map-codomain-cartesian-hom-arrow f g α) g)
  pr1 fold-cartesian-hom-arrow =
    fold-hom-arrow f g (hom-arrow-cartesian-hom-arrow f g α)
  pr2 fold-cartesian-hom-arrow =
    is-cartesian-fold-hom-arrow f g
      ( hom-arrow-cartesian-hom-arrow f g α)
      ( is-cartesian-cartesian-hom-arrow f g α)
```

### Lifting cartesian morphisms along lifts of the codomain

Suppose given a cospan diagram of arrows

```text
    A ------> C <------ B
    |         |       ⌞ |
  f |    α    h    β    | g
    ∨         ∨         ∨
    A' -----> C' <----- B'
```

where `β` is cartesian. Moreover, suppose we have a map `i : A' → B'` from the
codomain of the source of `α` to the codomain of the source of `β` such that the
triangle

```text
         i
     A' ---> B'
      \     /
       \   /
        ∨ ∨
         C'
```

commutes. Then there is a unique morphism of arrows `γ : f → g` with a homotopy
`β ~ α ∘ γ` extending the triangle, and this morphism is cartesian if and only
if `α` is.

**Proof.** The unique existence of `γ` and the homotopy follows from the
pullback property of `β`. The rest is a reiteration of the 3-for-2 property of
cartesian morphisms. ∎

We begin by constructing the commuting triangle of morphisms of arrows:

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (β : cartesian-hom-arrow g h)
  (α : hom-arrow f h)
  (i : A' → B')
  (H :
    coherence-triangle-maps'
      ( map-codomain-hom-arrow f h α)
      ( map-codomain-cartesian-hom-arrow g h β)
      ( i))
  where

  cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
    cone (map-codomain-cartesian-hom-arrow g h β) h A
  cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    ( i ∘ f , map-domain-hom-arrow f h α , H ·r f ∙h coh-hom-arrow f h α)

  map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow : A → B
  map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    gap-is-pullback
      ( map-codomain-cartesian-hom-arrow g h β)
      ( h)
      ( cone-cartesian-hom-arrow g h β)
      ( is-cartesian-cartesian-hom-arrow g h β)
      ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)

  hom-arrow-lift-map-codomain-cartesian-hom-arrow : hom-arrow f g
  pr1 hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow
  pr1 (pr2 hom-arrow-lift-map-codomain-cartesian-hom-arrow) = i
  pr2 (pr2 hom-arrow-lift-map-codomain-cartesian-hom-arrow) =
    inv-htpy
      ( htpy-vertical-map-gap-is-pullback
        ( map-codomain-cartesian-hom-arrow g h β)
        ( h)
        ( cone-cartesian-hom-arrow g h β)
        ( is-cartesian-cartesian-hom-arrow g h β)
        ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow))

  abstract
    inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
      coherence-triangle-hom-arrow' f g h
        ( α)
        ( hom-arrow-cartesian-hom-arrow g h β)
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrow)
    inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
      ( htpy-horizontal-map-gap-is-pullback
          ( map-codomain-cartesian-hom-arrow g h β)
          ( h)
          ( cone-cartesian-hom-arrow g h β)
          ( is-cartesian-cartesian-hom-arrow g h β)
          ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)) ,
      ( H) ,
      ( ( ap-concat-htpy'
          ( ( h) ·l
            ( htpy-horizontal-map-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( pr2 β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))
          ( ap-concat-htpy'
            ( coh-cartesian-hom-arrow g h β ·r
              map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow)
            ( left-whisker-inv-htpy
              ( map-codomain-cartesian-hom-arrow g h β)
              ( htpy-vertical-map-gap-is-pullback
                ( map-codomain-cartesian-hom-arrow g h β)
                ( h)
                ( cone-cartesian-hom-arrow g h β)
                ( pr2 β)
                ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow))))) ∙h
        ( assoc-htpy
          ( inv-htpy
            ( ( map-codomain-cartesian-hom-arrow g h β) ·l
              ( htpy-vertical-map-gap-is-pullback
                ( map-codomain-cartesian-hom-arrow g h β)
                ( h)
                ( cone-cartesian-hom-arrow g h β)
                ( pr2 β)
                ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow))))
          ( coh-cartesian-hom-arrow g h β ·r
            map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow)
          ( ( h) ·l
            ( htpy-horizontal-map-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( pr2 β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))) ∙h
        ( inv-htpy-left-transpose-htpy-concat
          ( ( map-codomain-cartesian-hom-arrow g h β) ·l
            ( htpy-vertical-map-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( pr2 β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))
          ( H ·r f ∙h coh-hom-arrow f h α)
          ( ( coh-cartesian-hom-arrow g h β ·r
              map-domain-hom-arrow-lift-map-codomain-cartesian-hom-arrow) ∙h
            ( h) ·l
            ( htpy-horizontal-map-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( is-cartesian-cartesian-hom-arrow g h β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))
          ( inv-htpy
            ( coh-htpy-cone-gap-is-pullback
              ( map-codomain-cartesian-hom-arrow g h β)
              ( h)
              ( cone-cartesian-hom-arrow g h β)
              ( is-cartesian-cartesian-hom-arrow g h β)
              ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow)))))

  coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
    coherence-triangle-hom-arrow f g h
      ( α)
      ( hom-arrow-cartesian-hom-arrow g h β)
      ( hom-arrow-lift-map-codomain-cartesian-hom-arrow)
  coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    inv-htpy-hom-arrow f h
      ( comp-hom-arrow f g h
        ( hom-arrow-cartesian-hom-arrow g h β)
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrow))
      ( α)
      ( inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow)
```

This lift is unique.

<!-- The following uniqueness proof also constructs an explicit lift, making the entire formalization above almost entirely useless -->

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (β : cartesian-hom-arrow g h)
  (α : hom-arrow f h)
  (i : A' → B')
  (H :
    coherence-triangle-maps'
      ( map-codomain-hom-arrow f h α)
      ( map-codomain-cartesian-hom-arrow g h β)
      ( i))
  where

  abstract
    uniqueness-lift-map-codomain-cartesian-hom-arrow :
      is-torsorial
        ( λ (j : A → B) →
          Σ ( coherence-hom-arrow f g j i)
            ( λ J →
              Σ ( coherence-triangle-maps'
                  ( map-domain-hom-arrow f h α)
                  ( map-domain-cartesian-hom-arrow g h β)
                  ( j))
                ( λ K →
                  coherence-htpy-hom-arrow f h
                    ( comp-hom-arrow f g h
                      ( hom-arrow-cartesian-hom-arrow g h β)
                      ( j , i , J))
                    ( α)
                    ( K)
                    ( H))))
    uniqueness-lift-map-codomain-cartesian-hom-arrow =
      is-contr-equiv _
        ( equiv-tot
          ( λ j →
            equiv-Σ _
              ( equiv-inv-htpy (i ∘ f) (g ∘ j))
              ( λ J →
                equiv-tot
                  ( λ K →
                    equivalence-reasoning
                    ( ( map-codomain-cartesian-hom-arrow g h β ·l J) ∙h
                      ( coh-cartesian-hom-arrow g h β ·r j) ∙h
                      ( h ·l K) ~
                      ( H ·r f) ∙h
                      ( coh-hom-arrow f h α))
                    ≃ ( ( map-codomain-cartesian-hom-arrow g h β ·l J) ∙h
                        ( ( coh-cartesian-hom-arrow g h β ·r j) ∙h
                          ( h ·l K)) ~
                        ( H ·r f) ∙h
                        ( coh-hom-arrow f h α))
                      by
                        equiv-tr
                          ( λ Q → Q ~ ( H ·r f) ∙h ( coh-hom-arrow f h α))
                          ( eq-htpy
                            ( assoc-htpy
                              ( map-codomain-cartesian-hom-arrow g h β ·l J)
                              ( coh-cartesian-hom-arrow g h β ·r j)
                              ( h ·l K)))
                    ≃ ( ( coh-cartesian-hom-arrow g h β ·r j) ∙h (h ·l K) ~
                        ( inv-htpy
                          ( map-codomain-cartesian-hom-arrow g h β ·l J)) ∙h
                        ( ( H ·r f) ∙h (coh-hom-arrow f h α)))
                      by
                        equiv-left-transpose-htpy-concat
                          ( map-codomain-cartesian-hom-arrow g h β ·l J)
                          ( ( coh-cartesian-hom-arrow g h β ·r j) ∙h (h ·l K))
                          ( ( H ·r f) ∙h (coh-hom-arrow f h α))
                    ≃ ( ( coh-cartesian-hom-arrow g h β ·r j) ∙h (h ·l K) ~
                        ( ( map-codomain-cartesian-hom-arrow g h β) ·l
                          ( inv-htpy J)) ∙h
                        ( ( H ·r f) ∙h (coh-hom-arrow f h α)))
                      by
                        equiv-tr
                          ( λ Q →
                            (coh-cartesian-hom-arrow g h β ·r j) ∙h (h ·l K) ~
                            Q ∙h ((H ·r f) ∙h (coh-hom-arrow f h α)))
                          ( inv
                            ( eq-htpy
                              ( left-whisker-inv-htpy
                                ( map-codomain-cartesian-hom-arrow g h β)
                                ( J))))))))
        ( uniqueness-universal-property-pullback
          ( map-codomain-cartesian-hom-arrow g h β)
          ( h)
          ( cone-cartesian-hom-arrow g h β)
          ( universal-property-cartesian-hom-arrow g h β)
          ( A)
          ( cone-hom-arrow-lift-map-codomain-cartesian-hom-arrow f g h β α i H))
```

Now, if `α` was cartesian to begin with, the lift is also.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (β : cartesian-hom-arrow g h)
  (α : cartesian-hom-arrow f h)
  (i : A' → B')
  (H :
    coherence-triangle-maps'
      ( map-codomain-cartesian-hom-arrow f h α)
      ( map-codomain-cartesian-hom-arrow g h β)
      ( i))
  where

  abstract
    is-cartesian-cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
      is-cartesian-hom-arrow f g
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrow f g h
          ( β)
          ( hom-arrow-cartesian-hom-arrow f h α)
          ( i)
          ( H))
    is-cartesian-cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
      is-cartesian-top-cartesian-hom-arrow-triangle' f g h
        ( hom-arrow-lift-map-codomain-cartesian-hom-arrow f g h
          ( β)
          ( hom-arrow-cartesian-hom-arrow f h α)
          ( i)
          ( H))
        ( α)
        ( β)
        ( inv-coherence-triangle-hom-arrow-lift-map-codomain-cartesian-hom-arrow
          ( f) g h β (hom-arrow-cartesian-hom-arrow f h α) i H)

  cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow :
    cartesian-hom-arrow f g
  cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow =
    ( hom-arrow-lift-map-codomain-cartesian-hom-arrow
      ( f) g h β (hom-arrow-cartesian-hom-arrow f h α) i H) ,
    ( is-cartesian-cartesian-hom-arrow-lift-map-codomain-cartesian-hom-arrow)
```

## See also

- [Cocartesian morphisms of arrows](synthetic-homotopy-theory.cocartesian-morphisms-arrows.md)
  for the dual.
- [Diagonals of morphisms of arrows](foundation.diagonals-of-morphisms-arrows.md)
  is another operation that preserves cartesianness.
