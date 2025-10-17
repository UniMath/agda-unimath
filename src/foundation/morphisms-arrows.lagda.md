# Morphisms of arrows

```agda
module foundation.morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
```

</details>

## Idea

A {{#concept "morphism of arrows" Agda=hom-arrow}} from a function `f : A → B`
to a function `g : X → Y` is a [triple](foundation.dependent-pair-types.md)
`(i , j , H)` consisting of maps `i : A → X` and `j : B → Y` and a
[homotopy](foundation-core.homotopies.md) `H : j ∘ f ~ g ∘ i` witnessing that
the square

```text
        i
    A -----> X
    |        |
  f |        | g
    ∨        ∨
    B -----> Y
        j
```

[commutes](foundation-core.commuting-squares-of-maps.md). Morphisms of arrows
can be composed horizontally or vertically by pasting of squares.

## Definitions

### Morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  coherence-hom-arrow : (A → X) → (B → Y) → UU (l1 ⊔ l4)
  coherence-hom-arrow i = coherence-square-maps i f g

  hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-arrow = Σ (A → X) (λ i → Σ (B → Y) (coherence-hom-arrow i))

  map-domain-hom-arrow : hom-arrow → A → X
  map-domain-hom-arrow = pr1

  map-codomain-hom-arrow : hom-arrow → B → Y
  map-codomain-hom-arrow = pr1 ∘ pr2

  coh-hom-arrow :
    (h : hom-arrow) →
    coherence-hom-arrow (map-domain-hom-arrow h) (map-codomain-hom-arrow h)
  coh-hom-arrow = pr2 ∘ pr2
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  coherence-hom-arrow' : (A → X) → (B → Y) → UU (l1 ⊔ l4)
  coherence-hom-arrow' i = coherence-square-maps' i f g

  hom-arrow' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-arrow' = Σ (A → X) (λ i → Σ (B → Y) (coherence-hom-arrow' i))

  map-domain-hom-arrow' : hom-arrow' → A → X
  map-domain-hom-arrow' = pr1

  map-codomain-hom-arrow' : hom-arrow' → B → Y
  map-codomain-hom-arrow' = pr1 ∘ pr2

  coh-hom-arrow' :
    (h : hom-arrow') →
    coherence-hom-arrow' (map-domain-hom-arrow' h) (map-codomain-hom-arrow' h)
  coh-hom-arrow' = pr2 ∘ pr2

  equiv-hom-arrow-hom-arrow' : hom-arrow' ≃ hom-arrow f g
  equiv-hom-arrow-hom-arrow' =
    equiv-tot (λ i → equiv-tot (λ j → equiv-inv-htpy (g ∘ i) (j ∘ f)))

  equiv-hom-arrow'-hom-arrow : hom-arrow f g ≃ hom-arrow'
  equiv-hom-arrow'-hom-arrow =
    equiv-tot (λ i → equiv-tot (λ j → equiv-inv-htpy (j ∘ f) (g ∘ i)))

  hom-arrow-hom-arrow' : hom-arrow' → hom-arrow f g
  hom-arrow-hom-arrow' = map-equiv equiv-hom-arrow-hom-arrow'

  hom-arrow'-hom-arrow : hom-arrow f g → hom-arrow'
  hom-arrow'-hom-arrow = map-equiv equiv-hom-arrow'-hom-arrow
```

## Operations

### The identity morphism of arrows

The identity morphism of arrows is defined as

```text
        id
    A -----> A
    |        |
  f |        | f
    ∨        ∨
    B -----> B
        id
```

where the homotopy `id ∘ f ~ f ∘ id` is the reflexivity homotopy.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  id-hom-arrow' : (f : A → B) → hom-arrow f f
  id-hom-arrow' f = (id , id , refl-htpy)

  id-hom-arrow : {f : A → B} → hom-arrow f f
  id-hom-arrow {f} = id-hom-arrow' f
```

### Composition of morphisms of arrows

Consider a commuting diagram of the form

```text
        α₀       β₀
    A -----> X -----> U
    |        |        |
  f |   α  g |   β    | h
    ∨        ∨        ∨
    B -----> Y -----> V.
        α₁       β₁
```

Then the outer rectangle commutes by horizontal pasting of commuting squares of
maps. The {{#concept "composition" Disambiguation="morphism of arrows"}} of
`β : g → h` with `α : f → g` is therefore defined to be

```text
        β₀ ∘ α₀
    A ----------> U
    |             |
  f |    α □ β    | h
    ∨             ∨
    B ----------> V.
        β₁ ∘ α₁
```

**Note.** Associativity and the unit laws for composition of morphisms of arrows
are proven in
[Homotopies of morphisms of arrows](foundation.homotopies-morphisms-arrows.md).

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V) (b : hom-arrow g h) (a : hom-arrow f g)
  where

  map-domain-comp-hom-arrow : A → U
  map-domain-comp-hom-arrow =
    map-domain-hom-arrow g h b ∘ map-domain-hom-arrow f g a

  map-codomain-comp-hom-arrow : B → V
  map-codomain-comp-hom-arrow =
    map-codomain-hom-arrow g h b ∘ map-codomain-hom-arrow f g a

  coh-comp-hom-arrow :
    coherence-hom-arrow f h
      ( map-domain-comp-hom-arrow)
      ( map-codomain-comp-hom-arrow)
  coh-comp-hom-arrow =
    pasting-horizontal-coherence-square-maps
      ( map-domain-hom-arrow f g a)
      ( map-domain-hom-arrow g h b)
      ( f)
      ( g)
      ( h)
      ( map-codomain-hom-arrow f g a)
      ( map-codomain-hom-arrow g h b)
      ( coh-hom-arrow f g a)
      ( coh-hom-arrow g h b)

  comp-hom-arrow : hom-arrow f h
  comp-hom-arrow =
    ( map-domain-comp-hom-arrow ,
      map-codomain-comp-hom-arrow ,
      coh-comp-hom-arrow)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V) (b : hom-arrow' g h) (a : hom-arrow' f g)
  where

  map-domain-comp-hom-arrow' : A → U
  map-domain-comp-hom-arrow' =
    map-domain-hom-arrow' g h b ∘ map-domain-hom-arrow' f g a

  map-codomain-comp-hom-arrow' : B → V
  map-codomain-comp-hom-arrow' =
    map-codomain-hom-arrow' g h b ∘ map-codomain-hom-arrow' f g a

  coh-comp-hom-arrow' :
    coherence-hom-arrow' f h
      ( map-domain-comp-hom-arrow')
      ( map-codomain-comp-hom-arrow')
  coh-comp-hom-arrow' =
    pasting-horizontal-coherence-square-maps'
      ( map-domain-hom-arrow' f g a)
      ( map-domain-hom-arrow' g h b)
      ( f)
      ( g)
      ( h)
      ( map-codomain-hom-arrow' f g a)
      ( map-codomain-hom-arrow' g h b)
      ( coh-hom-arrow' f g a)
      ( coh-hom-arrow' g h b)

  comp-hom-arrow' : hom-arrow' f h
  comp-hom-arrow' =
    ( map-domain-comp-hom-arrow' ,
      map-codomain-comp-hom-arrow' ,
      coh-comp-hom-arrow')
```

### Transposing morphisms of arrows

The {{#concept "transposition" Disambiguation="morphism of arrows"}} of a
morphism of arrows

```text
        i
    A -----> X
    |        |
  f |        | g
    ∨        ∨
    B -----> Y
        j
```

is the morphism of arrows

```text
        f
    A -----> B
    |        |
  i |        | j
    ∨        ∨
    X -----> Y.
        g
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  map-domain-transpose-hom-arrow : A → B
  map-domain-transpose-hom-arrow = f

  map-codomain-transpose-hom-arrow : X → Y
  map-codomain-transpose-hom-arrow = g

  coh-transpose-hom-arrow :
    coherence-hom-arrow
      ( map-domain-hom-arrow f g α)
      ( map-codomain-hom-arrow f g α)
      ( map-domain-transpose-hom-arrow)
      ( map-codomain-transpose-hom-arrow)
  coh-transpose-hom-arrow =
    inv-htpy (coh-hom-arrow f g α)

  transpose-hom-arrow :
    hom-arrow (map-domain-hom-arrow f g α) (map-codomain-hom-arrow f g α)
  pr1 transpose-hom-arrow = map-domain-transpose-hom-arrow
  pr1 (pr2 transpose-hom-arrow) = map-codomain-transpose-hom-arrow
  pr2 (pr2 transpose-hom-arrow) = coh-transpose-hom-arrow
```

### Morphisms of arrows obtained from cones over cospans

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  hom-arrow-cone : hom-arrow (vertical-map-cone f g c) g
  pr1 hom-arrow-cone = horizontal-map-cone f g c
  pr1 (pr2 hom-arrow-cone) = f
  pr2 (pr2 hom-arrow-cone) = coherence-square-cone f g c

  hom-arrow-cone' : hom-arrow (horizontal-map-cone f g c) f
  hom-arrow-cone' =
    transpose-hom-arrow (vertical-map-cone f g c) g hom-arrow-cone
```

### Cones over cospans obtained from morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  cone-hom-arrow : cone (map-codomain-hom-arrow f g h) g A
  pr1 cone-hom-arrow = f
  pr1 (pr2 cone-hom-arrow) = map-domain-hom-arrow f g h
  pr2 (pr2 cone-hom-arrow) = coh-hom-arrow f g h
```

### Morphisms of arrows are preserved under homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  hom-arrow-htpy-source :
    {f f' : A → B} (F' : f' ~ f) (g : X → Y) →
    hom-arrow f g → hom-arrow f' g
  hom-arrow-htpy-source F' g (i , j , H) = (i , j , (j ·l F') ∙h H)

  hom-arrow-htpy-target :
    (f : A → B) {g g' : X → Y} (G : g ~ g') →
    hom-arrow f g → hom-arrow f g'
  hom-arrow-htpy-target f G (i , j , H) = (i , j , H ∙h (G ·r i))

  hom-arrow-htpy :
    {f f' : A → B} (F' : f' ~ f) {g g' : X → Y} (G : g ~ g') →
    hom-arrow f g → hom-arrow f' g'
  hom-arrow-htpy F' G (i , j , H) = (i , j , (j ·l F') ∙h H ∙h (G ·r i))
```

### Dependent products of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l5} {A : I → UU l1} {B : I → UU l2} {X : I → UU l3} {Y : I → UU l4}
  (f : (i : I) → A i → B i) (g : (i : I) → X i → Y i)
  (α : (i : I) → hom-arrow (f i) (g i))
  where

  Π-hom-arrow : hom-arrow (map-Π f) (map-Π g)
  pr1 Π-hom-arrow =
    map-Π (λ i → map-domain-hom-arrow (f i) (g i) (α i))
  pr1 (pr2 Π-hom-arrow) =
    map-Π (λ i → map-codomain-hom-arrow (f i) (g i) (α i))
  pr2 (pr2 Π-hom-arrow) =
    htpy-map-Π (λ i → coh-hom-arrow (f i) (g i) (α i))
```

### Morphisms of arrows give morphisms of precomposition arrows

A morphism of arrows `α : f → g` gives a morphism of precomposition arrows
`(-)^α : (–)^g → (–)^f`.

```agda
module _
  {l1 l2 l3 l4 l : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  (S : UU l)
  where

  transpose-precomp-hom-arrow :
    hom-arrow
      ( precomp (map-codomain-hom-arrow f g α) S)
      ( precomp (map-domain-hom-arrow f g α) S)
  transpose-precomp-hom-arrow =
    ( precomp g S , precomp f S , htpy-precomp (coh-hom-arrow f g α) S)

  precomp-hom-arrow : hom-arrow (precomp g S) (precomp f S)
  precomp-hom-arrow =
    transpose-hom-arrow
      ( precomp (map-codomain-hom-arrow f g α) S)
      ( precomp (map-domain-hom-arrow f g α) S)
      ( transpose-precomp-hom-arrow)
```

### Morphisms of arrows give morphisms of postcomposition arrows

A morphism of arrows `α : f → g` gives a morphism of postcomposition arrows
`α^(-) : f^(-) → g^(-)`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  postcomp-hom-arrow :
    {l : Level} (S : UU l) → hom-arrow (postcomp S f) (postcomp S g)
  postcomp-hom-arrow S =
    ( postcomp S (map-domain-hom-arrow f g α) ,
      postcomp S (map-codomain-hom-arrow f g α) ,
      htpy-postcomp S (coh-hom-arrow f g α))
```

## See also

- [Equivalences of arrows](foundation.equivalences-arrows.md)
- [Morphisms of twisted arrows](foundation.morphisms-twisted-arrows.md).
- [Fibered maps](foundation.fibered-maps.md) for the same concept under a
  different name.
- [The pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is an
  operation that returns a morphism of arrows from a diagonal map.
- [Homotopies of morphisms of arrows](foundation.homotopies-morphisms-arrows.md)
