# Morphisms of arrows

```agda
module foundation.morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **morphism of arrows** from a function `f : A → B` to a function `g : X → Y`
is a triple `(i , j , H)` consisting of maps `i : A → X` and `j : B → Y` and a
[homotopy](foundation-core.homotopies.md) `H : j ∘ f ~ g ∘ i` witnessing that
the square

```text
        i
    A -----> X
    |        |
  f |        | g
    V        V
    B -----> Y
        j
```

[commutes](foundation-core.commuting-squares-of-maps.md). Morphisms of arrows
can be composed horizontally or vertically by pasting of squares.

## Definitions

### Morphisms of arrows

```agda
record hom-arrow
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) :
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  field
    map-domain-hom-arrow : A → X
    map-codomain-hom-arrow : B → Y
    coh-hom-arrow :
      coherence-square-maps
        ( map-domain-hom-arrow)
        ( f)
        ( g)
        ( map-codomain-hom-arrow)

open hom-arrow public
```

### Transposing morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (α : hom-arrow f g)
  where

  transpose-hom-arrow :
    hom-arrow (map-domain-hom-arrow α) (map-codomain-hom-arrow α)
  map-domain-hom-arrow transpose-hom-arrow = f
  map-codomain-hom-arrow transpose-hom-arrow = g
  coh-hom-arrow transpose-hom-arrow = inv-htpy (coh-hom-arrow α)
```

### The identity morphism of arrows

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  id-hom-arrow : hom-arrow f f
  id-hom-arrow .map-domain-hom-arrow = id
  id-hom-arrow .map-codomain-hom-arrow = id
  id-hom-arrow .coh-hom-arrow = refl-htpy
```

### Composition of morphisms of arrows

Consider a commuting diagram of the form

```text
        α₀       β₀
    A -----> X -----> U
    |        |        |
  f |   α  g |   β    | h
    V        V        V
    B -----> Y -----> V.
        α₁       β₁
```

Then the outer rectangle commutes by horizontal pasting of commuting squares of
maps.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  {f : A → B} {g : X → Y} {h : U → V} (β : hom-arrow g h) (α : hom-arrow f g)
  where

  map-domain-comp-hom-arrow : A → U
  map-domain-comp-hom-arrow =
    map-domain-hom-arrow β ∘ map-domain-hom-arrow α

  map-codomain-comp-hom-arrow : B → V
  map-codomain-comp-hom-arrow =
    map-codomain-hom-arrow β ∘ map-codomain-hom-arrow α

  coh-comp-hom-arrow :
    coherence-square-maps
      ( map-domain-comp-hom-arrow)
      ( f)
      ( h)
      ( map-codomain-comp-hom-arrow)
  coh-comp-hom-arrow =
    pasting-horizontal-coherence-square-maps
      ( map-domain-hom-arrow α)
      ( map-domain-hom-arrow β)
      ( f)
      ( g)
      ( h)
      ( map-codomain-hom-arrow α)
      ( map-codomain-hom-arrow β)
      ( coh-hom-arrow α)
      ( coh-hom-arrow β)

  comp-hom-arrow : hom-arrow f h
  comp-hom-arrow .map-domain-hom-arrow = map-domain-comp-hom-arrow
  comp-hom-arrow .map-codomain-hom-arrow = map-codomain-comp-hom-arrow
  comp-hom-arrow .coh-hom-arrow = coh-comp-hom-arrow
```

### Homotopies of morphsims of arrows

A **homotopy of morphisms of arrows** from `(i , j , H)` to `(i' , j' , H')` is
a triple `(I , J , K)` consisting of homotopies `I : i ~ i'` and `J : j ~ j'`
and a homotopy `K` witnessing that the
[square of homotopies](foundation.commuting-squares-of-homotopies.md)

```text
           J ·r f
  (j ∘ f) --------> (j' ∘ f)
     |                 |
   H |                 | H'
     V                 V
  (g ∘ i) --------> (g ∘ i')
           g ·l I
```

commutes.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (α : hom-arrow f g)
  where

  coherence-htpy-hom-arrow :
    (β : hom-arrow f g)
    (I : map-domain-hom-arrow α ~ map-domain-hom-arrow β)
    (J : map-codomain-hom-arrow α ~ map-codomain-hom-arrow β) →
    UU (l1 ⊔ l4)
  coherence-htpy-hom-arrow β I J =
    coherence-square-homotopies
      ( J ·r f)
      ( coh-hom-arrow α)
      ( coh-hom-arrow β)
      ( g ·l I)

  htpy-hom-arrow :
    (β : hom-arrow f g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-arrow β =
    Σ ( map-domain-hom-arrow α ~ map-domain-hom-arrow β)
      ( λ I →
        Σ ( map-codomain-hom-arrow α ~ map-codomain-hom-arrow β)
          ( coherence-htpy-hom-arrow β I))

  module _
    (β : hom-arrow f g) (η : htpy-hom-arrow β)
    where

    htpy-domain-htpy-hom-arrow :
      map-domain-hom-arrow α ~ map-domain-hom-arrow β
    htpy-domain-htpy-hom-arrow = pr1 η

    htpy-codomain-htpy-hom-arrow :
      map-codomain-hom-arrow α ~ map-codomain-hom-arrow β
    htpy-codomain-htpy-hom-arrow = pr1 (pr2 η)

    coh-htpy-hom-arrow :
      coherence-square-homotopies
        ( htpy-codomain-htpy-hom-arrow ·r f)
        ( coh-hom-arrow α)
        ( coh-hom-arrow β)
        ( g ·l htpy-domain-htpy-hom-arrow)
    coh-htpy-hom-arrow = pr2 (pr2 η)

  refl-htpy-hom-arrow : htpy-hom-arrow α
  pr1 refl-htpy-hom-arrow = refl-htpy
  pr1 (pr2 refl-htpy-hom-arrow) = refl-htpy
  pr2 (pr2 refl-htpy-hom-arrow) = right-unit-htpy

  -- is-torsorial-htpy-hom-arrow : is-torsorial htpy-hom-arrow
  -- is-torsorial-htpy-hom-arrow =
    -- is-torsorial-Eq-structure
    --   ( λ i jH I → Σ _ _)
    --   ( is-torsorial-htpy (map-domain-hom-arrow α))
    --   ( map-domain-hom-arrow α , refl-htpy)
    --   ( is-torsorial-Eq-structure
    --     ( λ j H J → _)
    --     ( is-torsorial-htpy (map-codomain-hom-arrow α))
    --     ( map-codomain-hom-arrow α , refl-htpy)
    --     ( is-torsorial-htpy (coh-hom-arrow α ∙h refl-htpy)))

  -- htpy-eq-hom-arrow : (β : hom-arrow f g) → (α ＝ β) → htpy-hom-arrow β
  -- htpy-eq-hom-arrow β refl = refl-htpy-hom-arrow

  -- is-equiv-htpy-eq-hom-arrow :
  --   (β : hom-arrow f g) → is-equiv (htpy-eq-hom-arrow β)
  -- is-equiv-htpy-eq-hom-arrow =
  --   fundamental-theorem-id is-torsorial-htpy-hom-arrow htpy-eq-hom-arrow

  -- extensionality-hom-arrow :
  --   (β : hom-arrow f g) → (α ＝ β) ≃ htpy-hom-arrow β
  -- pr1 (extensionality-hom-arrow β) = htpy-eq-hom-arrow β
  -- pr2 (extensionality-hom-arrow β) = is-equiv-htpy-eq-hom-arrow β

  -- eq-htpy-hom-arrow :
  --   (β : hom-arrow f g) → htpy-hom-arrow β → α ＝ β
  -- eq-htpy-hom-arrow β = map-inv-equiv (extensionality-hom-arrow β)
```

### Concatenation of homotopies of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (α β γ : hom-arrow f g)
  (H : htpy-hom-arrow α β) (K : htpy-hom-arrow β γ)
  where

  htpy-domain-concat-htpy-hom-arrow :
    map-domain-hom-arrow α ~ map-domain-hom-arrow γ
  htpy-domain-concat-htpy-hom-arrow =
    htpy-domain-htpy-hom-arrow α β H ∙h
    htpy-domain-htpy-hom-arrow β γ K

  htpy-codomain-concat-htpy-hom-arrow :
    map-codomain-hom-arrow α ~ map-codomain-hom-arrow γ
  htpy-codomain-concat-htpy-hom-arrow =
    htpy-codomain-htpy-hom-arrow α β H ∙h
    htpy-codomain-htpy-hom-arrow β γ K

  coh-concat-htpy-hom-arrow :
    coherence-htpy-hom-arrow α γ
      ( htpy-domain-concat-htpy-hom-arrow)
      ( htpy-codomain-concat-htpy-hom-arrow)
  coh-concat-htpy-hom-arrow a =
    ( ap
      ( concat (coh-hom-arrow α a) (g (map-domain-hom-arrow γ a)))
      ( ap-concat g
        ( htpy-domain-htpy-hom-arrow α β H a)
        ( htpy-domain-htpy-hom-arrow β γ K a))) ∙
    ( coherence-square-identifications-comp-horizontal
      ( coh-hom-arrow α a)
      ( coh-hom-arrow β a)
      ( coh-hom-arrow γ a)
      ( coh-htpy-hom-arrow α β H a)
      ( coh-htpy-hom-arrow β γ K a))

  concat-htpy-hom-arrow : htpy-hom-arrow α γ
  pr1 concat-htpy-hom-arrow = htpy-domain-concat-htpy-hom-arrow
  pr1 (pr2 concat-htpy-hom-arrow) = htpy-codomain-concat-htpy-hom-arrow
  pr2 (pr2 concat-htpy-hom-arrow) = coh-concat-htpy-hom-arrow
```

### Inverses of homotopies of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (α β : hom-arrow f g) (H : htpy-hom-arrow α β)
  where

  htpy-domain-inv-htpy-hom-arrow :
    map-domain-hom-arrow β ~ map-domain-hom-arrow α
  htpy-domain-inv-htpy-hom-arrow =
    inv-htpy (htpy-domain-htpy-hom-arrow α β H)

  htpy-codomain-inv-htpy-hom-arrow :
    map-codomain-hom-arrow β ~ map-codomain-hom-arrow α
  htpy-codomain-inv-htpy-hom-arrow =
    inv-htpy (htpy-codomain-htpy-hom-arrow α β H)

  coh-inv-htpy-hom-arrow :
    coherence-htpy-hom-arrow β α
      ( htpy-domain-inv-htpy-hom-arrow)
      ( htpy-codomain-inv-htpy-hom-arrow)
  coh-inv-htpy-hom-arrow a =
    ( ap
      ( concat (coh-hom-arrow β a) (g (map-domain-hom-arrow α a)))
      ( ap-inv g (htpy-domain-htpy-hom-arrow α β H a))) ∙
    ( double-transpose-eq-concat'
      ( coh-hom-arrow α a)
      ( htpy-codomain-htpy-hom-arrow α β H (f a))
      ( ap g (htpy-domain-htpy-hom-arrow α β H a))
      ( coh-hom-arrow β a)
      ( inv (coh-htpy-hom-arrow α β H a)))

  inv-htpy-hom-arrow : htpy-hom-arrow β α
  pr1 inv-htpy-hom-arrow = htpy-domain-inv-htpy-hom-arrow
  pr1 (pr2 inv-htpy-hom-arrow) = htpy-codomain-inv-htpy-hom-arrow
  pr2 (pr2 inv-htpy-hom-arrow) = coh-inv-htpy-hom-arrow
```

### Whiskering of homotopies of morphisms of arrows

#### Left whiskering

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  {f : A → B} {g : X → Y} {h : U → V}
  (γ : hom-arrow g h) (α β : hom-arrow f g) (H : htpy-hom-arrow α β)
  where

  htpy-domain-left-whisker-htpy-hom-arrow :
    map-domain-comp-hom-arrow γ α ~ map-domain-comp-hom-arrow γ β
  htpy-domain-left-whisker-htpy-hom-arrow =
    map-domain-hom-arrow γ ·l htpy-domain-htpy-hom-arrow α β H

  htpy-codomain-left-whisker-htpy-hom-arrow :
    map-codomain-comp-hom-arrow γ α ~ map-codomain-comp-hom-arrow γ β
  htpy-codomain-left-whisker-htpy-hom-arrow =
    map-codomain-hom-arrow γ ·l htpy-codomain-htpy-hom-arrow α β H

  coh-left-whisker-htpy-hom-arrow :
    coherence-htpy-hom-arrow
      ( comp-hom-arrow γ α)
      ( comp-hom-arrow γ β)
      ( htpy-domain-left-whisker-htpy-hom-arrow)
      ( htpy-codomain-left-whisker-htpy-hom-arrow)
  coh-left-whisker-htpy-hom-arrow a =
    ( inv
      ( ap
        ( concat _ _)
        ( ap-comp h
          ( map-domain-hom-arrow γ)
          ( htpy-domain-htpy-hom-arrow α β H x)))) ∙
    ( assoc
      ( ap (map-codomain-hom-arrow γ) (coh-hom-arrow α x))
      ( coh-hom-arrow γ (map-domain-hom-arrow α x))
      ( ap
        ( h ∘ map-domain-hom-arrow γ)
        ( htpy-domain-htpy-hom-arrow α β H x))) ∙
    ( ap
      ( concat
        ( ap (map-codomain-hom-arrow γ) (coh-hom-arrow α x))
        ( h (map-domain-hom-arrow γ (map-domain-hom-arrow β x))))
      ( nat-htpy
        ( coh-hom-arrow γ)
        ( htpy-domain-htpy-hom-arrow α β H x))) ∙
    ( inv
      ( assoc
        ( ap (map-codomain-hom-arrow γ) (coh-hom-arrow α x))
        ( ap
          ( map-codomain-hom-arrow γ ∘ g)
          ( htpy-domain-htpy-hom-arrow α β H x))
        ( coh-hom-arrow γ (map-domain-hom-arrow β x)))) ∙
    ( ap
      ( concat' _ (coh-hom-arrow γ (map-domain-hom-arrow β x)))
      ( ( ap
          ( concat
            ( ap (map-codomain-hom-arrow γ) (coh-hom-arrow α x))
            ( map-codomain-hom-arrow γ (g (map-domain-hom-arrow β x))))
          ( ap-comp
            ( map-codomain-hom-arrow γ)
            ( g)
            ( htpy-domain-htpy-hom-arrow α β H x))) ∙
        ( inv
          ( ap-concat
            ( map-codomain-hom-arrow γ)
            ( coh-hom-arrow α x)
            ( ap g (htpy-domain-htpy-hom-arrow α β H x)))) ∙
        ( ap
          ( ap (map-codomain-hom-arrow γ))
          ( coh-htpy-hom-arrow α β H x)) ∙
        ( ap-concat
          ( map-codomain-hom-arrow γ)
          ( htpy-codomain-htpy-hom-arrow α β H (f x))
          ( coh-hom-arrow β x)))) ∙
    ( assoc
      ( ap
        ( map-codomain-hom-arrow γ)
        ( htpy-codomain-htpy-hom-arrow α β H (f x)))
      ( ap (map-codomain-hom-arrow γ) (coh-hom-arrow β x))
      ( coh-hom-arrow γ (map-domain-hom-arrow β x)))

  left-whisker-htpy-hom-arrow :
    htpy-hom-arrow
      ( comp-hom-arrow γ α)
      ( comp-hom-arrow γ β)
  pr1 left-whisker-htpy-hom-arrow =
    htpy-domain-left-whisker-htpy-hom-arrow
  pr1 (pr2 left-whisker-htpy-hom-arrow) =
    htpy-codomain-left-whisker-htpy-hom-arrow
  pr2 (pr2 left-whisker-htpy-hom-arrow) =
    coh-left-whisker-htpy-hom-arrow
```

#### Right whiskering

Exercise for Fredrik.

### Associativity of composition of morphisms of arrows

Consider a commuting diagram of the form

```text
        α₀       β₀       γ₀
    A -----> X -----> U -----> K
    |        |        |        |
  f |   α  g |   β  h |   γ    | i
    V        V        V        V
    B -----> Y -----> V -----> L
        α₁       β₁       γ₁
```

Then associativity of composition of morphisms of arrows follows directly from
associativity of horizontal pasting of commutative squares of maps.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  {K : UU l7} {L : UU l8} {f : A → B} {g : X → Y} {h : U → V} {i : K → L}
  (γ : hom-arrow h i) (β : hom-arrow g h) (α : hom-arrow f g)
  where

  assoc-comp-hom-arrow :
    htpy-hom-arrow
      ( comp-hom-arrow (comp-hom-arrow γ β) α)
      ( comp-hom-arrow γ (comp-hom-arrow β α))
  pr1 assoc-comp-hom-arrow = refl-htpy
  pr1 (pr2 assoc-comp-hom-arrow) = refl-htpy
  pr2 (pr2 assoc-comp-hom-arrow) =
    ( right-unit-htpy) ∙h
    ( inv-htpy
      ( assoc-pasting-horizontal-coherence-square-maps
        ( map-domain-hom-arrow α)
        ( map-domain-hom-arrow β)
        ( map-domain-hom-arrow γ)
        ( f)
        ( g)
        ( h)
        ( i)
        ( map-codomain-hom-arrow α)
        ( map-codomain-hom-arrow β)
        ( map-codomain-hom-arrow γ)
        ( coh-hom-arrow α)
        ( coh-hom-arrow β)
        ( coh-hom-arrow γ)))

  inv-assoc-comp-hom-arrow :
    htpy-hom-arrow
      ( comp-hom-arrow γ (comp-hom-arrow β α))
      ( comp-hom-arrow (comp-hom-arrow γ β) α)
  pr1 inv-assoc-comp-hom-arrow = refl-htpy
  pr1 (pr2 inv-assoc-comp-hom-arrow) = refl-htpy
  pr2 (pr2 inv-assoc-comp-hom-arrow) =
    ( right-unit-htpy) ∙h
    ( assoc-pasting-horizontal-coherence-square-maps
      ( map-domain-hom-arrow α)
      ( map-domain-hom-arrow β)
      ( map-domain-hom-arrow γ)
      ( f)
      ( g)
      ( h)
      ( i)
      ( map-codomain-hom-arrow α)
      ( map-codomain-hom-arrow β)
      ( map-codomain-hom-arrow γ)
      ( coh-hom-arrow α)
      ( coh-hom-arrow β)
      ( coh-hom-arrow γ))
```

### The left unit law for composition of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (α : hom-arrow f g)
  where

  left-unit-law-comp-hom-arrow :
    htpy-hom-arrow (comp-hom-arrow id-hom-arrow α) α
  pr1 left-unit-law-comp-hom-arrow = refl-htpy
  pr1 (pr2 left-unit-law-comp-hom-arrow) = refl-htpy
  pr2 (pr2 left-unit-law-comp-hom-arrow) =
    ( right-unit-htpy) ∙h
    ( right-unit-law-pasting-horizontal-coherence-square-maps
      ( map-domain-hom-arrow α)
      ( f)
      ( g)
      ( map-codomain-hom-arrow α)
      ( coh-hom-arrow α))
```

### The right unit law for composition of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (α : hom-arrow f g)
  where

  right-unit-law-comp-hom-arrow :
    htpy-hom-arrow (comp-hom-arrow α id-hom-arrow) α
  pr1 right-unit-law-comp-hom-arrow = refl-htpy
  pr1 (pr2 right-unit-law-comp-hom-arrow) = refl-htpy
  pr2 (pr2 right-unit-law-comp-hom-arrow) = right-unit-htpy
```

## See also

- [Morphisms of twisted arrows](foundation.morphisms-twisted-arrows.md).
