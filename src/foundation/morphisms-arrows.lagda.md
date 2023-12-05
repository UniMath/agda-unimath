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
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-arrow = Σ (A → X) (λ i → Σ (B → Y) (coherence-square-maps i f g))

  map-domain-hom-arrow : hom-arrow → A → X
  map-domain-hom-arrow = pr1

  map-codomain-hom-arrow : hom-arrow → B → Y
  map-codomain-hom-arrow = pr1 ∘ pr2

  coh-hom-arrow :
    (h : hom-arrow) →
    coherence-square-maps
      ( map-domain-hom-arrow h)
      ( f)
      ( g)
      ( map-codomain-hom-arrow h)
  coh-hom-arrow = pr2 ∘ pr2
```

### Transposing morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  transpose-hom-arrow :
    hom-arrow (map-domain-hom-arrow f g α) (map-codomain-hom-arrow f g α)
  pr1 transpose-hom-arrow = f
  pr1 (pr2 transpose-hom-arrow) = g
  pr2 (pr2 transpose-hom-arrow) = inv-htpy (coh-hom-arrow f g α)
```

### The identity morphism of arrows

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  id-hom-arrow : hom-arrow f f
  pr1 id-hom-arrow = id
  pr1 (pr2 id-hom-arrow) = id
  pr2 (pr2 id-hom-arrow) = refl-htpy
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
  (f : A → B) (g : X → Y) (h : U → V) (b : hom-arrow g h) (a : hom-arrow f g)
  where

  map-domain-comp-hom-arrow : A → U
  map-domain-comp-hom-arrow =
    map-domain-hom-arrow g h b ∘ map-domain-hom-arrow f g a

  map-codomain-comp-hom-arrow : B → V
  map-codomain-comp-hom-arrow =
    map-codomain-hom-arrow g h b ∘ map-codomain-hom-arrow f g a

  coh-comp-hom-arrow :
    coherence-square-maps
      ( map-domain-comp-hom-arrow)
      ( f)
      ( h)
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
  pr1 comp-hom-arrow =
    map-domain-comp-hom-arrow
  pr1 (pr2 comp-hom-arrow) =
    map-codomain-comp-hom-arrow
  pr2 (pr2 comp-hom-arrow) =
    coh-comp-hom-arrow
```

### Homotopies of morphisms of arrows

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
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  coherence-htpy-hom-arrow :
    (β : hom-arrow f g)
    (I : map-domain-hom-arrow f g α ~ map-domain-hom-arrow f g β)
    (J : map-codomain-hom-arrow f g α ~ map-codomain-hom-arrow f g β) →
    UU (l1 ⊔ l4)
  coherence-htpy-hom-arrow β I J =
    coherence-square-homotopies
      ( J ·r f)
      ( coh-hom-arrow f g α)
      ( coh-hom-arrow f g β)
      ( g ·l I)

  htpy-hom-arrow :
    (β : hom-arrow f g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-arrow β =
    Σ ( map-domain-hom-arrow f g α ~ map-domain-hom-arrow f g β)
      ( λ I →
        Σ ( map-codomain-hom-arrow f g α ~ map-codomain-hom-arrow f g β)
          ( coherence-htpy-hom-arrow β I))

  module _
    (β : hom-arrow f g) (η : htpy-hom-arrow β)
    where

    htpy-domain-htpy-hom-arrow :
      map-domain-hom-arrow f g α ~ map-domain-hom-arrow f g β
    htpy-domain-htpy-hom-arrow = pr1 η

    htpy-codomain-htpy-hom-arrow :
      map-codomain-hom-arrow f g α ~ map-codomain-hom-arrow f g β
    htpy-codomain-htpy-hom-arrow = pr1 (pr2 η)

    coh-htpy-hom-arrow :
      coherence-square-homotopies
        ( htpy-codomain-htpy-hom-arrow ·r f)
        ( coh-hom-arrow f g α)
        ( coh-hom-arrow f g β)
        ( g ·l htpy-domain-htpy-hom-arrow)
    coh-htpy-hom-arrow = pr2 (pr2 η)

  refl-htpy-hom-arrow : htpy-hom-arrow α
  pr1 refl-htpy-hom-arrow = refl-htpy
  pr1 (pr2 refl-htpy-hom-arrow) = refl-htpy
  pr2 (pr2 refl-htpy-hom-arrow) = right-unit-htpy

  is-torsorial-htpy-hom-arrow :
    is-torsorial htpy-hom-arrow
  is-torsorial-htpy-hom-arrow =
    is-torsorial-Eq-structure
      ( λ i jH I → Σ _ _)
      ( is-torsorial-htpy (map-domain-hom-arrow f g α))
      ( map-domain-hom-arrow f g α , refl-htpy)
      ( is-torsorial-Eq-structure
        ( λ j H J → _)
        ( is-torsorial-htpy (map-codomain-hom-arrow f g α))
        ( map-codomain-hom-arrow f g α , refl-htpy)
        ( is-torsorial-htpy (coh-hom-arrow f g α ∙h refl-htpy)))

  htpy-eq-hom-arrow : (β : hom-arrow f g) → (α ＝ β) → htpy-hom-arrow β
  htpy-eq-hom-arrow β refl = refl-htpy-hom-arrow

  is-equiv-htpy-eq-hom-arrow :
    (β : hom-arrow f g) → is-equiv (htpy-eq-hom-arrow β)
  is-equiv-htpy-eq-hom-arrow =
    fundamental-theorem-id is-torsorial-htpy-hom-arrow htpy-eq-hom-arrow

  extensionality-hom-arrow :
    (β : hom-arrow f g) → (α ＝ β) ≃ htpy-hom-arrow β
  pr1 (extensionality-hom-arrow β) = htpy-eq-hom-arrow β
  pr2 (extensionality-hom-arrow β) = is-equiv-htpy-eq-hom-arrow β

  eq-htpy-hom-arrow :
    (β : hom-arrow f g) → htpy-hom-arrow β → α ＝ β
  eq-htpy-hom-arrow β = map-inv-equiv (extensionality-hom-arrow β)
```

### Concatenation of homotopies of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α β γ : hom-arrow f g)
  (H : htpy-hom-arrow f g α β) (K : htpy-hom-arrow f g β γ)
  where

  htpy-domain-concat-htpy-hom-arrow :
    map-domain-hom-arrow f g α ~ map-domain-hom-arrow f g γ
  htpy-domain-concat-htpy-hom-arrow =
    htpy-domain-htpy-hom-arrow f g α β H ∙h
    htpy-domain-htpy-hom-arrow f g β γ K

  htpy-codomain-concat-htpy-hom-arrow :
    map-codomain-hom-arrow f g α ~ map-codomain-hom-arrow f g γ
  htpy-codomain-concat-htpy-hom-arrow =
    htpy-codomain-htpy-hom-arrow f g α β H ∙h
    htpy-codomain-htpy-hom-arrow f g β γ K

  coh-concat-htpy-hom-arrow :
    coherence-htpy-hom-arrow f g α γ
      ( htpy-domain-concat-htpy-hom-arrow)
      ( htpy-codomain-concat-htpy-hom-arrow)
  coh-concat-htpy-hom-arrow a =
    ( ap
      ( concat (coh-hom-arrow f g α a) (g (map-domain-hom-arrow f g γ a)))
      ( ap-concat g
        ( htpy-domain-htpy-hom-arrow f g α β H a)
        ( htpy-domain-htpy-hom-arrow f g β γ K a))) ∙
    ( coherence-square-identifications-comp-horizontal
      ( coh-hom-arrow f g α a)
      ( coh-hom-arrow f g β a)
      ( coh-hom-arrow f g γ a)
      ( coh-htpy-hom-arrow f g α β H a)
      ( coh-htpy-hom-arrow f g β γ K a))

  concat-htpy-hom-arrow : htpy-hom-arrow f g α γ
  pr1 concat-htpy-hom-arrow = htpy-domain-concat-htpy-hom-arrow
  pr1 (pr2 concat-htpy-hom-arrow) = htpy-codomain-concat-htpy-hom-arrow
  pr2 (pr2 concat-htpy-hom-arrow) = coh-concat-htpy-hom-arrow
```

### Inverses of homotopies of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α β : hom-arrow f g) (H : htpy-hom-arrow f g α β)
  where

  htpy-domain-inv-htpy-hom-arrow :
    map-domain-hom-arrow f g β ~ map-domain-hom-arrow f g α
  htpy-domain-inv-htpy-hom-arrow =
    inv-htpy (htpy-domain-htpy-hom-arrow f g α β H)

  htpy-codomain-inv-htpy-hom-arrow :
    map-codomain-hom-arrow f g β ~ map-codomain-hom-arrow f g α
  htpy-codomain-inv-htpy-hom-arrow =
    inv-htpy (htpy-codomain-htpy-hom-arrow f g α β H)

  coh-inv-htpy-hom-arrow :
    coherence-htpy-hom-arrow f g β α
      ( htpy-domain-inv-htpy-hom-arrow)
      ( htpy-codomain-inv-htpy-hom-arrow)
  coh-inv-htpy-hom-arrow a =
    ( ap
      ( concat (coh-hom-arrow f g β a) _)
      ( ap-inv g (htpy-domain-htpy-hom-arrow f g α β H a))) ∙
    ( double-transpose-eq-concat'
      ( coh-hom-arrow f g α a)
      ( htpy-codomain-htpy-hom-arrow f g α β H (f a))
      ( ap g (htpy-domain-htpy-hom-arrow f g α β H a))
      ( coh-hom-arrow f g β a)
      ( inv (coh-htpy-hom-arrow f g α β H a)))

  inv-htpy-hom-arrow : htpy-hom-arrow f g β α
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
  (f : A → B) (g : X → Y) (h : U → V)
  (γ : hom-arrow g h) (α β : hom-arrow f g) (H : htpy-hom-arrow f g α β)
  where

  htpy-domain-left-whisker-htpy-hom-arrow :
    map-domain-comp-hom-arrow f g h γ α ~ map-domain-comp-hom-arrow f g h γ β
  htpy-domain-left-whisker-htpy-hom-arrow =
    map-domain-hom-arrow g h γ ·l htpy-domain-htpy-hom-arrow f g α β H

  htpy-codomain-left-whisker-htpy-hom-arrow :
    map-codomain-comp-hom-arrow f g h γ α ~
    map-codomain-comp-hom-arrow f g h γ β
  htpy-codomain-left-whisker-htpy-hom-arrow =
    map-codomain-hom-arrow g h γ ·l htpy-codomain-htpy-hom-arrow f g α β H

  coh-left-whisker-htpy-hom-arrow :
    coherence-htpy-hom-arrow f h
      ( comp-hom-arrow f g h γ α)
      ( comp-hom-arrow f g h γ β)
      ( htpy-domain-left-whisker-htpy-hom-arrow)
      ( htpy-codomain-left-whisker-htpy-hom-arrow)
  coh-left-whisker-htpy-hom-arrow a =
    ( inv
      ( ap
        ( concat _ _)
        ( ap-comp h
          ( map-domain-hom-arrow g h γ)
          ( htpy-domain-htpy-hom-arrow f g α β H a)))) ∙
    ( assoc
      ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g α a))
      ( coh-hom-arrow g h γ (map-domain-hom-arrow f g α a))
      ( ap
        ( h ∘ map-domain-hom-arrow g h γ)
        ( htpy-domain-htpy-hom-arrow f g α β H a))) ∙
    ( ap
      ( concat
        ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g α a))
        ( h _))
      ( nat-htpy
        ( coh-hom-arrow g h γ)
        ( htpy-domain-htpy-hom-arrow f g α β H a))) ∙
    ( inv
      ( assoc
        ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g α a))
        ( ap
          ( map-codomain-hom-arrow g h γ ∘ g)
          ( htpy-domain-htpy-hom-arrow f g α β H a))
        ( coh-hom-arrow g h γ (map-domain-hom-arrow f g β a)))) ∙
    ( ap
      ( concat' _ (coh-hom-arrow g h γ (map-domain-hom-arrow f g β a)))
      ( ( ap
          ( concat
            ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g α a))
            ( _))
          ( ap-comp
            ( map-codomain-hom-arrow g h γ)
            ( g)
            ( htpy-domain-htpy-hom-arrow f g α β H a))) ∙
        ( ( inv
            ( ap-concat
              ( map-codomain-hom-arrow g h γ)
              ( coh-hom-arrow f g α a)
              ( ap g (htpy-domain-htpy-hom-arrow f g α β H a)))) ∙
          ( ap
            ( ap (map-codomain-hom-arrow g h γ))
            ( coh-htpy-hom-arrow f g α β H a)) ∙
          ( ap-concat
            ( map-codomain-hom-arrow g h γ)
            ( htpy-codomain-htpy-hom-arrow f g α β H (f a))
            ( coh-hom-arrow f g β a))))) ∙
    ( assoc
      ( ap
        ( map-codomain-hom-arrow g h γ)
        ( htpy-codomain-htpy-hom-arrow f g α β H (f a)))
      ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g β a))
      ( coh-hom-arrow g h γ (map-domain-hom-arrow f g β a)))

  left-whisker-htpy-hom-arrow :
    htpy-hom-arrow f h
      ( comp-hom-arrow f g h γ α)
      ( comp-hom-arrow f g h γ β)
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
  {K : UU l7} {L : UU l8} (f : A → B) (g : X → Y) (h : U → V) (i : K → L)
  (γ : hom-arrow h i) (β : hom-arrow g h) (α : hom-arrow f g)
  where

  assoc-comp-hom-arrow :
    htpy-hom-arrow f i
      ( comp-hom-arrow f g i (comp-hom-arrow g h i γ β) α)
      ( comp-hom-arrow f h i γ (comp-hom-arrow f g h β α))
  pr1 assoc-comp-hom-arrow = refl-htpy
  pr1 (pr2 assoc-comp-hom-arrow) = refl-htpy
  pr2 (pr2 assoc-comp-hom-arrow) =
    ( right-unit-htpy) ∙h
    ( inv-htpy
      ( assoc-pasting-horizontal-coherence-square-maps
        ( map-domain-hom-arrow f g α)
        ( map-domain-hom-arrow g h β)
        ( map-domain-hom-arrow h i γ)
        ( f)
        ( g)
        ( h)
        ( i)
        ( map-codomain-hom-arrow f g α)
        ( map-codomain-hom-arrow g h β)
        ( map-codomain-hom-arrow h i γ)
        ( coh-hom-arrow f g α)
        ( coh-hom-arrow g h β)
        ( coh-hom-arrow h i γ)))

  inv-assoc-comp-hom-arrow :
    htpy-hom-arrow f i
      ( comp-hom-arrow f h i γ (comp-hom-arrow f g h β α))
      ( comp-hom-arrow f g i (comp-hom-arrow g h i γ β) α)
  pr1 inv-assoc-comp-hom-arrow = refl-htpy
  pr1 (pr2 inv-assoc-comp-hom-arrow) = refl-htpy
  pr2 (pr2 inv-assoc-comp-hom-arrow) =
    ( right-unit-htpy) ∙h
    ( assoc-pasting-horizontal-coherence-square-maps
      ( map-domain-hom-arrow f g α)
      ( map-domain-hom-arrow g h β)
      ( map-domain-hom-arrow h i γ)
      ( f)
      ( g)
      ( h)
      ( i)
      ( map-codomain-hom-arrow f g α)
      ( map-codomain-hom-arrow g h β)
      ( map-codomain-hom-arrow h i γ)
      ( coh-hom-arrow f g α)
      ( coh-hom-arrow g h β)
      ( coh-hom-arrow h i γ))
```

### The left unit law for composition of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  left-unit-law-comp-hom-arrow :
    htpy-hom-arrow f g
      ( comp-hom-arrow f g g id-hom-arrow α)
      ( α)
  pr1 left-unit-law-comp-hom-arrow = refl-htpy
  pr1 (pr2 left-unit-law-comp-hom-arrow) = refl-htpy
  pr2 (pr2 left-unit-law-comp-hom-arrow) =
    ( right-unit-htpy) ∙h
    ( right-unit-law-pasting-horizontal-coherence-square-maps
      ( map-domain-hom-arrow f g α)
      ( f)
      ( g)
      ( map-codomain-hom-arrow f g α)
      ( coh-hom-arrow f g α))
```

### The right unit law for composition of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  right-unit-law-comp-hom-arrow :
    htpy-hom-arrow f g
      ( comp-hom-arrow f f g α id-hom-arrow)
      ( α)
  pr1 right-unit-law-comp-hom-arrow = refl-htpy
  pr1 (pr2 right-unit-law-comp-hom-arrow) = refl-htpy
  pr2 (pr2 right-unit-law-comp-hom-arrow) = right-unit-htpy
```

## See also

- [Morphisms of twisted arrows](foundation.morphisms-twisted-arrows.md).
