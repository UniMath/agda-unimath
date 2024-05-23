# Homotopies of morphisms of arrows

```agda
module foundation.homotopies-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-triangles-of-identifications
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import foundation-core.commuting-squares-of-homotopies
open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Consider two [morphisms of arrows](foundation.morphisms-arrows.md) `(i , j , H)`
and `(i' , j' , H')` from `f` to `g`, as in the diagrams

```text
        i                   i'
    A -----> X          A -----> X
    |        |          |        |
  f |        | g      f |        | g
    ∨        ∨          ∨        ∨
    B -----> Y          B -----> Y.
        j                   j'
```

A {{#concept "homotopy of morphisms of arrows"}} from `(i , j , H)` to
`(i' , j' , H')` is a triple `(I , J , K)` consisting of homotopies `I : i ~ i'`
and `J : j ~ j'` and a homotopy `K` witnessing that the
[square of homotopies](foundation.commuting-squares-of-homotopies.md)

```text
           J ·r f
  (j ∘ f) --------> (j' ∘ f)
     |                 |
   H |                 | H'
     ∨                 ∨
  (g ∘ i) --------> (g ∘ i')
           g ·l I
```

commutes.

## Definitions

### Homotopies of morphisms of arrows

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
```

### The reflexivity homotopy of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  htpy-domain-refl-htpy-hom-arrow :
    map-domain-hom-arrow f g α ~ map-domain-hom-arrow f g α
  htpy-domain-refl-htpy-hom-arrow = refl-htpy

  htpy-codomain-refl-htpy-hom-arrow :
    map-codomain-hom-arrow f g α ~ map-codomain-hom-arrow f g α
  htpy-codomain-refl-htpy-hom-arrow = refl-htpy

  coh-refl-htpy-hom-arrow :
    coherence-square-homotopies
      ( htpy-codomain-refl-htpy-hom-arrow ·r f)
      ( coh-hom-arrow f g α)
      ( coh-hom-arrow f g α)
      ( g ·l htpy-domain-refl-htpy-hom-arrow)
  coh-refl-htpy-hom-arrow = right-unit-htpy

  refl-htpy-hom-arrow : htpy-hom-arrow f g α α
  pr1 refl-htpy-hom-arrow = htpy-domain-refl-htpy-hom-arrow
  pr1 (pr2 refl-htpy-hom-arrow) = htpy-codomain-refl-htpy-hom-arrow
  pr2 (pr2 refl-htpy-hom-arrow) = coh-refl-htpy-hom-arrow
```

## Operations

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
    ( left-whisker-concat
      ( coh-hom-arrow f g α a)
      ( ap-concat g
        ( htpy-domain-htpy-hom-arrow f g α β H a)
        ( htpy-domain-htpy-hom-arrow f g β γ K a))) ∙
    ( horizontal-pasting-coherence-square-identifications
      ( htpy-codomain-htpy-hom-arrow f g α β H (f a))
      ( htpy-codomain-htpy-hom-arrow f g β γ K (f a))
      ( coh-hom-arrow f g α a)
      ( coh-hom-arrow f g β a)
      ( coh-hom-arrow f g γ a)
      ( (g ·l htpy-domain-htpy-hom-arrow f g α β H) a)
      ( (g ·l htpy-domain-htpy-hom-arrow f g β γ K) a)
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
    ( left-whisker-concat
      ( coh-hom-arrow f g β a)
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

### Whiskering of homotopies of morphisms of arrows with respect to composition

#### Left whiskering of homotopies of morphisms of arrows with respect to composition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (γ : hom-arrow g h) (α β : hom-arrow f g) (H : htpy-hom-arrow f g α β)
  where

  htpy-domain-left-whisker-comp-hom-arrow :
    map-domain-comp-hom-arrow f g h γ α ~ map-domain-comp-hom-arrow f g h γ β
  htpy-domain-left-whisker-comp-hom-arrow =
    map-domain-hom-arrow g h γ ·l htpy-domain-htpy-hom-arrow f g α β H

  htpy-codomain-left-whisker-comp-hom-arrow :
    map-codomain-comp-hom-arrow f g h γ α ~
    map-codomain-comp-hom-arrow f g h γ β
  htpy-codomain-left-whisker-comp-hom-arrow =
    map-codomain-hom-arrow g h γ ·l htpy-codomain-htpy-hom-arrow f g α β H

  coh-left-whisker-comp-hom-arrow :
    coherence-htpy-hom-arrow f h
      ( comp-hom-arrow f g h γ α)
      ( comp-hom-arrow f g h γ β)
      ( htpy-domain-left-whisker-comp-hom-arrow)
      ( htpy-codomain-left-whisker-comp-hom-arrow)
  coh-left-whisker-comp-hom-arrow a =
    ( left-whisker-concat-coherence-triangle-identifications'
      ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g α a))
      ( _)
      ( _)
      ( _)
      ( ( ap
          ( coh-hom-arrow g h γ (map-domain-hom-arrow f g α a) ∙_)
          ( inv
            ( ap-comp h
              ( map-domain-hom-arrow g h γ)
              ( htpy-domain-htpy-hom-arrow f g α β H a)))) ∙
        ( nat-htpy
          ( coh-hom-arrow g h γ)
          ( htpy-domain-htpy-hom-arrow f g α β H a)))) ∙
    ( right-whisker-concat-coherence-square-identifications
      ( ap
        ( map-codomain-hom-arrow g h γ)
        ( htpy-codomain-htpy-hom-arrow f g α β H (f a)))
      ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g α a))
      ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g β a))
      ( ap
        ( map-codomain-hom-arrow g h γ ∘ g)
        ( htpy-domain-htpy-hom-arrow f g α β H a))
      ( ( ap
          ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g α a) ∙_)
          ( ap-comp
            ( map-codomain-hom-arrow g h γ)
            ( g)
            ( htpy-domain-htpy-hom-arrow f g α β H a))) ∙
        ( map-coherence-square-identifications
          ( map-codomain-hom-arrow g h γ)
          ( htpy-codomain-htpy-hom-arrow f g α β H (f a))
          ( coh-hom-arrow f g α a)
          ( coh-hom-arrow f g β a)
          ( ap g (htpy-domain-htpy-hom-arrow f g α β H a))
          ( coh-htpy-hom-arrow f g α β H a)))
      ( coh-hom-arrow g h γ (map-domain-hom-arrow f g β a)))

  left-whisker-comp-hom-arrow :
    htpy-hom-arrow f h
      ( comp-hom-arrow f g h γ α)
      ( comp-hom-arrow f g h γ β)
  pr1 left-whisker-comp-hom-arrow =
    htpy-domain-left-whisker-comp-hom-arrow
  pr1 (pr2 left-whisker-comp-hom-arrow) =
    htpy-codomain-left-whisker-comp-hom-arrow
  pr2 (pr2 left-whisker-comp-hom-arrow) =
    coh-left-whisker-comp-hom-arrow
```

#### Right whiskering of homotopies of morphisms of arrows with respect to composition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (β γ : hom-arrow g h) (H : htpy-hom-arrow g h β γ) (α : hom-arrow f g)
  where

  htpy-domain-right-whisker-comp-hom-arrow :
    map-domain-comp-hom-arrow f g h β α ~ map-domain-comp-hom-arrow f g h γ α
  htpy-domain-right-whisker-comp-hom-arrow =
    htpy-domain-htpy-hom-arrow g h β γ H ·r map-domain-hom-arrow f g α

  htpy-codomain-right-whisker-comp-hom-arrow :
    map-codomain-comp-hom-arrow f g h β α ~
    map-codomain-comp-hom-arrow f g h γ α
  htpy-codomain-right-whisker-comp-hom-arrow =
    htpy-codomain-htpy-hom-arrow g h β γ H ·r map-codomain-hom-arrow f g α

  coh-right-whisker-comp-hom-arrow :
    coherence-htpy-hom-arrow f h
      ( comp-hom-arrow f g h β α)
      ( comp-hom-arrow f g h γ α)
      ( htpy-domain-right-whisker-comp-hom-arrow)
      ( htpy-codomain-right-whisker-comp-hom-arrow)
  coh-right-whisker-comp-hom-arrow a =
    ( left-whisker-concat-coherence-square-identifications
      ( ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α a))
      ( htpy-codomain-htpy-hom-arrow g h β γ H
        ( g (map-domain-hom-arrow f g α a)))
      ( coh-hom-arrow g h β (map-domain-hom-arrow f g α a))
      ( coh-hom-arrow g h γ (map-domain-hom-arrow f g α a))
      ( ap h
        ( htpy-domain-htpy-hom-arrow g h β γ H
          ( map-domain-hom-arrow f g α a)))
      ( coh-htpy-hom-arrow g h β γ H (map-domain-hom-arrow f g α a))) ∙
    ( ( assoc
        ( ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α a))
        ( htpy-codomain-htpy-hom-arrow g h β γ H
          ( g (map-domain-hom-arrow f g α a)))
        ( coh-hom-arrow g h γ (map-domain-hom-arrow f g α a))) ∙
      ( right-whisker-concat-coherence-square-identifications
        ( htpy-codomain-htpy-hom-arrow g h β γ H
          ( map-codomain-hom-arrow f g α (f a)))
        ( ap (map-codomain-hom-arrow g h β) (coh-hom-arrow f g α a))
        ( ap (map-codomain-hom-arrow g h γ) (coh-hom-arrow f g α a))
        ( htpy-codomain-htpy-hom-arrow g h β γ H
          ( g (map-domain-hom-arrow f g α a)))
        ( inv
          ( nat-htpy
            ( htpy-codomain-htpy-hom-arrow g h β γ H)
            ( coh-hom-arrow f g α a)))
        ( coh-hom-arrow g h γ (map-domain-hom-arrow f g α a))))

  right-whisker-comp-hom-arrow :
    htpy-hom-arrow f h
      ( comp-hom-arrow f g h β α)
      ( comp-hom-arrow f g h γ α)
  pr1 right-whisker-comp-hom-arrow =
    htpy-domain-right-whisker-comp-hom-arrow
  pr1 (pr2 right-whisker-comp-hom-arrow) =
    htpy-codomain-right-whisker-comp-hom-arrow
  pr2 (pr2 right-whisker-comp-hom-arrow) =
    coh-right-whisker-comp-hom-arrow
```

## Properties

### Homotopies of morphisms of arrows characterize equality of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  is-torsorial-htpy-hom-arrow :
    is-torsorial (htpy-hom-arrow f g α)
  is-torsorial-htpy-hom-arrow =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-domain-hom-arrow f g α))
      ( map-domain-hom-arrow f g α , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-codomain-hom-arrow f g α))
        ( map-codomain-hom-arrow f g α , refl-htpy)
        ( is-torsorial-htpy (coh-hom-arrow f g α ∙h refl-htpy)))

  htpy-eq-hom-arrow : (β : hom-arrow f g) → (α ＝ β) → htpy-hom-arrow f g α β
  htpy-eq-hom-arrow β refl = refl-htpy-hom-arrow f g α

  is-equiv-htpy-eq-hom-arrow :
    (β : hom-arrow f g) → is-equiv (htpy-eq-hom-arrow β)
  is-equiv-htpy-eq-hom-arrow =
    fundamental-theorem-id is-torsorial-htpy-hom-arrow htpy-eq-hom-arrow

  extensionality-hom-arrow :
    (β : hom-arrow f g) → (α ＝ β) ≃ htpy-hom-arrow f g α β
  pr1 (extensionality-hom-arrow β) = htpy-eq-hom-arrow β
  pr2 (extensionality-hom-arrow β) = is-equiv-htpy-eq-hom-arrow β

  eq-htpy-hom-arrow :
    (β : hom-arrow f g) → htpy-hom-arrow f g α β → α ＝ β
  eq-htpy-hom-arrow β = map-inv-equiv (extensionality-hom-arrow β)
```

### Homotopies of morphisms of arrows give homotopies of their associated cones

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
      (α β : hom-arrow f g)
  where

  coh-htpy-parallell-cone-htpy-hom-arrow :
    (H : htpy-hom-arrow f g α β) →
    coherence-htpy-parallel-cone
      ( htpy-codomain-htpy-hom-arrow f g α β H)
      ( refl-htpy' g)
      ( cone-hom-arrow f g α)
      ( cone-hom-arrow f g β)
      ( refl-htpy)
      ( htpy-domain-htpy-hom-arrow f g α β H)
  coh-htpy-parallell-cone-htpy-hom-arrow H =
    ( ap-concat-htpy (coh-hom-arrow f g α) right-unit-htpy) ∙h
    ( coh-htpy-hom-arrow f g α β H)

  htpy-parallell-cone-htpy-hom-arrow :
    (H : htpy-hom-arrow f g α β) →
    htpy-parallel-cone
      ( htpy-codomain-htpy-hom-arrow f g α β H)
      ( refl-htpy' g)
      ( cone-hom-arrow f g α)
      ( cone-hom-arrow f g β)
  htpy-parallell-cone-htpy-hom-arrow H =
    ( refl-htpy ,
      htpy-domain-htpy-hom-arrow f g α β H ,
      coh-htpy-parallell-cone-htpy-hom-arrow H)
```

### Associativity of composition of morphisms of arrows

Consider a commuting diagram of the form

```text
        α₀       β₀       γ₀
    A -----> X -----> U -----> K
    |        |        |        |
  f |   α  g |   β  h |   γ    | i
    ∨        ∨        ∨        ∨
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
