# Morphisms of pointed arrows

```agda
module structured-types.morphisms-pointed-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation.whiskering-homotopies-composition

open import structured-types.commuting-squares-of-pointed-homotopies
open import structured-types.commuting-squares-of-pointed-maps
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-homotopies
```

</details>

## Idea

A {{#concept "morphism of pointed arrows"}} from a
[pointed map](structured-types.pointed-maps.md) `f : A →∗ B` to a pointed map
`g : X →∗ Y` is a [triple](foundation.dependent-pair-types.md) `(i , j , H)`
consisting of pointed maps `i : A →∗ X` and `j : B →∗ Y` and a
[pointed homotopy](structured-types.pointed-homotopies.md)
`H : j ∘∗ f ~∗ g ∘∗ i` witnessing that the square

```text
        i
    A -----> X
    |        |
  f |        | g
    V        V
    B -----> Y
        j
```

[commutes](structured-types.commuting-squares-of-pointed-maps.md). Morphisms of
pointed arrows can be composed horizontally or vertically by pasting of squares.

## Definitions

### Morphisms of pointed arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A →∗ B) (g : X →∗ Y)
  where

  coherence-hom-pointed-arrow :
    (A →∗ X) → (B →∗ Y) → UU (l1 ⊔ l4)
  coherence-hom-pointed-arrow i = coherence-square-pointed-maps i f g

  hom-pointed-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-pointed-arrow =
    Σ (A →∗ X) (λ i → Σ (B →∗ Y) (coherence-hom-pointed-arrow i))

  pointed-map-domain-hom-pointed-arrow :
    hom-pointed-arrow → A →∗ X
  pointed-map-domain-hom-pointed-arrow = pr1

  map-domain-hom-pointed-arrow :
    hom-pointed-arrow → type-Pointed-Type A → type-Pointed-Type X
  map-domain-hom-pointed-arrow h =
    map-pointed-map (pointed-map-domain-hom-pointed-arrow h)

  preserves-point-map-domain-hom-pointed-arrow :
    (h : hom-pointed-arrow) →
    map-domain-hom-pointed-arrow h (point-Pointed-Type A) ＝
    point-Pointed-Type X
  preserves-point-map-domain-hom-pointed-arrow h =
    preserves-point-pointed-map (pointed-map-domain-hom-pointed-arrow h)

  pointed-map-codomain-hom-pointed-arrow :
    hom-pointed-arrow → B →∗ Y
  pointed-map-codomain-hom-pointed-arrow = pr1 ∘ pr2

  map-codomain-hom-pointed-arrow :
    hom-pointed-arrow → type-Pointed-Type B → type-Pointed-Type Y
  map-codomain-hom-pointed-arrow h =
    map-pointed-map (pointed-map-codomain-hom-pointed-arrow h)

  preserves-point-map-codomain-hom-pointed-arrow :
    (h : hom-pointed-arrow) →
    map-codomain-hom-pointed-arrow h (point-Pointed-Type B) ＝
    point-Pointed-Type Y
  preserves-point-map-codomain-hom-pointed-arrow h =
    preserves-point-pointed-map (pointed-map-codomain-hom-pointed-arrow h)

  coh-hom-pointed-arrow :
    (h : hom-pointed-arrow) →
    coherence-hom-pointed-arrow
      ( pointed-map-domain-hom-pointed-arrow h)
      ( pointed-map-codomain-hom-pointed-arrow h)
  coh-hom-pointed-arrow = pr2 ∘ pr2

  htpy-coh-hom-pointed-arrow :
    (h : hom-pointed-arrow) →
    coherence-hom-arrow
      ( map-pointed-map f)
      ( map-pointed-map g)
      ( map-domain-hom-pointed-arrow h)
      ( map-codomain-hom-pointed-arrow h)
  htpy-coh-hom-pointed-arrow h =
    htpy-pointed-htpy
      ( coh-hom-pointed-arrow h)
```

### Transposing morphisms of pointed arrows

The {{#concept "transposition" Disambiguation="morphism of pointed arrows"}} of
a morphism of pointed arrows

```text
        i
    A -----> X
    |        |
  f |        | g
    V        V
    B -----> Y
        j
```

is the morphism of pointed arrows

```text
        f
    A -----> B
    |        |
  i |        | j
    V        V
    X -----> Y.
        g
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A →∗ B) (g : X →∗ Y) (α : hom-pointed-arrow f g)
  where

  pointed-map-domain-transpose-hom-pointed-arrow : A →∗ B
  pointed-map-domain-transpose-hom-pointed-arrow = f

  pointed-map-codomain-transpose-hom-pointed-arrow : X →∗ Y
  pointed-map-codomain-transpose-hom-pointed-arrow = g

  coh-transpose-hom-pointed-arrow :
    coherence-hom-pointed-arrow
      ( pointed-map-domain-hom-pointed-arrow f g α)
      ( pointed-map-codomain-hom-pointed-arrow f g α)
      ( pointed-map-domain-transpose-hom-pointed-arrow)
      ( pointed-map-codomain-transpose-hom-pointed-arrow)
  coh-transpose-hom-pointed-arrow =
    inv-pointed-htpy
      ( coh-hom-pointed-arrow f g α)

  transpose-hom-pointed-arrow :
    hom-pointed-arrow
      ( pointed-map-domain-hom-pointed-arrow f g α)
      ( pointed-map-codomain-hom-pointed-arrow f g α)
  pr1 transpose-hom-pointed-arrow =
    pointed-map-domain-transpose-hom-pointed-arrow
  pr1 (pr2 transpose-hom-pointed-arrow) =
    pointed-map-codomain-transpose-hom-pointed-arrow
  pr2 (pr2 transpose-hom-pointed-arrow) = coh-transpose-hom-pointed-arrow
```

### The identity morphism of pointed arrows

The identity morphism of pointed arrows is defined as

```text
        id
    A -----> A
    |        |
  f |        | f
    V        V
    B -----> B
        id
```

where the homotopy `id ∘ f ~ f ∘ id` is the reflexivity homotopy.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} {f : A →∗ B}
  where

  id-hom-pointed-arrow : hom-pointed-arrow f f
  pr1 id-hom-pointed-arrow = id-pointed-map
  pr1 (pr2 id-hom-pointed-arrow) = id-pointed-map
  pr2 (pr2 id-hom-pointed-arrow) =
    concat-pointed-htpy
      ( left-unit-law-comp-pointed-map f)
      ( inv-pointed-htpy (right-unit-law-comp-pointed-map f))
```

### Composition of morphisms of pointed arrows

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
pointed maps. The
{{#concept "composition" Disambiguation="morphism of pointed arrows"}} of
`β : g → h` with `α : f → g` is therefore defined to be

```text
        β₀ ∘ α₀
    A ----------> U
    |             |
  f |    α □ β    | h
    V             V
    B ----------> V.
        β₁ ∘ α₁
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  {U : Pointed-Type l5} {V : Pointed-Type l6}
  (f : A →∗ B) (g : X →∗ Y) (h : U →∗ V) (b : hom-pointed-arrow g h)
  (a : hom-pointed-arrow f g)
  where

  pointed-map-domain-comp-hom-pointed-arrow : A →∗ U
  pointed-map-domain-comp-hom-pointed-arrow =
    pointed-map-domain-hom-pointed-arrow g h b ∘∗
    pointed-map-domain-hom-pointed-arrow f g a

  map-domain-comp-hom-pointed-arrow :
    type-Pointed-Type A → type-Pointed-Type U
  map-domain-comp-hom-pointed-arrow =
    map-pointed-map pointed-map-domain-comp-hom-pointed-arrow

  preserves-point-map-domain-comp-hom-pointed-arrow :
    map-domain-comp-hom-pointed-arrow (point-Pointed-Type A) ＝
    point-Pointed-Type U
  preserves-point-map-domain-comp-hom-pointed-arrow =
    preserves-point-pointed-map pointed-map-domain-comp-hom-pointed-arrow

  pointed-map-codomain-comp-hom-pointed-arrow : B →∗ V
  pointed-map-codomain-comp-hom-pointed-arrow =
    pointed-map-codomain-hom-pointed-arrow g h b ∘∗
    pointed-map-codomain-hom-pointed-arrow f g a

  map-codomain-comp-hom-pointed-arrow :
    type-Pointed-Type B → type-Pointed-Type V
  map-codomain-comp-hom-pointed-arrow =
    map-pointed-map pointed-map-codomain-comp-hom-pointed-arrow

  preserves-point-map-codomain-comp-hom-pointed-arrow :
    map-codomain-comp-hom-pointed-arrow (point-Pointed-Type B) ＝
    point-Pointed-Type V
  preserves-point-map-codomain-comp-hom-pointed-arrow =
    preserves-point-pointed-map pointed-map-codomain-comp-hom-pointed-arrow

  coh-comp-hom-pointed-arrow :
    coherence-hom-pointed-arrow f h
      ( pointed-map-domain-comp-hom-pointed-arrow)
      ( pointed-map-codomain-comp-hom-pointed-arrow)
  coh-comp-hom-pointed-arrow =
    horizontal-pasting-coherence-square-pointed-maps
      ( pointed-map-domain-hom-pointed-arrow f g a)
      ( pointed-map-domain-hom-pointed-arrow g h b)
      ( f)
      ( g)
      ( h)
      ( pointed-map-codomain-hom-pointed-arrow f g a)
      ( pointed-map-codomain-hom-pointed-arrow g h b)
      ( coh-hom-pointed-arrow f g a)
      ( coh-hom-pointed-arrow g h b)

  comp-hom-pointed-arrow : hom-pointed-arrow f h
  pr1 comp-hom-pointed-arrow = pointed-map-domain-comp-hom-pointed-arrow
  pr1 (pr2 comp-hom-pointed-arrow) = pointed-map-codomain-comp-hom-pointed-arrow
  pr2 (pr2 comp-hom-pointed-arrow) = coh-comp-hom-pointed-arrow
```

### Homotopies of morphisms of pointed arrows

A {{#concept "homotopy of morphisms of pointed arrows"}} from `(i , j , H)`
to `(i' , j' , H')` is a triple `(I , J , K)` consisting of pointed homotopies
`I : i ~∗ i'` and `J : j ~∗ j'` and a pointed 2-homotopy `K` witnessing that the
[square of pointed homotopies](structured-types.commuting-squares-of-pointed-homotopies.md)

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
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A →∗ B) (g : X →∗ Y) (α : hom-pointed-arrow f g)
  where

  coherence-htpy-hom-pointed-arrow :
    (β : hom-pointed-arrow f g)
    (I :
      pointed-map-domain-hom-pointed-arrow f g α ~∗
      pointed-map-domain-hom-pointed-arrow f g β)
    (J :
      pointed-map-codomain-hom-pointed-arrow f g α ~∗
      pointed-map-codomain-hom-pointed-arrow f g β) →
    UU (l1 ⊔ l4)
  coherence-htpy-hom-pointed-arrow β I J =
    coherence-square-pointed-homotopies
      ( right-whisker-pointed-htpy _ _ J f)
      ( coh-hom-pointed-arrow f g α)
      ( coh-hom-pointed-arrow f g β)
      ( left-whisker-pointed-htpy g _ _ I)

  htpy-hom-pointed-arrow :
    (β : hom-pointed-arrow f g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-pointed-arrow β =
    Σ ( pointed-map-domain-hom-pointed-arrow f g α ~∗
        pointed-map-domain-hom-pointed-arrow f g β)
      ( λ I →
        Σ ( pointed-map-codomain-hom-pointed-arrow f g α ~∗
            pointed-map-codomain-hom-pointed-arrow f g β)
          ( coherence-htpy-hom-pointed-arrow β I))

  module _
    (β : hom-pointed-arrow f g) (η : htpy-hom-pointed-arrow β)
    where

    pointed-htpy-domain-htpy-hom-pointed-arrow :
      pointed-map-domain-hom-pointed-arrow f g α ~∗
      pointed-map-domain-hom-pointed-arrow f g β
    pointed-htpy-domain-htpy-hom-pointed-arrow = pr1 η

    pointed-htpy-codomain-htpy-hom-pointed-arrow :
      pointed-map-codomain-hom-pointed-arrow f g α ~∗
      pointed-map-codomain-hom-pointed-arrow f g β
    pointed-htpy-codomain-htpy-hom-pointed-arrow = pr1 (pr2 η)

    coh-htpy-hom-pointed-arrow :
      coherence-htpy-hom-pointed-arrow β
        ( pointed-htpy-domain-htpy-hom-pointed-arrow)
        ( pointed-htpy-codomain-htpy-hom-pointed-arrow)
    coh-htpy-hom-pointed-arrow = pr2 (pr2 η)

  refl-htpy-hom-pointed-arrow : htpy-hom-pointed-arrow α
  pr1 refl-htpy-hom-pointed-arrow = refl-pointed-htpy _
  pr1 (pr2 refl-htpy-hom-pointed-arrow) = refl-pointed-htpy _
  pr2 (pr2 refl-htpy-hom-pointed-arrow) =
    concat-pointed-2-htpy
      ( right-unit-law-concat-pointed-htpy _)
      ( inv-pointed-2-htpy
        ( concat-pointed-2-htpy
          {!!}
          ( left-unit-law-concat-pointed-htpy _)))
  
  {-
      coherence-square-pointed-homotopies
      ( right-whisker-pointed-htpy _ _ J f)
      ( coh-hom-pointed-arrow f g α)
      ( coh-hom-pointed-arrow f g β)
      ( left-whisker-pointed-htpy g _ _ I)

    concat-pointed-2-htpy
      ( right-unit-law-concat-pointed-htpy _)
      ( {!!}) -}

  is-torsorial-htpy-hom-pointed-arrow : is-torsorial htpy-hom-pointed-arrow
  is-torsorial-htpy-hom-pointed-arrow =
    is-torsorial-Eq-structure
      {! !}
      {!!}
      {!!}

{-
    is-torsorial-Eq-structure
      ( λ i jH I → Σ _ _)
      ( is-torsorial-htpy (map-domain-hom-pointed-arrow f g α))
      ( map-domain-hom-pointed-arrow f g α , refl-htpy)
      ( is-torsorial-Eq-structure
        ( λ j H J → _)
        ( is-torsorial-htpy (map-codomain-hom-pointed-arrow f g α))
        ( map-codomain-hom-pointed-arrow f g α , refl-htpy)
        ( is-torsorial-htpy (coh-hom-pointed-arrow f g α ∙h refl-htpy))) -}

  htpy-eq-hom-pointed-arrow :
    (β : hom-pointed-arrow f g) → α ＝ β → htpy-hom-pointed-arrow β
  htpy-eq-hom-pointed-arrow β refl = refl-htpy-hom-pointed-arrow

  is-equiv-htpy-eq-hom-pointed-arrow :
    (β : hom-pointed-arrow f g) → is-equiv (htpy-eq-hom-pointed-arrow β)
  is-equiv-htpy-eq-hom-pointed-arrow =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-pointed-arrow)
      ( htpy-eq-hom-pointed-arrow)

  extensionality-hom-pointed-arrow :
    (β : hom-pointed-arrow f g) → (α ＝ β) ≃ htpy-hom-pointed-arrow β
  pr1 (extensionality-hom-pointed-arrow β) =
    htpy-eq-hom-pointed-arrow β
  pr2 (extensionality-hom-pointed-arrow β) =
    is-equiv-htpy-eq-hom-pointed-arrow β

  eq-htpy-hom-pointed-arrow :
    (β : hom-pointed-arrow f g) → htpy-hom-pointed-arrow β → α ＝ β
  eq-htpy-hom-pointed-arrow β =
    map-inv-equiv (extensionality-hom-pointed-arrow β)
```

### Concatenation of homotopies of morphisms of pointed arrows

```text
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A → B) (g : X → Y) (α β γ : hom-pointed-arrow f g)
  (H : htpy-hom-pointed-arrow f g α β)
  (K : htpy-hom-pointed-arrow f g β γ)
  where

  htpy-domain-concat-htpy-hom-pointed-arrow :
    map-domain-hom-pointed-arrow f g α ~ map-domain-hom-pointed-arrow f g γ
  htpy-domain-concat-htpy-hom-pointed-arrow =
    htpy-domain-htpy-hom-pointed-arrow f g α β H ∙h
    htpy-domain-htpy-hom-pointed-arrow f g β γ K

  htpy-codomain-concat-htpy-hom-pointed-arrow :
    map-codomain-hom-pointed-arrow f g α ~
    map-codomain-hom-pointed-arrow f g γ
  htpy-codomain-concat-htpy-hom-pointed-arrow =
    htpy-codomain-htpy-hom-pointed-arrow f g α β H ∙h
    htpy-codomain-htpy-hom-pointed-arrow f g β γ K

  coh-concat-htpy-hom-pointed-arrow :
    coherence-htpy-hom-pointed-arrow f g α γ
      ( htpy-domain-concat-htpy-hom-pointed-arrow)
      ( htpy-codomain-concat-htpy-hom-pointed-arrow)
  coh-concat-htpy-hom-pointed-arrow a =
    ( ap
      ( concat
        ( coh-hom-pointed-arrow f g α a)
        ( g (map-domain-hom-pointed-arrow f g γ a)))
      ( ap-concat g
        ( htpy-domain-htpy-hom-pointed-arrow f g α β H a)
        ( htpy-domain-htpy-hom-pointed-arrow f g β γ K a))) ∙
    ( horizontal-pasting-coherence-square-identifications
      ( coh-hom-pointed-arrow f g α a)
      ( coh-hom-pointed-arrow f g β a)
      ( coh-hom-pointed-arrow f g γ a)
      ( coh-htpy-hom-pointed-arrow f g α β H a)
      ( coh-htpy-hom-pointed-arrow f g β γ K a))

  concat-htpy-hom-pointed-arrow : htpy-hom-pointed-arrow f g α γ
  pr1 concat-htpy-hom-pointed-arrow =
    htpy-domain-concat-htpy-hom-pointed-arrow
  pr1 (pr2 concat-htpy-hom-pointed-arrow) =
    htpy-codomain-concat-htpy-hom-pointed-arrow
  pr2 (pr2 concat-htpy-hom-pointed-arrow) =
    coh-concat-htpy-hom-pointed-arrow
```

### Inverses of homotopies of morphisms of pointed arrows

```text
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A → B) (g : X → Y) (α β : hom-pointed-arrow f g)
  (H : htpy-hom-pointed-arrow f g α β)
  where

  htpy-domain-inv-htpy-hom-pointed-arrow :
    map-domain-hom-pointed-arrow f g β ~ map-domain-hom-pointed-arrow f g α
  htpy-domain-inv-htpy-hom-pointed-arrow =
    inv-htpy (htpy-domain-htpy-hom-pointed-arrow f g α β H)

  htpy-codomain-inv-htpy-hom-pointed-arrow :
    map-codomain-hom-pointed-arrow f g β ~ map-codomain-hom-pointed-arrow f g α
  htpy-codomain-inv-htpy-hom-pointed-arrow =
    inv-htpy (htpy-codomain-htpy-hom-pointed-arrow f g α β H)

  coh-inv-htpy-hom-pointed-arrow :
    coherence-htpy-hom-pointed-arrow f g β α
      ( htpy-domain-inv-htpy-hom-pointed-arrow)
      ( htpy-codomain-inv-htpy-hom-pointed-arrow)
  coh-inv-htpy-hom-pointed-arrow a =
    ( ap
      ( concat (coh-hom-pointed-arrow f g β a) _)
      ( ap-inv g (htpy-domain-htpy-hom-pointed-arrow f g α β H a))) ∙
    ( double-transpose-eq-concat'
      ( coh-hom-pointed-arrow f g α a)
      ( htpy-codomain-htpy-hom-pointed-arrow f g α β H (f a))
      ( ap g (htpy-domain-htpy-hom-pointed-arrow f g α β H a))
      ( coh-hom-pointed-arrow f g β a)
      ( inv (coh-htpy-hom-pointed-arrow f g α β H a)))

  inv-htpy-hom-pointed-arrow : htpy-hom-pointed-arrow f g β α
  pr1 inv-htpy-hom-pointed-arrow =
    htpy-domain-inv-htpy-hom-pointed-arrow
  pr1 (pr2 inv-htpy-hom-pointed-arrow) =
    htpy-codomain-inv-htpy-hom-pointed-arrow
  pr2 (pr2 inv-htpy-hom-pointed-arrow) =
    coh-inv-htpy-hom-pointed-arrow
```

### Whiskering of homotopies of morphisms of pointed arrows

#### Left whiskering

```text
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  {U : UU l5} {V : UU l6}
  (f : A → B) (g : X → Y) (h : U → V)
  (γ : hom-pointed-arrow g h)
  (α β : hom-pointed-arrow f g) (H : htpy-hom-pointed-arrow f g α β)
  where

  htpy-domain-left-whisker-htpy-hom-pointed-arrow :
    map-domain-comp-hom-pointed-arrow f g h γ α ~
    map-domain-comp-hom-pointed-arrow f g h γ β
  htpy-domain-left-whisker-htpy-hom-pointed-arrow =
    map-domain-hom-pointed-arrow g h γ ·l
    htpy-domain-htpy-hom-pointed-arrow f g α β H

  htpy-codomain-left-whisker-htpy-hom-pointed-arrow :
    map-codomain-comp-hom-pointed-arrow f g h γ α ~
    map-codomain-comp-hom-pointed-arrow f g h γ β
  htpy-codomain-left-whisker-htpy-hom-pointed-arrow =
    map-codomain-hom-pointed-arrow g h γ ·l
    htpy-codomain-htpy-hom-pointed-arrow f g α β H

  coh-left-whisker-htpy-hom-pointed-arrow :
    coherence-htpy-hom-pointed-arrow f h
      ( comp-hom-pointed-arrow f g h γ α)
      ( comp-hom-pointed-arrow f g h γ β)
      ( htpy-domain-left-whisker-htpy-hom-pointed-arrow)
      ( htpy-codomain-left-whisker-htpy-hom-pointed-arrow)
  coh-left-whisker-htpy-hom-pointed-arrow a = ?

{-
    ( left-whisk-triangle-identifications'
      ( ap
        ( map-codomain-hom-pointed-arrow g h γ)
        ( coh-hom-pointed-arrow f g α a))
      ( ( ap ?
          {-
          ( coh-hom-pointed-arrow g h γ
            ( map-domain-hom-pointed-arrow f g α a)) -}
          ( inv
            ( ap-comp h
              ( map-domain-hom-pointed-arrow g h γ)
              ( htpy-domain-htpy-hom-pointed-arrow f g α β H a)))) ∙
        ( nat-htpy
          ( coh-hom-pointed-arrow g h γ)
          ( htpy-domain-htpy-hom-pointed-arrow f g α β H a)))) ∙
    ( right-whisk-square-identification
      ( ap
        ( map-codomain-hom-pointed-arrow g h γ)
        ( htpy-codomain-htpy-hom-pointed-arrow f g α β H (f a)))
      ( ap
        ( map-codomain-hom-pointed-arrow g h γ)
        ( coh-hom-pointed-arrow f g α a))
      ( coh-hom-pointed-arrow g h γ (map-domain-hom-pointed-arrow f g β a))
      ( ( ap ?
          {-
          ( ap
            ( map-codomain-hom-pointed-arrow g h γ)
            ( coh-hom-pointed-arrow f g α a) ∙*) -}
          ( ap-comp
            ( map-codomain-hom-pointed-arrow g h γ)
            ( g)
            ( htpy-domain-htpy-hom-pointed-arrow f g α β H a))) ∙
        ( coherence-square-identifications-ap
          ( map-codomain-hom-pointed-arrow g h γ)
          ( htpy-codomain-htpy-hom-pointed-arrow f g α β H (f a))
          ( coh-hom-pointed-arrow f g α a)
          ( coh-hom-pointed-arrow f g β a)
          ( ap g (htpy-domain-htpy-hom-pointed-arrow f g α β H a))
          ( coh-htpy-hom-pointed-arrow f g α β H a)))) -}

  left-whisker-htpy-hom-pointed-arrow :
    htpy-hom-pointed-arrow f h
      ( comp-hom-pointed-arrow f g h γ α)
      ( comp-hom-pointed-arrow f g h γ β)
  pr1 left-whisker-htpy-hom-pointed-arrow =
    htpy-domain-left-whisker-htpy-hom-pointed-arrow
  pr1 (pr2 left-whisker-htpy-hom-pointed-arrow) =
    htpy-codomain-left-whisker-htpy-hom-pointed-arrow
  pr2 (pr2 left-whisker-htpy-hom-pointed-arrow) =
    coh-left-whisker-htpy-hom-pointed-arrow
```

#### Right whiskering

Exercise for Fredrik.

### Associativity of composition of morphisms of pointed arrows

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

Then associativity of composition of morphisms of pointed arrows follows
directly from associativity of horizontal pasting of commutative squares of
maps.

```text
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4} {U : UU l5} {V : UU l6}
  {K : UU l7} {L : UU l8} (f : A → B) (g : X → Y) (h : U → V) (i : K → L)
  (γ : hom-pointed-arrow h i) (β : hom-pointed-arrow g h)
  (α : hom-pointed-arrow f g)
  where

  assoc-comp-hom-pointed-arrow :
    htpy-hom-pointed-arrow f i
      ( comp-hom-pointed-arrow f g i (comp-hom-pointed-arrow g h i γ β) α)
      ( comp-hom-pointed-arrow f h i γ (comp-hom-pointed-arrow f g h β α))
  pr1 assoc-comp-hom-pointed-arrow = refl-htpy
  pr1 (pr2 assoc-comp-hom-pointed-arrow) = refl-htpy
  pr2 (pr2 assoc-comp-hom-pointed-arrow) = ?

{-
    ( right-unit-htpy) ∙h
    ( inv-htpy
      ( assoc-horizontal-pasting-coherence-square-maps
        ( map-domain-hom-pointed-arrow f g α)
        ( map-domain-hom-pointed-arrow g h β)
        ( map-domain-hom-pointed-arrow h i γ)
        ( f)
        ( g)
        ( h)
        ( i)
        ( map-codomain-hom-pointed-arrow f g α)
        ( map-codomain-hom-pointed-arrow g h β)
        ( map-codomain-hom-pointed-arrow h i γ)
        ( coh-hom-pointed-arrow f g α)
        ( coh-hom-pointed-arrow g h β)
        ( coh-hom-pointed-arrow h i γ))) -}

  inv-assoc-comp-hom-pointed-arrow :
    htpy-hom-pointed-arrow f i
      ( comp-hom-pointed-arrow f h i γ (comp-hom-pointed-arrow f g h β α))
      ( comp-hom-pointed-arrow f g i (comp-hom-pointed-arrow g h i γ β) α)
  pr1 inv-assoc-comp-hom-pointed-arrow = refl-htpy
  pr1 (pr2 inv-assoc-comp-hom-pointed-arrow) = refl-htpy
  pr2 (pr2 inv-assoc-comp-hom-pointed-arrow) = ?

{-
    ( right-unit-htpy) ∙h
    ( assoc-horizontal-pasting-coherence-square-maps
      ( map-domain-hom-pointed-arrow f g α)
      ( map-domain-hom-pointed-arrow g h β)
      ( map-domain-hom-pointed-arrow h i γ)
      ( f)
      ( g)
      ( h)
      ( i)
      ( map-codomain-hom-pointed-arrow f g α)
      ( map-codomain-hom-pointed-arrow g h β)
      ( map-codomain-hom-pointed-arrow h i γ)
      ( coh-hom-pointed-arrow f g α)
      ( coh-hom-pointed-arrow g h β)
      ( coh-hom-pointed-arrow h i γ)) -}
```

### The left unit law for composition of morphisms of pointed arrows

```text
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A → B) (g : X → Y) (α : hom-pointed-arrow f g)
  where

  left-unit-law-comp-hom-pointed-arrow :
    htpy-hom-pointed-arrow f g
      ( comp-hom-pointed-arrow f g g id-hom-pointed-arrow α)
      ( α)
  pr1 left-unit-law-comp-hom-pointed-arrow = refl-htpy
  pr1 (pr2 left-unit-law-comp-hom-pointed-arrow) = refl-htpy
  pr2 (pr2 left-unit-law-comp-hom-pointed-arrow) = ?

{-
    ( right-unit-htpy) ∙h
    ( right-unit-law-horizontal-pasting-coherence-square-maps
      ( map-domain-hom-pointed-arrow f g α)
      ( f)
      ( g)
      ( map-codomain-hom-pointed-arrow f g α)
      ( coh-hom-pointed-arrow f g α)) -}
```

### The right unit law for composition of morphisms of pointed arrows

```text
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A → B) (g : X → Y) (α : hom-pointed-arrow f g)
  where

  right-unit-law-comp-hom-pointed-arrow :
    htpy-hom-pointed-arrow f g
      ( comp-hom-pointed-arrow f f g α id-hom-pointed-arrow)
      ( α)
  pr1 right-unit-law-comp-hom-pointed-arrow = refl-htpy
  pr1 (pr2 right-unit-law-comp-hom-pointed-arrow) = refl-htpy
  pr2 (pr2 right-unit-law-comp-hom-pointed-arrow) = right-unit-htpy
```

## See also

- [Equivalences of pointed arrows](foundation.equivalences-pointed-arrows.md)
- [Morphisms of twisted pointed arrows](foundation.morphisms-twisted-pointed-arrows.md)
