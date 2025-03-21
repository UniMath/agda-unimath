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
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families

open import structured-types.commuting-squares-of-pointed-homotopies
open import structured-types.commuting-squares-of-pointed-maps
open import structured-types.pointed-2-homotopies
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.whiskering-pointed-2-homotopies-concatenation
open import structured-types.whiskering-pointed-homotopies-composition
```

</details>

## Idea

A {{#concept "morphism of pointed arrows" Agda=hom-pointed-arrow}} from a
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
    ∨        ∨
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

The
{{#concept "transposition" Disambiguation="morphism of pointed arrows" Agda=transpose-hom-pointed-arrow}}
of a morphism of pointed arrows

```text
        i
    A -----> X
    |        |
  f |        | g
    ∨        ∨
    B -----> Y
        j
```

is the morphism of pointed arrows

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
    ∨        ∨
    B -----> B
        id
```

where the pointed homotopy `id ∘∗ f ~∗ f ∘∗ id` is the concatenation of the left
unit law pointed homotopy and the inverse pointed homotopy of the right unit law
pointed homotopy.

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
    ∨        ∨        ∨
    B -----> Y -----> V.
        α₁       β₁
```

Then the outer rectangle commutes by horizontal pasting of commuting squares of
pointed maps. The
{{#concept "composition" Disambiguation="morphism of pointed arrows" Agda=comp-hom-pointed-arrow}}
of `β : g → h` with `α : f → g` is therefore defined to be

```text
        β₀ ∘ α₀
    A ----------> U
    |             |
  f |    α □ β    | h
    ∨             ∨
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

A
{{#concept "homotopy of morphisms of pointed arrows" Agda=htpy-hom-pointed-arrow}}
from `(i , j , H)` to `(i' , j' , H')` is a triple `(I , J , K)` consisting of
pointed homotopies `I : i ~∗ i'` and `J : j ~∗ j'` and a pointed `2`-homotopy
`K` witnessing that the
[square of pointed homotopies](structured-types.commuting-squares-of-pointed-homotopies.md)

```text
            J ·r f
  (j ∘∗ f) --------> (j' ∘∗ f)
     |                   |
   H |                   | H'
     ∨                   ∨
  (g ∘∗ i) ---------> (g ∘∗ i')
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
      ( right-whisker-comp-pointed-htpy _ _ J f)
      ( coh-hom-pointed-arrow f g α)
      ( coh-hom-pointed-arrow f g β)
      ( left-whisker-comp-pointed-htpy g _ _ I)

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
```

### The reflexive homotopy of pointed arrows

Consider a morphism of pointed arrows

```text
                α₀
            A -----> X
            |        |
  (f₀ , f₁) |   α₂   | (g₀ , g₁)
            ∨        ∨
            B -----> Y
                α₁
```

from `f : A →∗ B` to `g : X →∗ Y`. The reflexive homotopy of morphisms of arrows
`r := (r₀ , r₁ , r₂)` on `α := (α₀ , α₁ , α₂)` is given by

```text
  r₀ := refl-pointed-htpy : α₀ ~∗ α₀
  r₁ := refl-pointed-htpy : α₁ ~∗ α₁
```

and a pointed `2`-homotopy `r₂` witnessing that the square of pointed homotopies

```text
            r₁ ·r f
  (α₁ ∘ f) --------> (α₁ ∘ f)
      |                  |
   α₂ |                  | α₂
      ∨                  ∨
   (g ∘ α₀) --------> (g ∘ α₀)
             g ·l r₀
```

commutes. Note that `r₁ ·r f ~∗ refl-pointed-htpy` and
`g ·l r₀ ≐ refl-pointed-htpy`. By
[whiskering of pointed `2`-homotopies](structured-types.whiskering-pointed-2-homotopies-concatenation.md)
with respect to concatenation it follows that

```text
  (r₁ ·r f) ∙h α₂ ~∗ refl-pointed-htpy ∙h α₂ ~∗ α₂.
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A →∗ B) (g : X →∗ Y) (α : hom-pointed-arrow f g)
  where

  pointed-htpy-domain-refl-htpy-hom-pointed-arrow :
    pointed-map-domain-hom-pointed-arrow f g α ~∗
    pointed-map-domain-hom-pointed-arrow f g α
  pointed-htpy-domain-refl-htpy-hom-pointed-arrow = refl-pointed-htpy _

  pointed-htpy-codomain-refl-htpy-hom-pointed-arrow :
    pointed-map-codomain-hom-pointed-arrow f g α ~∗
    pointed-map-codomain-hom-pointed-arrow f g α
  pointed-htpy-codomain-refl-htpy-hom-pointed-arrow = refl-pointed-htpy _

  coh-refl-htpy-hom-pointed-arrow :
    coherence-htpy-hom-pointed-arrow f g α α
      ( pointed-htpy-domain-refl-htpy-hom-pointed-arrow)
      ( pointed-htpy-codomain-refl-htpy-hom-pointed-arrow)
  coh-refl-htpy-hom-pointed-arrow =
    concat-pointed-2-htpy
      ( right-unit-law-concat-pointed-htpy (coh-hom-pointed-arrow f g α))
      ( inv-pointed-2-htpy
        ( concat-pointed-2-htpy
          ( right-whisker-concat-pointed-2-htpy
            ( right-whisker-comp-pointed-htpy
              ( pointed-map-codomain-hom-pointed-arrow f g α)
              ( pointed-map-codomain-hom-pointed-arrow f g α)
              ( pointed-htpy-codomain-refl-htpy-hom-pointed-arrow)
              ( f))
            ( refl-pointed-htpy _)
            ( compute-refl-right-whisker-comp-pointed-htpy
              ( pointed-map-codomain-hom-pointed-arrow f g α)
              ( f))
            ( coh-hom-pointed-arrow f g α))
          ( left-unit-law-concat-pointed-htpy (coh-hom-pointed-arrow f g α))))

  refl-htpy-hom-pointed-arrow : htpy-hom-pointed-arrow f g α α
  pr1 refl-htpy-hom-pointed-arrow =
    pointed-htpy-domain-refl-htpy-hom-pointed-arrow
  pr1 (pr2 refl-htpy-hom-pointed-arrow) =
    pointed-htpy-codomain-refl-htpy-hom-pointed-arrow
  pr2 (pr2 refl-htpy-hom-pointed-arrow) =
    coh-refl-htpy-hom-pointed-arrow
```

### Characterization of the identity types of morphisms of pointed arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A →∗ B) (g : X →∗ Y) (α : hom-pointed-arrow f g)
  where

  is-torsorial-htpy-hom-pointed-arrow :
    is-torsorial (htpy-hom-pointed-arrow f g α)
  is-torsorial-htpy-hom-pointed-arrow =
    is-torsorial-Eq-structure
      ( is-torsorial-pointed-htpy _)
      ( pointed-map-domain-hom-pointed-arrow f g α , refl-pointed-htpy _)
      ( is-torsorial-Eq-structure
        ( is-torsorial-pointed-htpy _)
        ( pointed-map-codomain-hom-pointed-arrow f g α , refl-pointed-htpy _)
        ( is-contr-equiv' _
          ( equiv-tot
            ( λ H →
              equiv-concat-pointed-2-htpy'
                ( inv-pointed-2-htpy
                  ( concat-pointed-2-htpy
                    ( right-whisker-concat-pointed-2-htpy _ _
                      ( compute-refl-right-whisker-comp-pointed-htpy
                        ( pointed-map-codomain-hom-pointed-arrow f g α)
                        ( f))
                      ( H))
                    ( left-unit-law-concat-pointed-htpy H)))))
          ( is-torsorial-pointed-2-htpy
            ( concat-pointed-htpy
              ( coh-hom-pointed-arrow f g α)
              ( refl-pointed-htpy _)))))

  htpy-eq-hom-pointed-arrow :
    (β : hom-pointed-arrow f g) → α ＝ β → htpy-hom-pointed-arrow f g α β
  htpy-eq-hom-pointed-arrow β refl = refl-htpy-hom-pointed-arrow f g α

  is-equiv-htpy-eq-hom-pointed-arrow :
    (β : hom-pointed-arrow f g) → is-equiv (htpy-eq-hom-pointed-arrow β)
  is-equiv-htpy-eq-hom-pointed-arrow =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-pointed-arrow)
      ( htpy-eq-hom-pointed-arrow)

  extensionality-hom-pointed-arrow :
    (β : hom-pointed-arrow f g) → (α ＝ β) ≃ htpy-hom-pointed-arrow f g α β
  pr1 (extensionality-hom-pointed-arrow β) =
    htpy-eq-hom-pointed-arrow β
  pr2 (extensionality-hom-pointed-arrow β) =
    is-equiv-htpy-eq-hom-pointed-arrow β

  eq-htpy-hom-pointed-arrow :
    (β : hom-pointed-arrow f g) → htpy-hom-pointed-arrow f g α β → α ＝ β
  eq-htpy-hom-pointed-arrow β =
    map-inv-equiv (extensionality-hom-pointed-arrow β)
```

## See also

- [Equivalences of pointed arrows](structured-types.equivalences-pointed-arrows.md)
- [Morphisms of twisted pointed arrows](structured-types.morphisms-twisted-pointed-arrows.md)
