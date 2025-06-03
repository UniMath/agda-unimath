# Dependent products of reflexive graphs

```agda
module graph-theory.dependent-products-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-dependent-identifications
open import foundation.binary-transport
open import foundation.commuting-squares-of-identifications
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.reflexive-relations
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.base-change-dependent-reflexive-graphs
open import graph-theory.cartesian-products-reflexive-graphs
open import graph-theory.dependent-products-directed-graphs
open import graph-theory.dependent-reflexive-graphs
open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.morphisms-reflexive-graphs
open import graph-theory.reflexive-graphs
open import graph-theory.sections-dependent-reflexive-graphs
```

</details>

## Idea

Given a [dependent reflexive graph](graph-theory.dependent-reflexive-graphs.md)
`B` over a [reflexive graphs](graph-theory.reflexive-graphs.md) `A`, the
{{#concept "dependent product" Disambiguation="reflexive graph" agda=Π-Reflexive-Graph}}
`Π A B` is the reflexive graph that satisfies the universal property

```text
  hom X (Π A B) ≃ section (X × A) (pr2* B).
```

Concretely, the reflexive graph `Π A B` has

- The type of [sections](graph-theory.sections-dependent-reflexive-graphs.md)
  `section A B` as its type of vertices.
- For any two sections `f g : section A B`, an edge from `f` to `g` is an
  element of type

  ```text
    (x y : A₀) (e : A₁ x y) → B₁ e (f₀ x) (g₀ y).
  ```

- For any section `f : section A B`, the reflexivity edge is given by `f₁`.

The universal property of the dependent product gives that the type of
[sections](graph-theory.sections-dependent-reflexive-graphs.md) of `B` is
[equivalent](foundation-core.equivalences.md) to the type of morphisms from the
[terminal reflexive graph](graph-theory.terminal-reflexive-graphs.md) into
`Π A B`, which is in turn equivalent to the type of vertices `f₀` of the
dependent product `Π A B`, i.e., the type of sections of `B`.

## Definitions

### The dependent product of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Reflexive-Graph l1 l2)
  (B : Dependent-Reflexive-Graph l3 l4 A)
  where

  vertex-Π-Reflexive-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  vertex-Π-Reflexive-Graph =
    section-Dependent-Reflexive-Graph B

  edge-Π-Reflexive-Graph :
    (f g : vertex-Π-Reflexive-Graph) → UU (l1 ⊔ l2 ⊔ l4)
  edge-Π-Reflexive-Graph f g =
    (x x' : vertex-Reflexive-Graph A) →
    (e : edge-Reflexive-Graph A x x') →
    edge-Dependent-Reflexive-Graph B e
      ( vertex-section-Dependent-Reflexive-Graph B f x)
      ( vertex-section-Dependent-Reflexive-Graph B g x')

  refl-Π-Reflexive-Graph :
    (f : vertex-Π-Reflexive-Graph) → edge-Π-Reflexive-Graph f f
  refl-Π-Reflexive-Graph f _ _ =
    edge-section-Dependent-Reflexive-Graph B f

  directed-graph-Π-Reflexive-Graph :
    Directed-Graph (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 directed-graph-Π-Reflexive-Graph = vertex-Π-Reflexive-Graph
  pr2 directed-graph-Π-Reflexive-Graph = edge-Π-Reflexive-Graph

  Π-Reflexive-Graph : Reflexive-Graph (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  pr1 Π-Reflexive-Graph = directed-graph-Π-Reflexive-Graph
  pr2 Π-Reflexive-Graph = refl-Π-Reflexive-Graph
```

## Properties

### The dependent product of reflexive graphs satisfies the universal property of the dependent product

#### The evaluation of a morphism into a dependent product of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Reflexive-Graph l1 l2) (B : Dependent-Reflexive-Graph l3 l4 A)
  (C : Reflexive-Graph l5 l6)
  (f : hom-Reflexive-Graph C (Π-Reflexive-Graph A B))
  where

  vertex-ev-section-Π-Reflexive-Graph :
    (x : vertex-product-Reflexive-Graph C A) →
    vertex-Dependent-Reflexive-Graph B (pr2 x)
  vertex-ev-section-Π-Reflexive-Graph (c , a) =
    vertex-section-Dependent-Reflexive-Graph B
      ( vertex-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f c)
      ( a)

  edge-ev-section-Π-Reflexive-Graph :
    {x x' : vertex-product-Reflexive-Graph C A}
    (e : edge-product-Reflexive-Graph C A x x') →
    edge-Dependent-Reflexive-Graph B
      ( pr2 e)
      ( vertex-ev-section-Π-Reflexive-Graph x)
      ( vertex-ev-section-Π-Reflexive-Graph x')
  edge-ev-section-Π-Reflexive-Graph (d , e) =
    edge-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f d _ _ e

  refl-ev-section-Π-Reflexive-Graph :
    (x : vertex-product-Reflexive-Graph C A) →
    edge-ev-section-Π-Reflexive-Graph (refl-product-Reflexive-Graph C A x) ＝
    refl-Dependent-Reflexive-Graph B (vertex-ev-section-Π-Reflexive-Graph x)
  refl-ev-section-Π-Reflexive-Graph (x , y) =
    ( htpy-eq
      ( htpy-eq
        ( htpy-eq (refl-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f x) y)
        ( y))
      ( refl-Reflexive-Graph A y)) ∙
    ( refl-section-Dependent-Reflexive-Graph B
      ( vertex-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f x)
      ( y))

  section-dependent-directed-graph-ev-section-Π-Reflexive-Graph :
    section-dependent-directed-graph-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( product-Reflexive-Graph C A)
        ( pr2-product-Reflexive-Graph C A)
        ( B))
  pr1 section-dependent-directed-graph-ev-section-Π-Reflexive-Graph =
    vertex-ev-section-Π-Reflexive-Graph
  pr2 section-dependent-directed-graph-ev-section-Π-Reflexive-Graph =
    edge-ev-section-Π-Reflexive-Graph

  ev-section-Π-Reflexive-Graph :
    section-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( product-Reflexive-Graph C A)
        ( pr2-product-Reflexive-Graph C A)
        ( B))
  pr1 ev-section-Π-Reflexive-Graph =
    section-dependent-directed-graph-ev-section-Π-Reflexive-Graph
  pr2 ev-section-Π-Reflexive-Graph =
    refl-ev-section-Π-Reflexive-Graph
```

#### Uncurrying a morphism from a cartesian product into a reflexive graph

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Reflexive-Graph l1 l2) (B : Dependent-Reflexive-Graph l3 l4 A)
  (C : Reflexive-Graph l5 l6)
  (f :
    section-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( product-Reflexive-Graph C A)
        ( pr2-product-Reflexive-Graph C A)
        ( B)))
  where

  module _
    (x : vertex-Reflexive-Graph C)
    where

    vertex-vertex-uncurry-section-product-Reflexive-Graph :
      (y : vertex-Reflexive-Graph A) → vertex-Dependent-Reflexive-Graph B y
    vertex-vertex-uncurry-section-product-Reflexive-Graph y =
      vertex-section-Dependent-Reflexive-Graph
        ( base-change-Dependent-Reflexive-Graph
          ( product-Reflexive-Graph C A)
          ( pr2-product-Reflexive-Graph C A)
          ( B))
        ( f)
        ( x , y)

    edge-vertex-uncurry-section-product-Reflexive-Graph :
      {y y' : vertex-Reflexive-Graph A} (e : edge-Reflexive-Graph A y y') →
      edge-Dependent-Reflexive-Graph B e
        ( vertex-vertex-uncurry-section-product-Reflexive-Graph y)
        ( vertex-vertex-uncurry-section-product-Reflexive-Graph y')
    edge-vertex-uncurry-section-product-Reflexive-Graph e =
      edge-section-Dependent-Reflexive-Graph
        ( base-change-Dependent-Reflexive-Graph
          ( product-Reflexive-Graph C A)
          ( pr2-product-Reflexive-Graph C A)
          ( B))
        ( f)
        ( refl-Reflexive-Graph C x , e)

    refl-vertex-uncurry-section-product-Reflexive-Graph :
      (y : vertex-Reflexive-Graph A) →
      edge-vertex-uncurry-section-product-Reflexive-Graph
        ( refl-Reflexive-Graph A y) ＝
      refl-Dependent-Reflexive-Graph B
        ( vertex-vertex-uncurry-section-product-Reflexive-Graph y)
    refl-vertex-uncurry-section-product-Reflexive-Graph y =
      refl-section-Dependent-Reflexive-Graph
        ( base-change-Dependent-Reflexive-Graph
          ( product-Reflexive-Graph C A)
          ( pr2-product-Reflexive-Graph C A)
          ( B))
        ( f)
        ( x , y)

    section-dependent-directed-graph-vertex-uncurry-section-product-Reflexive-Graph :
      section-dependent-directed-graph-Dependent-Reflexive-Graph B
    pr1
      section-dependent-directed-graph-vertex-uncurry-section-product-Reflexive-Graph =
      vertex-vertex-uncurry-section-product-Reflexive-Graph
    pr2
      section-dependent-directed-graph-vertex-uncurry-section-product-Reflexive-Graph =
      edge-vertex-uncurry-section-product-Reflexive-Graph

  vertex-uncurry-section-product-Reflexive-Graph :
    vertex-Reflexive-Graph C → vertex-Π-Reflexive-Graph A B
  pr1 (vertex-uncurry-section-product-Reflexive-Graph x) =
    section-dependent-directed-graph-vertex-uncurry-section-product-Reflexive-Graph
      x
  pr2 (vertex-uncurry-section-product-Reflexive-Graph x) =
    refl-vertex-uncurry-section-product-Reflexive-Graph x

  edge-uncurry-section-product-Reflexive-Graph :
    {x x' : vertex-Reflexive-Graph C} (d : edge-Reflexive-Graph C x x') →
    edge-Π-Reflexive-Graph A B
      ( vertex-uncurry-section-product-Reflexive-Graph x)
      ( vertex-uncurry-section-product-Reflexive-Graph x')
  edge-uncurry-section-product-Reflexive-Graph d y y' e =
    edge-section-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( product-Reflexive-Graph C A)
        ( pr2-product-Reflexive-Graph C A)
        ( B))
      ( f)
      ( d , e)

  refl-uncurry-section-product-Reflexive-Graph :
    (x : vertex-Reflexive-Graph C) →
    edge-uncurry-section-product-Reflexive-Graph (refl-Reflexive-Graph C x) ＝
    refl-Π-Reflexive-Graph A B
      ( vertex-uncurry-section-product-Reflexive-Graph x)
  refl-uncurry-section-product-Reflexive-Graph x =
    refl

  hom-directed-graph-uncurry-section-product-Reflexive-Graph :
    hom-Directed-Graph
      ( directed-graph-Reflexive-Graph C)
      ( directed-graph-Π-Reflexive-Graph A B)
  pr1 hom-directed-graph-uncurry-section-product-Reflexive-Graph =
    vertex-uncurry-section-product-Reflexive-Graph
  pr2 hom-directed-graph-uncurry-section-product-Reflexive-Graph _ _ =
    edge-uncurry-section-product-Reflexive-Graph

  uncurry-section-product-Reflexive-Graph :
    hom-Reflexive-Graph C (Π-Reflexive-Graph A B)
  pr1 uncurry-section-product-Reflexive-Graph =
    hom-directed-graph-uncurry-section-product-Reflexive-Graph
  pr2 uncurry-section-product-Reflexive-Graph =
    refl-uncurry-section-product-Reflexive-Graph
```

#### The equivalence of the adjunction between products and dependent products of reflexive graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Reflexive-Graph l1 l2) (B : Dependent-Reflexive-Graph l3 l4 A)
  (C : Reflexive-Graph l5 l6)
  where

  htpy-is-section-uncurry-section-product-Reflexive-Graph :
    ( f :
      section-Dependent-Reflexive-Graph
        ( base-change-Dependent-Reflexive-Graph
          ( product-Reflexive-Graph C A)
          ( pr2-product-Reflexive-Graph C A)
          ( B))) →
    htpy-section-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( product-Reflexive-Graph C A)
        ( pr2-product-Reflexive-Graph C A)
        ( B))
      ( ev-section-Π-Reflexive-Graph A B C
        ( uncurry-section-product-Reflexive-Graph A B C f))
      ( f)
  pr1 (pr1 (htpy-is-section-uncurry-section-product-Reflexive-Graph f)) =
    refl-htpy
  pr2 (pr1 (htpy-is-section-uncurry-section-product-Reflexive-Graph f)) =
    refl-htpy
  pr2 (htpy-is-section-uncurry-section-product-Reflexive-Graph f) x =
    inv (right-unit ∙ ap-id _)

  is-section-uncurry-section-product-Reflexive-Graph :
    is-section
      ( ev-section-Π-Reflexive-Graph A B C)
      ( uncurry-section-product-Reflexive-Graph A B C)
  is-section-uncurry-section-product-Reflexive-Graph f =
    eq-htpy-section-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( product-Reflexive-Graph C A)
        ( pr2-product-Reflexive-Graph C A)
        ( B))
      ( ev-section-Π-Reflexive-Graph A B C
        ( uncurry-section-product-Reflexive-Graph A B C f))
      ( f)
      ( htpy-is-section-uncurry-section-product-Reflexive-Graph f)

  htpy-hom-Π-Reflexive-Graph :
    (f g : hom-Reflexive-Graph C (Π-Reflexive-Graph A B)) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  htpy-hom-Π-Reflexive-Graph f g =
    Σ ( Σ ( (x : vertex-Reflexive-Graph C) →
            htpy-section-Dependent-Reflexive-Graph B
              ( vertex-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f x)
              ( vertex-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) g x))
          ( λ h₀ →
            (x x' : vertex-Reflexive-Graph C)
            (d : edge-Reflexive-Graph C x x')
            (y y' : vertex-Reflexive-Graph A)
            (e : edge-Reflexive-Graph A y y') →
            binary-tr
              ( edge-Dependent-Reflexive-Graph B e)
              ( pr1 (pr1 (h₀ x)) y)
              ( pr1 (pr1 (h₀ x')) y')
              ( edge-hom-Reflexive-Graph C
                ( Π-Reflexive-Graph A B)
                ( f)
                ( d)
                ( y)
                ( y')
                ( e)) ＝
            edge-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) g d y y' e))
      ( λ h →
        (x : vertex-Reflexive-Graph C)
        (y y' : vertex-Reflexive-Graph A) (e : edge-Reflexive-Graph A y y') →
        coherence-square-identifications
          ( ap
            ( binary-tr
              ( edge-Dependent-Reflexive-Graph B e)
              ( pr1 (pr1 (pr1 h x)) y)
              ( pr1 (pr1 (pr1 h x)) y'))
          ( htpy-eq
            ( htpy-eq
              ( htpy-eq
                ( refl-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f x)
                ( y))
              ( y'))
            ( e)))
          ( pr2 h x x (refl-Reflexive-Graph C x) y y' e)
          ( pr2 (pr1 (pr1 h x)) e)
          ( htpy-eq
            ( htpy-eq
              ( htpy-eq
                ( refl-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) g x)
                ( y))
              ( y'))
            ( e)))

  refl-htpy-hom-Π-Reflexive-Graph :
    (f : hom-Reflexive-Graph C (Π-Reflexive-Graph A B)) →
    htpy-hom-Π-Reflexive-Graph f f
  pr1 (pr1 (refl-htpy-hom-Π-Reflexive-Graph f)) x =
    refl-htpy-section-Dependent-Reflexive-Graph B
      ( vertex-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f x)
  pr2 (pr1 (refl-htpy-hom-Π-Reflexive-Graph f)) x x' d y y' e = refl
  pr2 (refl-htpy-hom-Π-Reflexive-Graph f) x y y' e =
    inv (right-unit ∙ ap-id _)

  abstract
    is-torsorial-htpy-hom-Π-Reflexive-Graph :
      (f : hom-Reflexive-Graph C (Π-Reflexive-Graph A B)) →
      is-torsorial (htpy-hom-Π-Reflexive-Graph f)
    is-torsorial-htpy-hom-Π-Reflexive-Graph f =
      is-torsorial-Eq-structure
        ( is-torsorial-Eq-structure
          ( is-torsorial-Eq-Π
            ( λ x →
              is-torsorial-htpy-section-Dependent-Reflexive-Graph B
                ( vertex-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f x)))
          ( ( λ x → vertex-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f x) ,
            ( λ x → refl-htpy-section-Dependent-Reflexive-Graph B _))
          ( is-torsorial-Eq-Π
            ( λ x →
              is-torsorial-Eq-Π
                ( λ x' →
                  is-torsorial-Eq-Π
                    ( λ d →
                      is-torsorial-Eq-Π
                        ( λ y →
                          is-torsorial-Eq-Π
                            ( λ y' →
                              is-torsorial-Eq-Π
                                ( λ e →
                                  is-torsorial-Id _))))))))
        ( ( ( λ x → vertex-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f x) ,
            ( λ x x' d y y' e → _)) ,
          ( λ x → refl-htpy-section-Dependent-Reflexive-Graph B _) ,
          ( λ x x' d y y' e → refl))
        ( is-torsorial-Eq-Π
          ( λ x →
            is-contr-equiv
              ( Σ ( (y y' : vertex-Reflexive-Graph A)
                    (e : edge-Reflexive-Graph A y y') →
                    ( edge-hom-Reflexive-Graph C
                      ( Π-Reflexive-Graph A B)
                      ( f)
                      ( refl-Reflexive-Graph C x)
                      ( y)
                      ( y')
                      ( e)) ＝
                    ( refl-Π-Reflexive-Graph A B
                      ( vertex-hom-Reflexive-Graph C
                        ( Π-Reflexive-Graph A B)
                        ( f)
                        ( x))
                      ( y)
                      ( y')
                      ( e)))
                  ( λ H →
                    (y y' : vertex-Reflexive-Graph A)
                    (e : edge-Reflexive-Graph A y y') →
                    coherence-square-identifications
                      ( ap
                        ( id)
                        ( htpy-eq
                          ( htpy-eq
                            ( htpy-eq
                              ( refl-hom-Reflexive-Graph C
                                ( Π-Reflexive-Graph A B)
                                ( f)
                                ( x))
                              ( y))
                            ( y'))
                          ( e)))
                      ( refl)
                      ( refl)
                      ( H y y' e)))
              ( equiv-Σ-equiv-base _
                ( ( equiv-Π-equiv-family
                    ( λ y →
                      ( equiv-Π-equiv-family (λ y' → equiv-funext)) ∘e
                      ( equiv-funext))) ∘e
                  ( equiv-funext)))
              ( is-torsorial-Eq-Π
                ( λ y →
                  is-torsorial-Eq-Π
                    ( λ y' → is-torsorial-Eq-Π (λ e → is-torsorial-Id' _))))))

  htpy-eq-hom-Π-Reflexive-Graph :
    (f g : hom-Reflexive-Graph C (Π-Reflexive-Graph A B)) →
    f ＝ g → htpy-hom-Π-Reflexive-Graph f g
  htpy-eq-hom-Π-Reflexive-Graph f .f refl =
    refl-htpy-hom-Π-Reflexive-Graph f

  abstract
    is-equiv-htpy-eq-hom-Π-Reflexive-Graph :
      (f g : hom-Reflexive-Graph C (Π-Reflexive-Graph A B)) →
      is-equiv (htpy-eq-hom-Π-Reflexive-Graph f g)
    is-equiv-htpy-eq-hom-Π-Reflexive-Graph f =
      fundamental-theorem-id
        ( is-torsorial-htpy-hom-Π-Reflexive-Graph f)
        ( htpy-eq-hom-Π-Reflexive-Graph f)

  extensionality-hom-Π-Reflexive-Graph :
    (f g : hom-Reflexive-Graph C (Π-Reflexive-Graph A B)) →
    (f ＝ g) ≃ htpy-hom-Π-Reflexive-Graph f g
  pr1 (extensionality-hom-Π-Reflexive-Graph f g) =
    htpy-eq-hom-Π-Reflexive-Graph f g
  pr2 (extensionality-hom-Π-Reflexive-Graph f g) =
    is-equiv-htpy-eq-hom-Π-Reflexive-Graph f g

  eq-htpy-hom-Π-Reflexive-Graph :
    (f g : hom-Reflexive-Graph C (Π-Reflexive-Graph A B)) →
    htpy-hom-Π-Reflexive-Graph f g → f ＝ g
  eq-htpy-hom-Π-Reflexive-Graph f g =
    map-inv-equiv (extensionality-hom-Π-Reflexive-Graph f g)

  htpy-is-retraction-uncurry-section-product-Reflexive-Graph :
    (f : hom-Reflexive-Graph C (Π-Reflexive-Graph A B)) →
    htpy-hom-Π-Reflexive-Graph
      ( uncurry-section-product-Reflexive-Graph A B C
        ( ev-section-Π-Reflexive-Graph A B C f))
      ( f)
  pr1
    ( pr1
      ( pr1
        ( pr1
          ( htpy-is-retraction-uncurry-section-product-Reflexive-Graph f))
        ( x))) =
    refl-htpy
  pr2
    ( pr1
      ( pr1
        ( pr1
          ( htpy-is-retraction-uncurry-section-product-Reflexive-Graph f))
        ( x)))
    { y}
    { y'}
    ( e) =
    htpy-eq
      ( htpy-eq
        ( htpy-eq
          ( refl-hom-Reflexive-Graph C (Π-Reflexive-Graph A B) f _)
            ( y))
          ( y'))
        ( e)
  pr2
    ( pr1
      ( pr1
        ( htpy-is-retraction-uncurry-section-product-Reflexive-Graph f))
      ( x))
    ( y) =
    inv (right-unit ∙ ap-id _)
  pr2
    ( pr1
      ( htpy-is-retraction-uncurry-section-product-Reflexive-Graph f))
    ( x)
    ( x')
    ( d)
    ( y)
    ( y')
    ( e) =
    refl
  pr2
    ( htpy-is-retraction-uncurry-section-product-Reflexive-Graph f)
    ( x)
    ( y)
    ( y')
    ( e) =
    refl

  is-retraction-uncurry-section-product-Reflexive-Graph :
    is-retraction
      ( ev-section-Π-Reflexive-Graph A B C)
      ( uncurry-section-product-Reflexive-Graph A B C)
  is-retraction-uncurry-section-product-Reflexive-Graph f =
    eq-htpy-hom-Π-Reflexive-Graph
      ( uncurry-section-product-Reflexive-Graph A B C
        ( ev-section-Π-Reflexive-Graph A B C f))
      ( f)
      ( htpy-is-retraction-uncurry-section-product-Reflexive-Graph f)

  abstract
    is-equiv-ev-section-Π-Reflexive-Graph :
      is-equiv (ev-section-Π-Reflexive-Graph A B C)
    is-equiv-ev-section-Π-Reflexive-Graph =
      is-equiv-is-invertible
        ( uncurry-section-product-Reflexive-Graph A B C)
        ( is-section-uncurry-section-product-Reflexive-Graph)
        ( is-retraction-uncurry-section-product-Reflexive-Graph)

  ev-equiv-hom-Π-Reflexive-Graph :
    hom-Reflexive-Graph C (Π-Reflexive-Graph A B) ≃
    section-Dependent-Reflexive-Graph
      ( base-change-Dependent-Reflexive-Graph
        ( product-Reflexive-Graph C A)
        ( pr2-product-Reflexive-Graph C A)
        ( B))
  pr1 ev-equiv-hom-Π-Reflexive-Graph =
    ev-section-Π-Reflexive-Graph A B C
  pr2 ev-equiv-hom-Π-Reflexive-Graph =
    is-equiv-ev-section-Π-Reflexive-Graph
```

## See also

- [dependent sums of reflexive graphs](graph-theory.dependent-sums-reflexive-graphs.md)
