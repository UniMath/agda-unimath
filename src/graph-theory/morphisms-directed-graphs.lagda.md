# Morphisms of directed graphs

```agda
module graph-theory.morphisms-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import graph-theory.directed-graphs
```

</details>

## Definitions

### Morphisms of directed graphs

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  where

  hom-Directed-Graph : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-Directed-Graph =
    Σ ( vertex-Directed-Graph G → vertex-Directed-Graph H)
      ( λ α →
        (x y : vertex-Directed-Graph G) →
        edge-Directed-Graph G x y → edge-Directed-Graph H (α x) (α y))

  module _
    (f : hom-Directed-Graph)
    where

    vertex-hom-Directed-Graph :
      vertex-Directed-Graph G → vertex-Directed-Graph H
    vertex-hom-Directed-Graph = pr1 f

    edge-hom-Directed-Graph :
      {x y : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y) →
      edge-Directed-Graph H
        ( vertex-hom-Directed-Graph x)
        ( vertex-hom-Directed-Graph y)
    edge-hom-Directed-Graph {x} {y} e = pr2 f x y e

    direct-predecessor-hom-Directed-Graph :
      (x : vertex-Directed-Graph G) →
      direct-predecessor-Directed-Graph G x →
      direct-predecessor-Directed-Graph H (vertex-hom-Directed-Graph x)
    direct-predecessor-hom-Directed-Graph x =
      map-Σ
        ( λ y → edge-Directed-Graph H y (vertex-hom-Directed-Graph x))
        ( vertex-hom-Directed-Graph)
        ( λ y → edge-hom-Directed-Graph)

    direct-successor-hom-Directed-Graph :
      (x : vertex-Directed-Graph G) →
      direct-successor-Directed-Graph G x →
      direct-successor-Directed-Graph H (vertex-hom-Directed-Graph x)
    direct-successor-hom-Directed-Graph x =
      map-Σ
        ( edge-Directed-Graph H (vertex-hom-Directed-Graph x))
        ( vertex-hom-Directed-Graph)
        ( λ y → edge-hom-Directed-Graph)
```

### Composition of morphisms graphs

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (K : Directed-Graph l5 l6)
  where

  vertex-comp-hom-Directed-Graph :
    hom-Directed-Graph H K → hom-Directed-Graph G H →
    vertex-Directed-Graph G → vertex-Directed-Graph K
  vertex-comp-hom-Directed-Graph g f =
    (vertex-hom-Directed-Graph H K g) ∘ (vertex-hom-Directed-Graph G H f)

  edge-comp-hom-Directed-Graph :
    (g : hom-Directed-Graph H K) (f : hom-Directed-Graph G H)
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y →
    edge-Directed-Graph K
      ( vertex-comp-hom-Directed-Graph g f x)
      ( vertex-comp-hom-Directed-Graph g f y)
  edge-comp-hom-Directed-Graph g f x y e =
    edge-hom-Directed-Graph H K g (edge-hom-Directed-Graph G H f e)

  comp-hom-Directed-Graph :
    hom-Directed-Graph H K → hom-Directed-Graph G H →
    hom-Directed-Graph G K
  pr1 (comp-hom-Directed-Graph g f) = vertex-comp-hom-Directed-Graph g f
  pr2 (comp-hom-Directed-Graph g f) = edge-comp-hom-Directed-Graph g f
```

### Identity morphisms graphs

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  id-hom-Directed-Graph : hom-Directed-Graph G G
  pr1 id-hom-Directed-Graph = id
  pr2 id-hom-Directed-Graph _ _ = id
```

## Properties

### Characterizing the identity type of morphisms graphs

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  where

  htpy-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-Directed-Graph f g =
    Σ ( vertex-hom-Directed-Graph G H f ~ vertex-hom-Directed-Graph G H g)
      ( λ α →
        ( x y : vertex-Directed-Graph G) (e : edge-Directed-Graph G x y) →
        binary-tr
          ( edge-Directed-Graph H)
          ( α x)
          ( α y)
          ( edge-hom-Directed-Graph G H f e) ＝
        edge-hom-Directed-Graph G H g e)

  module _
    (f g : hom-Directed-Graph G H) (α : htpy-hom-Directed-Graph f g)
    where

    vertex-htpy-hom-Directed-Graph :
      vertex-hom-Directed-Graph G H f ~ vertex-hom-Directed-Graph G H g
    vertex-htpy-hom-Directed-Graph = pr1 α

    edge-htpy-hom-Directed-Graph :
      (x y : vertex-Directed-Graph G) (e : edge-Directed-Graph G x y) →
      binary-tr
        ( edge-Directed-Graph H)
        ( vertex-htpy-hom-Directed-Graph x)
        ( vertex-htpy-hom-Directed-Graph y)
        ( edge-hom-Directed-Graph G H f e) ＝
      edge-hom-Directed-Graph G H g e
    edge-htpy-hom-Directed-Graph = pr2 α

  refl-htpy-hom-Directed-Graph :
    (f : hom-Directed-Graph G H) → htpy-hom-Directed-Graph f f
  pr1 (refl-htpy-hom-Directed-Graph f) = refl-htpy
  pr2 (refl-htpy-hom-Directed-Graph f) x y e = refl

  htpy-eq-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → f ＝ g → htpy-hom-Directed-Graph f g
  htpy-eq-hom-Directed-Graph f .f refl = refl-htpy-hom-Directed-Graph f

  is-contr-total-htpy-hom-Directed-Graph :
    (f : hom-Directed-Graph G H) →
    is-contr (Σ (hom-Directed-Graph G H) (htpy-hom-Directed-Graph f))
  is-contr-total-htpy-hom-Directed-Graph f =
    is-contr-total-Eq-structure
      ( λ gV gE α →
        (x y : vertex-Directed-Graph G) (e : edge-Directed-Graph G x y) →
        binary-tr
          ( edge-Directed-Graph H)
          ( α x)
          ( α y)
          ( edge-hom-Directed-Graph G H f e) ＝
        gE x y e)
      ( is-contr-total-htpy (vertex-hom-Directed-Graph G H f))
      ( pair
        ( vertex-hom-Directed-Graph G H f)
        ( refl-htpy))
      ( is-contr-total-Eq-Π
        ( λ x g →
          ( y : vertex-Directed-Graph G) →
          ( λ e → edge-hom-Directed-Graph G H f e) ~ g y)
        ( λ x →
          is-contr-total-Eq-Π
            ( λ y g → (λ e → edge-hom-Directed-Graph G H f e) ~ g)
            ( λ y → is-contr-total-htpy (edge-hom-Directed-Graph G H f))))

  is-equiv-htpy-eq-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → is-equiv (htpy-eq-hom-Directed-Graph f g)
  is-equiv-htpy-eq-hom-Directed-Graph f =
    fundamental-theorem-id
      ( is-contr-total-htpy-hom-Directed-Graph f)
      ( htpy-eq-hom-Directed-Graph f)

  extensionality-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → (f ＝ g) ≃ htpy-hom-Directed-Graph f g
  pr1 (extensionality-hom-Directed-Graph f g) = htpy-eq-hom-Directed-Graph f g
  pr2 (extensionality-hom-Directed-Graph f g) =
    is-equiv-htpy-eq-hom-Directed-Graph f g

  eq-htpy-hom-Directed-Graph :
    (f g : hom-Directed-Graph G H) → htpy-hom-Directed-Graph f g → (f ＝ g)
  eq-htpy-hom-Directed-Graph f g =
    map-inv-equiv (extensionality-hom-Directed-Graph f g)
```
