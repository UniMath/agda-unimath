# Functoriality of the combinator of directed trees

```agda
module trees.functoriality-combinator-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.combinator-directed-trees
open import trees.directed-trees
open import trees.equivalences-directed-trees
open import trees.morphisms-directed-trees
open import trees.rooted-morphisms-directed-trees
```

</details>

## Idea

Given a family of [rooted morphisms](trees.rooted-morphisms-directed-trees.md)
`fᵢ : Sᵢ → Tᵢ` of [directed trees](trees.directed-trees.md), we obtain a
[morphism](trees.morphisms-directed-trees.md)

```text
  combinator f : combinator S → combinator T
```

of directed trees. Furthermore, `f` is a family of
[equivalences](trees.equivalences-directed-trees.md) of directed trees if and
only if `combinator f` is an equivalence.

## Definitions

### The action of the combinator on families of rooted morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  (S : I → Directed-Tree l2 l3) (T : I → Directed-Tree l4 l5)
  (f : (i : I) → rooted-hom-Directed-Tree (S i) (T i))
  where

  node-rooted-hom-combinator-Directed-Tree :
    node-combinator-Directed-Tree S → node-combinator-Directed-Tree T
  node-rooted-hom-combinator-Directed-Tree root-combinator-Directed-Tree =
    root-combinator-Directed-Tree
  node-rooted-hom-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    node-inclusion-combinator-Directed-Tree i
      ( node-rooted-hom-Directed-Tree (S i) (T i) (f i) x)

  edge-rooted-hom-combinator-Directed-Tree :
    (x y : node-combinator-Directed-Tree S) →
    edge-combinator-Directed-Tree S x y →
    edge-combinator-Directed-Tree T
      ( node-rooted-hom-combinator-Directed-Tree x)
      ( node-rooted-hom-combinator-Directed-Tree y)
  edge-rooted-hom-combinator-Directed-Tree ._ ._
    ( edge-to-root-combinator-Directed-Tree i) =
    tr
      ( λ u → edge-combinator-Directed-Tree T u root-combinator-Directed-Tree)
      ( ap
        ( node-inclusion-combinator-Directed-Tree i)
        ( preserves-root-rooted-hom-Directed-Tree (S i) (T i) (f i)))
      ( edge-to-root-combinator-Directed-Tree i)
  edge-rooted-hom-combinator-Directed-Tree ._ ._
    ( edge-inclusion-combinator-Directed-Tree i x y e) =
    edge-inclusion-combinator-Directed-Tree i
      ( node-rooted-hom-Directed-Tree (S i) (T i) (f i) x)
      ( node-rooted-hom-Directed-Tree (S i) (T i) (f i) y)
      ( edge-rooted-hom-Directed-Tree (S i) (T i) (f i) e)

  hom-combinator-Directed-Tree :
    hom-Directed-Tree (combinator-Directed-Tree S) (combinator-Directed-Tree T)
  pr1 hom-combinator-Directed-Tree = node-rooted-hom-combinator-Directed-Tree
  pr2 hom-combinator-Directed-Tree = edge-rooted-hom-combinator-Directed-Tree

  preserves-root-rooted-hom-combinator-Directed-Tree :
    node-rooted-hom-combinator-Directed-Tree root-combinator-Directed-Tree ＝
    root-combinator-Directed-Tree
  preserves-root-rooted-hom-combinator-Directed-Tree = refl

  rooted-hom-combinator-Directed-Tree :
    rooted-hom-Directed-Tree
      ( combinator-Directed-Tree S)
      ( combinator-Directed-Tree T)
  pr1 rooted-hom-combinator-Directed-Tree = hom-combinator-Directed-Tree
  pr2 rooted-hom-combinator-Directed-Tree =
    preserves-root-rooted-hom-combinator-Directed-Tree
```

### The action of the combinator is functorial

#### The action of the combinator preserves identity morphisms

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (T : I → Directed-Tree l2 l3)
  where

  node-id-rooted-hom-combinator-Directed-Tree :
    node-rooted-hom-combinator-Directed-Tree T T
      ( λ i → id-rooted-hom-Directed-Tree (T i)) ~ id
  node-id-rooted-hom-combinator-Directed-Tree root-combinator-Directed-Tree =
    refl
  node-id-rooted-hom-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    refl

  edge-id-rooted-hom-combinator-Directed-Tree :
    (x y : node-combinator-Directed-Tree T) →
    (e : edge-combinator-Directed-Tree T x y) →
    binary-tr
      ( edge-combinator-Directed-Tree T)
      ( node-id-rooted-hom-combinator-Directed-Tree x)
      ( node-id-rooted-hom-combinator-Directed-Tree y)
      ( edge-rooted-hom-combinator-Directed-Tree T T
        ( λ i → id-rooted-hom-Directed-Tree (T i))
        ( x)
        ( y)
        ( e)) ＝ e
  edge-id-rooted-hom-combinator-Directed-Tree ._ ._
    ( edge-to-root-combinator-Directed-Tree i) = refl
  edge-id-rooted-hom-combinator-Directed-Tree ._ ._
    ( edge-inclusion-combinator-Directed-Tree i x y e) = refl

  id-rooted-hom-combinator-Directed-Tree :
    htpy-hom-Directed-Tree
      ( combinator-Directed-Tree T)
      ( combinator-Directed-Tree T)
      ( hom-combinator-Directed-Tree T T
        ( λ i → id-rooted-hom-Directed-Tree (T i)))
      ( id-hom-Directed-Tree (combinator-Directed-Tree T))
  pr1 id-rooted-hom-combinator-Directed-Tree =
    node-id-rooted-hom-combinator-Directed-Tree
  pr2 id-rooted-hom-combinator-Directed-Tree =
    edge-id-rooted-hom-combinator-Directed-Tree
```

#### The action of the combinator on morphisms preserves composition

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level} {I : UU l1}
  (R : I → Directed-Tree l2 l3) (S : I → Directed-Tree l4 l5)
  (T : I → Directed-Tree l6 l7)
  (g : (i : I) → rooted-hom-Directed-Tree (S i) (T i))
  (f : (i : I) → rooted-hom-Directed-Tree (R i) (S i))
  where

  comp-rooted-hom-combinator-Directed-Tree :
    htpy-hom-Directed-Tree
      ( combinator-Directed-Tree R)
      ( combinator-Directed-Tree T)
      ( hom-combinator-Directed-Tree R T
        ( λ i → comp-rooted-hom-Directed-Tree (R i) (S i) (T i) (g i) (f i)))
      ( comp-hom-Directed-Tree
        ( combinator-Directed-Tree R)
        ( combinator-Directed-Tree S)
        ( combinator-Directed-Tree T)
        ( hom-combinator-Directed-Tree S T g)
        ( hom-combinator-Directed-Tree R S f))
  pr1 comp-rooted-hom-combinator-Directed-Tree root-combinator-Directed-Tree =
    refl
  pr1 comp-rooted-hom-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    refl
  pr2 comp-rooted-hom-combinator-Directed-Tree ._ ._
    ( edge-to-root-combinator-Directed-Tree i) =
    eq-is-contr
      ( is-proof-irrelevant-edge-to-root-Directed-Tree
        ( combinator-Directed-Tree T)
        ( node-comp-hom-Directed-Tree
          ( combinator-Directed-Tree R)
          ( combinator-Directed-Tree S)
          ( combinator-Directed-Tree T)
          ( hom-combinator-Directed-Tree S T g)
          ( hom-combinator-Directed-Tree R S f)
          ( node-inclusion-combinator-Directed-Tree i
            ( root-Directed-Tree (R i))))
        ( tr
          ( λ u →
            edge-combinator-Directed-Tree T u root-combinator-Directed-Tree)
          ( ap
            ( node-inclusion-combinator-Directed-Tree i)
            ( ( preserves-root-rooted-hom-Directed-Tree (S i) (T i) (g i)) ∙
              ( ap
                ( node-rooted-hom-Directed-Tree (S i) (T i) (g i))
                ( preserves-root-rooted-hom-Directed-Tree (R i) (S i) (f i)))))
          ( edge-to-root-combinator-Directed-Tree i)))
  pr2 comp-rooted-hom-combinator-Directed-Tree ._ ._
    ( edge-inclusion-combinator-Directed-Tree i x y e) =
    refl
```

#### The action of the combinator on morphisms preserves homotopies

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  (S : I → Directed-Tree l2 l3) (T : I → Directed-Tree l4 l5)
  (f g : (i : I) → rooted-hom-Directed-Tree (S i) (T i))
  (H : (i : I) → htpy-rooted-hom-Directed-Tree (S i) (T i) (f i) (g i))
  where

  node-htpy-hom-combinator-Directed-Tree :
    node-rooted-hom-combinator-Directed-Tree S T f ~
    node-rooted-hom-combinator-Directed-Tree S T g
  node-htpy-hom-combinator-Directed-Tree root-combinator-Directed-Tree = refl
  node-htpy-hom-combinator-Directed-Tree
    ( node-inclusion-combinator-Directed-Tree i x) =
    ap
      ( node-inclusion-combinator-Directed-Tree i)
      ( node-htpy-rooted-hom-Directed-Tree (S i) (T i) (f i) (g i) (H i) x)

  edge-htpy-hom-combinator-Directed-Tree :
    ( x y : node-combinator-Directed-Tree S)
    ( e : edge-combinator-Directed-Tree S x y) →
    binary-tr
      ( edge-combinator-Directed-Tree T)
      ( node-htpy-hom-combinator-Directed-Tree x)
      ( node-htpy-hom-combinator-Directed-Tree y)
      ( edge-rooted-hom-combinator-Directed-Tree S T f x y e) ＝
    edge-rooted-hom-combinator-Directed-Tree S T g x y e
  edge-htpy-hom-combinator-Directed-Tree ._ ._
    ( edge-to-root-combinator-Directed-Tree i) =
    eq-edge-to-root-Directed-Tree (combinator-Directed-Tree T) _ _ _
  edge-htpy-hom-combinator-Directed-Tree ._ ._
    ( edge-inclusion-combinator-Directed-Tree i x y e) =
    binary-tr-ap
      ( edge-combinator-Directed-Tree T)
      ( edge-inclusion-combinator-Directed-Tree i)
      ( node-htpy-rooted-hom-Directed-Tree (S i) (T i) (f i) (g i) (H i) x)
      ( node-htpy-rooted-hom-Directed-Tree (S i) (T i) (f i) (g i) (H i) y)
      ( edge-htpy-rooted-hom-Directed-Tree (S i) (T i) (f i) (g i) (H i) x y e)

  htpy-hom-combinator-Directed-Tree :
    htpy-hom-Directed-Tree
      ( combinator-Directed-Tree S)
      ( combinator-Directed-Tree T)
      ( hom-combinator-Directed-Tree S T f)
      ( hom-combinator-Directed-Tree S T g)
  pr1 htpy-hom-combinator-Directed-Tree =
    node-htpy-hom-combinator-Directed-Tree
  pr2 htpy-hom-combinator-Directed-Tree =
    edge-htpy-hom-combinator-Directed-Tree
```

### The action of the combinator on families of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  (S : I → Directed-Tree l2 l3) (T : I → Directed-Tree l4 l5)
  (f : (i : I) → equiv-Directed-Tree (S i) (T i))
  where

  rooted-hom-equiv-combinator-Directed-Tree :
    rooted-hom-Directed-Tree
      ( combinator-Directed-Tree S)
      ( combinator-Directed-Tree T)
  rooted-hom-equiv-combinator-Directed-Tree =
    rooted-hom-combinator-Directed-Tree S T
      ( λ i → rooted-hom-equiv-Directed-Tree (S i) (T i) (f i))

  hom-equiv-combinator-Directed-Tree :
    hom-Directed-Tree (combinator-Directed-Tree S) (combinator-Directed-Tree T)
  hom-equiv-combinator-Directed-Tree =
    hom-rooted-hom-Directed-Tree
      ( combinator-Directed-Tree S)
      ( combinator-Directed-Tree T)
      ( rooted-hom-equiv-combinator-Directed-Tree)

  node-equiv-combinator-Directed-Tree :
    node-combinator-Directed-Tree S → node-combinator-Directed-Tree T
  node-equiv-combinator-Directed-Tree =
    node-hom-Directed-Tree
      ( combinator-Directed-Tree S)
      ( combinator-Directed-Tree T)
      ( hom-equiv-combinator-Directed-Tree)

  edge-equiv-combinator-Directed-Tree :
    {x y : node-combinator-Directed-Tree S} →
    edge-combinator-Directed-Tree S x y →
    edge-combinator-Directed-Tree T
      ( node-equiv-combinator-Directed-Tree x)
      ( node-equiv-combinator-Directed-Tree y)
  edge-equiv-combinator-Directed-Tree =
    edge-hom-Directed-Tree
      ( combinator-Directed-Tree S)
      ( combinator-Directed-Tree T)
      ( hom-equiv-combinator-Directed-Tree)
```
