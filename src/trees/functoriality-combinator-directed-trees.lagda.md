# Functoriality of the combinator of directed trees

```agda
module trees.functoriality-combinator-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import trees.combinator-directed-trees
open import trees.directed-trees
open import trees.morphisms-directed-trees
open import trees.rooted-morphisms-directed-trees
```

</details>

## Idea

Given a family of rooted morphisms `fᵢ : Sᵢ → Tᵢ` of directed trees, we obtain a morphism

```md
  combinator f : combinator S → combinator T
```

of directed trees. Furthermore, `f` is a family of equivalences of directed trees if and only if `combinator f` is an equivalence, and moreover this induces an equivlence between families of equivalences `Sᵢ ≃ Tᵢ` and equivalences `combinator S ≃ combinator T`.

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
        ( inv
          ( preserves-root-rooted-hom-Directed-Tree (S i) (T i) (f i))))
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
