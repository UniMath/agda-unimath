# Freely generated left modules over rings

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.freely-generated-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.equivalences
open import foundation.universe-levels

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.universal-property-free-left-modules-rings

open import ring-theory.rings

open import universal-algebra.algebraic-theory-of-left-modules-rings
open import universal-algebra.freely-generated-algebras
open import universal-algebra.isomorphisms-of-algebras
open import universal-algebra.precategory-of-algebras-algebraic-theories
open import universal-algebra.universal-property-freely-generated-algebras
```

</details>

## Idea

The
{{#concept "freely generated left module" Disambiguation="over a ring" Agda=free-left-module-Ring}}
over a [ring](ring-theory.rings.md) `R` with generator type `G` is a canonical
construction of a [left module](linear-algebra.left-modules-rings.md) satisfying
the
[universal property of freely generated left modules](linear-algebra.universal-property-free-left-modules-rings.md).
Notably, this is equivalent to the direct sum of copies of `R` as a module over
itself indexed by `G`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (G : UU l2)
  where

  algebra-free-left-module-Ring : Algebra-Left-Module-Ring (l1 ⊔ l2) R
  algebra-free-left-module-Ring =
    free-Algebra
      ( signature-left-module-Ring R)
      ( algebraic-theory-left-module-Ring R)
      ( G)

  opaque
    free-left-module-Ring : left-module-Ring (l1 ⊔ l2) R
    free-left-module-Ring =
      left-module-Algebra-Left-Module-Ring R algebra-free-left-module-Ring

  type-free-left-module-Ring : UU (l1 ⊔ l2)
  type-free-left-module-Ring =
    type-left-module-Ring R free-left-module-Ring

  opaque
    unfolding free-left-module-Ring

    in-free-left-module-Ring : G → type-free-left-module-Ring
    in-free-left-module-Ring =
      in-generator-free-Algebra
        ( signature-left-module-Ring R)
        ( algebraic-theory-left-module-Ring R)
        ( G)

    is-free-free-left-module-Ring :
      is-free-left-module-Ring R G
        ( free-left-module-Ring)
        ( in-free-left-module-Ring)
    is-free-free-left-module-Ring N =
      is-equiv-map-equiv
        ( equivalence-reasoning
          linear-map-left-module-Ring R free-left-module-Ring N
          ≃ hom-Algebra-Left-Module-Ring R
              ( algebra-left-module-left-module-Ring R free-left-module-Ring)
              ( algebra-left-module-left-module-Ring R N)
            by equiv-linear-map-hom-algebra-Left-Module-Ring R _ N
          ≃ hom-Algebra-Left-Module-Ring R
              ( algebra-free-left-module-Ring)
              ( algebra-left-module-left-module-Ring R N)
            by
              equiv-precomp-hom-iso-Large-Precategory
                ( Algebra-Large-Precategory
                  ( signature-left-module-Ring R)
                  ( algebraic-theory-left-module-Ring R))
                ( inv-iso-Algebra
                  ( signature-left-module-Ring R)
                  ( algebraic-theory-left-module-Ring R)
                  ( _)
                  ( _)
                  ( iso-is-section-left-module-Algebra-Left-Module-Ring
                    ( R)
                    ( algebra-free-left-module-Ring)))
                ( algebra-left-module-left-module-Ring R N)
          ≃ (G → type-left-module-Ring R N)
            by
              equiv-free-Algebra
                ( signature-left-module-Ring R)
                ( algebraic-theory-left-module-Ring R)
                ( G)
                ( algebra-left-module-left-module-Ring R N))
```
