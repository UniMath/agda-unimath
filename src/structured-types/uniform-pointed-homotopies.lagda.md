# Uniform pointed homotopies

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.uniform-pointed-homotopies
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-identifications funext
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.function-extensionality funext
open import foundation.function-types funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import structured-types.pointed-dependent-functions funext
open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies funext univalence truncations
open import structured-types.pointed-maps funext univalence truncations
open import structured-types.pointed-types
```

</details>

## Idea

The concept of _uniform pointed homotopy_ is an
[equivalent](foundation-core.equivalences.md) way of defining
[pointed homotopies](structured-types.pointed-homotopies.md). A uniform pointed
homotopy `H` between two
[pointed dependent functions](structured-types.pointed-dependent-functions.md)
`f` and `g` is defined to be a pointed dependent function of the
[pointed type family](structured-types.pointed-families-of-types.md) of
[identifications](foundation-core.identity-types.md) between the values of `f`
and `g`. The main idea is that, since uniform pointed homotopies between pointed
dependent functions are again pointed dependent functions, we can easily
consider uniform pointed homotopies between uniform pointed homotopies and so
on. The definition of uniform pointed homotopies is uniform in the sense that
they can be iterated in this way. We now give a more detailed description of the
definition.

Consider two pointed dependent functions `f := (f₀ , f₁)` and `g := (g₀ , g₁)`
in the pointed dependent function type `Π∗ A B`. Then the type family
`x ↦ f₀ x ＝ g₀ x` over the base type `A` is a pointed type family, where the
base point is the identification

```text
  f₁ ∙ inv g₁ : f₀ * ＝ g₀ *.
```

A {{#concept "uniform pointed homotopy" Agda=uniform-pointed-htpy}} from `f` to
`g` is defined to be a
[pointed dependent function](structured-types.pointed-dependent-functions.md) of
the pointed type family `x ↦ f₀ x ＝ g₀ x`. In other words, a pointed dependent
function consists of an unpointed [homotopy](foundation-core.homotopies.md)
`H₀ : f₀ ~ g₀` between the underlying dependent functions and an identification
witnessing that the triangle of identifications

```text
        H₀ *
  f₀ * ------> g₀ *
      \       ∧
    f₁ \     / inv g₁
        \   /
         ∨ /
          *
```

[commutes](foundation.commuting-triangles-of-identifications.md).

Notice that in comparison to the pointed homotopies, the identification on the
right in this triangle goes up, in the inverse direction of the identification
`g₁`. This makes it slightly more complicated to construct an identification
witnessing that the triangle commutes in the case of uniform pointed homotopies.
Furthermore, this complication becomes more significant and bothersome when we
are trying to construct a
[pointed `2`-homotopy](structured-types.pointed-2-homotopies.md).

## Definitions

### Preservation of the base point of unpointed homotopies between pointed maps

The underlying homotopy of a uniform pointed homotopy preserves the base point
in the sense that the triangle of identifications

```text
                      H *
                f * ------> g *
                   \       ∧
  preserves-point f \     / inv (preserves-point g)
                     \   /
                      ∨ /
                       *
```

commutes.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (G : unpointed-htpy-pointed-Π f g)
  where

  preserves-point-unpointed-htpy-pointed-Π : UU l2
  preserves-point-unpointed-htpy-pointed-Π =
    coherence-triangle-identifications
      ( G (point-Pointed-Type A))
      ( inv (preserves-point-function-pointed-Π g))
      ( preserves-point-function-pointed-Π f)

  compute-coherence-point-unpointed-htpy-pointed-Π :
    coherence-point-unpointed-htpy-pointed-Π f g G ≃
    preserves-point-unpointed-htpy-pointed-Π
  compute-coherence-point-unpointed-htpy-pointed-Π =
    equiv-transpose-right-coherence-triangle-identifications _ _ _

  preserves-point-coherence-point-unpointed-htpy-pointed-Π :
    coherence-point-unpointed-htpy-pointed-Π f g G →
    preserves-point-unpointed-htpy-pointed-Π
  preserves-point-coherence-point-unpointed-htpy-pointed-Π =
    transpose-right-coherence-triangle-identifications _ _ _ refl

  coherence-point-preserves-point-unpointed-htpy-pointed-Π :
    preserves-point-unpointed-htpy-pointed-Π →
    coherence-point-unpointed-htpy-pointed-Π f g G
  coherence-point-preserves-point-unpointed-htpy-pointed-Π =
    inv ∘ inv-right-transpose-eq-concat _ _ _

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H : f ~∗ g)
  where

  preserves-point-pointed-htpy :
    preserves-point-unpointed-htpy-pointed-Π f g (htpy-pointed-htpy H)
  preserves-point-pointed-htpy =
    preserves-point-coherence-point-unpointed-htpy-pointed-Π f g
      ( htpy-pointed-htpy H)
      ( coherence-point-pointed-htpy H)
```

### Uniform pointed homotopies

**Note.** The operation `htpy-uniform-pointed-htpy` that converts a uniform
pointed homotopy to an unpointed homotopy is set up with the pointed functions
as explicit arguments, because Agda has trouble inferring them.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B)
  where

  eq-value-Pointed-Fam : Pointed-Fam l2 A
  pr1 eq-value-Pointed-Fam =
    eq-value (function-pointed-Π f) (function-pointed-Π g)
  pr2 eq-value-Pointed-Fam =
    ( preserves-point-function-pointed-Π f) ∙
    ( inv (preserves-point-function-pointed-Π g))

  uniform-pointed-htpy : UU (l1 ⊔ l2)
  uniform-pointed-htpy = pointed-Π A eq-value-Pointed-Fam

  htpy-uniform-pointed-htpy :
    uniform-pointed-htpy → function-pointed-Π f ~ function-pointed-Π g
  htpy-uniform-pointed-htpy = pr1

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B}
  (H : uniform-pointed-htpy f g)
  where

  preserves-point-uniform-pointed-htpy :
    preserves-point-unpointed-htpy-pointed-Π f g
      ( htpy-uniform-pointed-htpy f g H)
  preserves-point-uniform-pointed-htpy = pr2 H

  coherence-point-uniform-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π f g
      ( htpy-uniform-pointed-htpy f g H)
  coherence-point-uniform-pointed-htpy =
    coherence-point-preserves-point-unpointed-htpy-pointed-Π f g
      ( htpy-uniform-pointed-htpy f g H)
      ( preserves-point-uniform-pointed-htpy)

  pointed-htpy-uniform-pointed-htpy : f ~∗ g
  pr1 pointed-htpy-uniform-pointed-htpy =
    htpy-uniform-pointed-htpy f g H
  pr2 pointed-htpy-uniform-pointed-htpy =
    coherence-point-uniform-pointed-htpy

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B}
  where

  make-uniform-pointed-htpy :
    (G : unpointed-htpy-pointed-Π f g) →
    coherence-point-unpointed-htpy-pointed-Π f g G →
    uniform-pointed-htpy f g
  pr1 (make-uniform-pointed-htpy G p) = G
  pr2 (make-uniform-pointed-htpy G p) =
    preserves-point-coherence-point-unpointed-htpy-pointed-Π f g G p

  uniform-pointed-htpy-pointed-htpy : f ~∗ g → uniform-pointed-htpy f g
  pr1 (uniform-pointed-htpy-pointed-htpy H) = htpy-pointed-htpy H
  pr2 (uniform-pointed-htpy-pointed-htpy H) = preserves-point-pointed-htpy H

  compute-uniform-pointed-htpy : (f ~∗ g) ≃ uniform-pointed-htpy f g
  compute-uniform-pointed-htpy =
    equiv-tot (compute-coherence-point-unpointed-htpy-pointed-Π f g)
```

### The reflexive uniform pointed homotopy

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  refl-uniform-pointed-htpy : uniform-pointed-htpy f f
  pr1 refl-uniform-pointed-htpy = refl-htpy
  pr2 refl-uniform-pointed-htpy =
    inv (right-inv (preserves-point-function-pointed-Π f))
```

### Concatenation of uniform pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g h : pointed-Π A B}
  (G : uniform-pointed-htpy f g) (H : uniform-pointed-htpy g h)
  where

  htpy-concat-uniform-pointed-htpy : unpointed-htpy-pointed-Π f h
  htpy-concat-uniform-pointed-htpy =
    htpy-uniform-pointed-htpy f g G ∙h htpy-uniform-pointed-htpy g h H

  coherence-point-concat-uniform-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π f h
      ( htpy-concat-uniform-pointed-htpy)
  coherence-point-concat-uniform-pointed-htpy =
    coherence-point-concat-pointed-htpy
      ( pointed-htpy-uniform-pointed-htpy G)
      ( pointed-htpy-uniform-pointed-htpy H)

  concat-uniform-pointed-htpy : uniform-pointed-htpy f h
  concat-uniform-pointed-htpy =
    make-uniform-pointed-htpy
      ( htpy-concat-uniform-pointed-htpy)
      ( coherence-point-concat-uniform-pointed-htpy)
```

### Inverses of uniform pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H : uniform-pointed-htpy f g)
  where

  htpy-inv-uniform-pointed-htpy : unpointed-htpy-pointed-Π g f
  htpy-inv-uniform-pointed-htpy = inv-htpy (htpy-uniform-pointed-htpy f g H)

  coherence-point-inv-uniform-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π g f htpy-inv-uniform-pointed-htpy
  coherence-point-inv-uniform-pointed-htpy =
    coherence-point-inv-pointed-htpy
      ( pointed-htpy-uniform-pointed-htpy H)

  inv-uniform-pointed-htpy : uniform-pointed-htpy g f
  inv-uniform-pointed-htpy =
    make-uniform-pointed-htpy
      ( htpy-inv-uniform-pointed-htpy)
      ( coherence-point-inv-uniform-pointed-htpy)
```

## Properties

### Extensionality of pointed dependent function types by uniform pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  uniform-extensionality-pointed-Π :
    (g : pointed-Π A B) → (f ＝ g) ≃ uniform-pointed-htpy f g
  uniform-extensionality-pointed-Π =
    extensionality-Σ
      ( λ {g} q H →
        H (point-Pointed-Type A) ＝
        preserves-point-function-pointed-Π f ∙
        inv (preserves-point-function-pointed-Π (g , q)))
      ( refl-htpy)
      ( inv (right-inv (preserves-point-function-pointed-Π f)))
      ( λ g → equiv-funext)
      ( λ p →
        ( equiv-right-transpose-eq-concat
          ( refl)
          ( p)
          ( preserves-point-function-pointed-Π f)) ∘e
        ( equiv-inv (preserves-point-function-pointed-Π f) p))

  eq-uniform-pointed-htpy :
    (g : pointed-Π A B) → uniform-pointed-htpy f g → f ＝ g
  eq-uniform-pointed-htpy g = map-inv-equiv (uniform-extensionality-pointed-Π g)
```
