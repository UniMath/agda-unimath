# Pointed homotopies

```agda
module structured-types.pointed-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import foundation-core.torsorial-type-families

open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "pointed homotopy"}} between
[pointed dependent functions](structured-types.pointed-dependent-functions.md)
is a pointed dependent function of the
[pointed family](structured-types.pointed-families-of-types.md) of
[pointwise identifications](foundation-core.homotopies.md). The base point of
the family `x ↦ f₀ x ＝ g₀ x` over `A` is the identification

```text
  f₁ ∙ inv g₁ : f₀ * ＝ g₀ *.
```

A pointed homotopy `f ~∗ g` therefore consists of an unpointed homotopy `H₀ : f₀ ~ g₀` between
the underlying dependent functions and a
{{#concept "base point coherence" Disambiguation="pointed homotopy" Agda=preserves-base-point-uniform-pointed-htpy}},
which is an [identification](foundation-core.identity-types.md) witnessing that
the triangle of identifications

```text
        H₀ *
  f₀ * ------> g₀ *
      \       ∧
    f₀ \     / inv g₁
        \   /
         ∨ /
          *
```

[commutes](foundation.commuting-triangles-of-identifications.md).

Note that since pointed homotopies are defined for pointed dependent functions,
a pointed homotopy between pointed homotopies is just an instance of a pointed
homotopy. For this reason, we will also refer to the above definition of pointed homotopies as {{#concept "uniform pointed homotopies" Agda=uniform-pointed-homotopy}}.

A significant complication of this approach to the definition of pointed
homotopies is that identifications witnessing the commutativity of the triangle in a pointed homotopy is more complicated to construct than an identification witnessing that the triangle

```text
        H₀ *
  f₀ * ------> g₀ *
      \       /
    f₁ \     / g₁
        \   /
         ∨ ∨
          *.
```

commutes. Therefore we also introduce the type `uniform-pointed-htpy` of pointed homotopies, where the base point coherence takes this simpler form. The (nonuniform definition of pointed homotopies from `f` to `g` is therefore

```text
  Σ (H₀ : f₀ ~ g₀), f₁ ＝ (H₀ *) ∙ g₁
```

By transposing the commuting triangle of identifications in a pointed homotopy we directly obtain from each pointed homotopy a uniform pointed homotopy. This construction is an equivalence. By convention we will construct every uniform pointed homotopy this way.

We will see below that for pointed 2-homotopies, i.e., pointed homotopies between pointed homotopies, a significant simplification is possible by making sure that every identification faces in its uninverted direction. The only disadvantage of the nonuniform definition of pointed homotopies is that it does not easily iterate.

We will write `f ~∗ g` for the nonuniform definition of pointed homotopies, and we will write `H ~²∗ K` for the nonuniform definition of pointed 2-homotopies. Note that the definition `_~∗_` of pointed homotopies applies to all pointed dependent functions, but pointed homotopies `H : f ~∗ g` are not by definition pointed dependent functions.

## Definitions

### Unpointed homotopies between pointed dependent functions

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B)
  where

  unpointed-htpy-pointed-Π : UU (l1 ⊔ l2)
  unpointed-htpy-pointed-Π = function-pointed-Π f ~ function-pointed-Π g
```

### Unpointed homotopies between pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f g : A →∗ B)
  where

  unpointed-htpy-pointed-map : UU (l1 ⊔ l2)
  unpointed-htpy-pointed-map = map-pointed-map f ~ map-pointed-map g
```

### The base point coherence of unpointed homotopies between pointed maps

The coherence of pointed homotopies asserts that its underlying homotopy
preserves the base point, in the sense that the triangle of identifications

```text
                      H *
                f * ------> g *
                   \       /
  preserves-point f \     / preserves-point g
                     \   /
                      ∨ ∨
                       *
```

commutes.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (G : unpointed-htpy-pointed-Π f g)
  where

  coherence-point-unpointed-htpy-pointed-Π : UU l2
  coherence-point-unpointed-htpy-pointed-Π =
    coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( G (point-Pointed-Type A))
```

### Preservation of the base point of unpointed homotopies between pointed maps

The coherence of pointed homotopies asserts that its underlying homotopy
preserves the base point, in the sense that the triangle of identifications

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
    transpose-right-coherence-triangle-identifications _ _ _

  coherence-point-preserves-point-unpointed-htpy-pointed-Π :
    preserves-point-unpointed-htpy-pointed-Π →
    coherence-point-unpointed-htpy-pointed-Π f g G
  coherence-point-preserves-point-unpointed-htpy-pointed-Π =
    inv ∘ inv-right-transpose-eq-concat _ _ _
```

### Pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B)
  where

  pointed-htpy : UU (l1 ⊔ l2)
  pointed-htpy =
    Σ ( function-pointed-Π f ~ function-pointed-Π g)
      ( coherence-point-unpointed-htpy-pointed-Π f g)

  infix 6 _~∗_

  _~∗_ : UU (l1 ⊔ l2)
  _~∗_ = pointed-htpy

  module _
    (H : pointed-htpy)
    where

    htpy-pointed-htpy : function-pointed-Π f ~ function-pointed-Π g
    htpy-pointed-htpy = pr1 H

    coherence-point-pointed-htpy :
      coherence-point-unpointed-htpy-pointed-Π f g htpy-pointed-htpy
    coherence-point-pointed-htpy = pr2 H

    preserves-point-pointed-htpy :
      preserves-point-unpointed-htpy-pointed-Π f g htpy-pointed-htpy
    preserves-point-pointed-htpy =
      preserves-point-coherence-point-unpointed-htpy-pointed-Π f g
        ( htpy-pointed-htpy)
        ( coherence-point-pointed-htpy)
```

### The reflexive pointed homotopy

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  refl-pointed-htpy : pointed-htpy f f
  pr1 refl-pointed-htpy = refl-htpy
  pr2 refl-pointed-htpy = refl
```

### The uniform definition of pointed homotopies

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

  module _
    (H : uniform-pointed-htpy)
    where

    htpy-uniform-pointed-htpy :
      function-pointed-Π f ~ function-pointed-Π g
    htpy-uniform-pointed-htpy = pr1 H

    preserves-point-uniform-pointed-htpy :
      preserves-point-unpointed-htpy-pointed-Π f g htpy-uniform-pointed-htpy
    preserves-point-uniform-pointed-htpy = pr2 H

    coherence-point-uniform-pointed-htpy :
      coherence-point-unpointed-htpy-pointed-Π f g htpy-uniform-pointed-htpy
    coherence-point-uniform-pointed-htpy =
      coherence-point-preserves-point-unpointed-htpy-pointed-Π f g
        ( htpy-uniform-pointed-htpy)
        ( preserves-point-uniform-pointed-htpy)

  make-uniform-pointed-htpy :
    (G : unpointed-htpy-pointed-Π f g) →
    coherence-point-unpointed-htpy-pointed-Π f g G →
    uniform-pointed-htpy
  pr1 (make-uniform-pointed-htpy G p) = G
  pr2 (make-uniform-pointed-htpy G p) =
    preserves-point-coherence-point-unpointed-htpy-pointed-Π f g G p

  uniform-pointed-htpy-pointed-htpy : f ~∗ g → uniform-pointed-htpy
  pr1 (uniform-pointed-htpy-pointed-htpy H) = htpy-pointed-htpy f g H
  pr2 (uniform-pointed-htpy-pointed-htpy H) = preserves-point-pointed-htpy f g H

  pointed-htpy-uniform-pointed-htpy : uniform-pointed-htpy → f ~∗ g
  pr1 (pointed-htpy-uniform-pointed-htpy H) =
    htpy-uniform-pointed-htpy H
  pr2 (pointed-htpy-uniform-pointed-htpy H) =
    coherence-point-uniform-pointed-htpy H

  compute-uniform-pointed-htpy : (f ~∗ g) ≃ uniform-pointed-htpy
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

### Pointed 2-homotopies

Consider two pointed homotopies `H := (H₀ , H₁)` and `K := (K₀ , K₁)` between two pointed dependent functions `f := (f₀ , f₁)` and `g := (g₀ , g₁)` with base point coherences

```text
        H₀ *                        H₀ *
  f₀ * ------> g₀ *           f₀ * ------> g₀ *
      \       /                   \       ∧
    f₁ \  H₁ / g₁      and      f₁ \  H̃₁ / inv g₁
        \   /                       \   /
         ∨ ∨                         ∨ /
          *                           *
```

and

```text
        K₀ *                        K₀ *
  f₀ * ------> g₀ *           f₀ * ------> g₀ *
      \       /                   \       ∧
    f₁ \  K₁ / g₁      and      f₁ \  K̃₁ / inv g₁
        \   /                       \   /
         ∨ ∨                         ∨ /
          *                           *,
```

where

```text
  H̃₁ := coherence-triangle-inv-right f₁ g₁ (H₀ *) H₁
  K̃₁ := coherence-triangle-inv-right f₁ g₁ (K₀ *) K₁
```

A pointed homotopy `H ~∗ K` then consists of an unpointed homotopy `α₀ : H₀ ~ K₀` and an identification witnessing that the triangle

```text
        H₁
  f₁ ------> (H₀ *) ∙ g₁
    \       /
  K₁ \     / right-whisker-concat (α₀ *) ∙ g₁
      \   /
       ∨ ∨
   (K₀ *) ∙ g₁
```

commutes. Equivalently, following equivalence of pointed homotopies and uniform pointed homotopies, a uniform pointed 2-homotopy consists of  an unpointed homotopy `α₀ : H₀ ~ K₀` is and an identification witnessing that `α₀` preserves the base point, i.e., witnessing that the triangle

```text
        α₀ *
  H₀ * ------> K₀ *
      \       ∧
    H̃₁ \     / inv K̃₁
        \   /
         ∨ /
       f₁ ∙ inv g₁
```

commutes.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H K : pointed-htpy f g)
  where

  unpointed-htpy-pointed-htpy : UU (l1 ⊔ l2)
  unpointed-htpy-pointed-htpy =
    htpy-pointed-htpy f g H ~ htpy-pointed-htpy f g K

  coherence-point-unpointed-htpy-pointed-htpy :
    unpointed-htpy-pointed-htpy → UU l2
  coherence-point-unpointed-htpy-pointed-htpy α =
    coherence-triangle-identifications
      ( coherence-point-pointed-htpy f g K)
      ( right-whisker-concat
        ( α (point-Pointed-Type A))
        ( preserves-point-function-pointed-Π g))
      ( coherence-point-pointed-htpy f g H)

  pointed-2-htpy : UU (l1 ⊔ l2)
  pointed-2-htpy =
    Σ unpointed-htpy-pointed-htpy coherence-point-unpointed-htpy-pointed-htpy

  module _
    (α : pointed-2-htpy)
    where

    htpy-pointed-2-htpy : unpointed-htpy-pointed-htpy
    htpy-pointed-2-htpy = pr1 α

    coherence-point-pointed-2-htpy :
      coherence-point-unpointed-htpy-pointed-htpy htpy-pointed-2-htpy
    coherence-point-pointed-2-htpy = pr2 α

    preserves-point-pointed-2-htpy :
      preserves-point-unpointed-htpy-pointed-Π
        ( make-uniform-pointed-htpy f g
          ( htpy-pointed-htpy f g H)
          ( coherence-point-pointed-htpy f g H))
        ( make-uniform-pointed-htpy f g
          ( htpy-pointed-htpy f g K)
          ( coherence-point-pointed-htpy f g K))
        ( htpy-pointed-2-htpy)
    preserves-point-pointed-2-htpy =
      transpose-right-coherence-triangle-identifications
        ( htpy-pointed-2-htpy (point-Pointed-Type A))
        ( preserves-point-pointed-htpy f g K)
        ( preserves-point-pointed-htpy f g H)
        ( higher-transpose-right-coherence-triangle-identifications
          ( htpy-pointed-htpy f g H (point-Pointed-Type A))
          ( preserves-point-function-pointed-Π g)
          ( preserves-point-function-pointed-Π f)
          ( htpy-pointed-2-htpy (point-Pointed-Type A))
          ( coherence-point-pointed-htpy f g H)
          ( coherence-point-pointed-htpy f g K)
          ( coherence-point-pointed-2-htpy))

    uniform-pointed-htpy-pointed-2-htpy :
      uniform-pointed-htpy
        ( uniform-pointed-htpy-pointed-htpy f g H)
        ( uniform-pointed-htpy-pointed-htpy f g K)
    pr1 uniform-pointed-htpy-pointed-2-htpy =
      htpy-pointed-2-htpy
    pr2 uniform-pointed-htpy-pointed-2-htpy =
      preserves-point-pointed-2-htpy
```

### The reflexive pointed 2-homotopy

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (H : f ~∗ g)
  where

  htpy-refl-pointed-2-htpy : unpointed-htpy-pointed-htpy H H
  htpy-refl-pointed-2-htpy = refl-htpy

  coherence-point-refl-pointed-2-htpy :
    coherence-point-unpointed-htpy-pointed-htpy H H
      ( htpy-refl-pointed-2-htpy)
  coherence-point-refl-pointed-2-htpy = inv right-unit

  refl-pointed-2-htpy : pointed-2-htpy H H
  pr1 refl-pointed-2-htpy = htpy-refl-pointed-2-htpy
  pr2 refl-pointed-2-htpy = coherence-point-refl-pointed-2-htpy
```

## Properties

### Extensionality of pointed dependent function types by pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  abstract
    is-torsorial-pointed-htpy :
      is-torsorial (pointed-htpy f)
    is-torsorial-pointed-htpy =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy _)
        ( function-pointed-Π f , refl-htpy)
        ( is-torsorial-Id _)

  pointed-htpy-eq :
    (g : pointed-Π A B) → f ＝ g → f ~∗ g
  pointed-htpy-eq .f refl = refl-pointed-htpy f

  abstract
    is-equiv-pointed-htpy-eq :
      (g : pointed-Π A B) → is-equiv (pointed-htpy-eq g)
    is-equiv-pointed-htpy-eq =
      fundamental-theorem-id
        ( is-torsorial-pointed-htpy)
        ( pointed-htpy-eq)

  extensionality-pointed-Π :
    (g : pointed-Π A B) → (f ＝ g) ≃ (f ~∗ g)
  pr1 (extensionality-pointed-Π g) = pointed-htpy-eq g
  pr2 (extensionality-pointed-Π g) = is-equiv-pointed-htpy-eq g

  eq-pointed-htpy :
    (g : pointed-Π A B) → f ~∗ g → f ＝ g
  eq-pointed-htpy g = map-inv-equiv (extensionality-pointed-Π g)
```

### Extensionality of pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B)
  where

  extensionality-pointed-map :
    (g : A →∗ B) → (f ＝ g) ≃ (f ~∗ g)
  extensionality-pointed-map = extensionality-pointed-Π f
```

### Extensionality of pointed dependent function types by uniform pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  uniform-extensionality-pointed-Π :
    (g : pointed-Π A B) → Id f g ≃ uniform-pointed-htpy f g
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
    (g : pointed-Π A B) → uniform-pointed-htpy f g → Id f g
  eq-uniform-pointed-htpy g = map-inv-equiv (uniform-extensionality-pointed-Π g)
```

### Extensionality of pointed 2-homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (H : f ~∗ g)
  where

  is-torsorial-pointed-2-htpy :
    is-torsorial (pointed-2-htpy H)
  is-torsorial-pointed-2-htpy =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy _)
      ( htpy-pointed-htpy f g H , refl-htpy)
      ( is-torsorial-Id' _)

  pointed-2-htpy-eq : (K : f ~∗ g) → H ＝ K → pointed-2-htpy H K
  pointed-2-htpy-eq .H refl = refl-pointed-2-htpy f g H

  is-equiv-pointed-2-htpy-eq :
    (K : f ~∗ g) → is-equiv (pointed-2-htpy-eq K)
  is-equiv-pointed-2-htpy-eq =
    fundamental-theorem-id
      ( is-torsorial-pointed-2-htpy)
      ( pointed-2-htpy-eq)

  extensionality-pointed-htpy :
    (K : f ~∗ g) → (H ＝ K) ≃ pointed-2-htpy H K
  pr1 (extensionality-pointed-htpy K) = pointed-2-htpy-eq K
  pr2 (extensionality-pointed-htpy K) = is-equiv-pointed-2-htpy-eq K

  eq-pointed-2-htpy :
    (K : f ~∗ g) → pointed-2-htpy H K → H ＝ K
  eq-pointed-2-htpy K = map-inv-equiv (extensionality-pointed-htpy K)
```

### Concatenation of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g h : pointed-Π A B} (G : f ~∗ g) (H : g ~∗ h)
  where

  htpy-concat-pointed-htpy : unpointed-htpy-pointed-Π f h
  htpy-concat-pointed-htpy = htpy-pointed-htpy f g G ∙h htpy-pointed-htpy g h H

  coherence-point-concat-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π f h htpy-concat-pointed-htpy
  coherence-point-concat-pointed-htpy =
    horizontal-pasting-coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( preserves-point-function-pointed-Π h)
      ( htpy-pointed-htpy f g G (point-Pointed-Type A))
      ( htpy-pointed-htpy g h H (point-Pointed-Type A))
      ( coherence-point-pointed-htpy f g G)
      ( coherence-point-pointed-htpy g h H)

  concat-pointed-htpy : f ~∗ h
  pr1 concat-pointed-htpy = htpy-concat-pointed-htpy
  pr2 concat-pointed-htpy = coherence-point-concat-pointed-htpy
```

### Concatenation of uniform pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g h : pointed-Π A B)
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
      ( pointed-htpy-uniform-pointed-htpy f g G)
      ( pointed-htpy-uniform-pointed-htpy g h H)

  concat-uniform-pointed-htpy : uniform-pointed-htpy f h
  concat-uniform-pointed-htpy =
    make-uniform-pointed-htpy f h
      ( htpy-concat-uniform-pointed-htpy)
      ( coherence-point-concat-uniform-pointed-htpy)
```

### Inverses of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (H : f ~∗ g)
  where

  htpy-inv-pointed-htpy : unpointed-htpy-pointed-Π g f
  htpy-inv-pointed-htpy = inv-htpy (htpy-pointed-htpy f g H)

  coherence-point-inv-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π g f htpy-inv-pointed-htpy
  coherence-point-inv-pointed-htpy =
    transpose-top-coherence-triangle-identifications
      ( preserves-point-function-pointed-Π g)
      ( preserves-point-function-pointed-Π f)
      ( htpy-pointed-htpy f g H (point-Pointed-Type A))
      ( coherence-point-pointed-htpy f g H)

  inv-pointed-htpy : g ~∗ f
  pr1 inv-pointed-htpy = htpy-inv-pointed-htpy
  pr2 inv-pointed-htpy = coherence-point-inv-pointed-htpy
```

### Inverses of uniform pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (H : uniform-pointed-htpy f g)
  where

  htpy-inv-uniform-pointed-htpy : unpointed-htpy-pointed-Π g f
  htpy-inv-uniform-pointed-htpy = inv-htpy (htpy-uniform-pointed-htpy f g H)

  coherence-point-inv-uniform-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π g f htpy-inv-uniform-pointed-htpy
  coherence-point-inv-uniform-pointed-htpy =
    coherence-point-inv-pointed-htpy f g
      ( pointed-htpy-uniform-pointed-htpy f g H)

  inv-uniform-pointed-htpy : uniform-pointed-htpy g f
  inv-uniform-pointed-htpy =
    make-uniform-pointed-htpy g f
      ( htpy-inv-uniform-pointed-htpy)
      ( coherence-point-inv-uniform-pointed-htpy)
```

### Associativity of composition of pointed maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {C : Pointed-Type l3} {D : Pointed-Type l4}
  (h : C →∗ D) (g : B →∗ C) (f : A →∗ B)
  where

  htpy-inv-associative-comp-pointed-map :
    unpointed-htpy-pointed-Π (h ∘∗ (g ∘∗ f)) ((h ∘∗ g) ∘∗ f)
  htpy-inv-associative-comp-pointed-map = refl-htpy

  coherence-point-inv-associative-comp-pointed-map :
    coherence-point-unpointed-htpy-pointed-Π
      ( h ∘∗ (g ∘∗ f))
      ( (h ∘∗ g) ∘∗ f)
      ( htpy-inv-associative-comp-pointed-map)
  coherence-point-inv-associative-comp-pointed-map =
    right-whisker-concat-coherence-triangle-identifications
      ( ap
        ( map-pointed-map h)
        ( ( ap
            ( map-pointed-map g)
            ( preserves-point-pointed-map f)) ∙
          ( preserves-point-pointed-map g)))
      ( ap (map-pointed-map h) _)
      ( ap (map-comp-pointed-map h g) (preserves-point-pointed-map f))
      ( preserves-point-pointed-map h)
      ( ( ap-concat
          ( map-pointed-map h)
          ( ap (map-pointed-map g) (preserves-point-pointed-map f))
          ( preserves-point-pointed-map g)) ∙
        ( inv
          ( right-whisker-concat
            ( ap-comp
              ( map-pointed-map h)
              ( map-pointed-map g)
              ( preserves-point-pointed-map f))
            ( ap (map-pointed-map h) (preserves-point-pointed-map g)))))

  inv-associative-comp-pointed-map :
    h ∘∗ (g ∘∗ f) ~∗ (h ∘∗ g) ∘∗ f
  pr1 inv-associative-comp-pointed-map =
    htpy-inv-associative-comp-pointed-map
  pr2 inv-associative-comp-pointed-map =
    coherence-point-inv-associative-comp-pointed-map

  htpy-associative-comp-pointed-map :
    unpointed-htpy-pointed-Π ((h ∘∗ g) ∘∗ f) (h ∘∗ (g ∘∗ f))
  htpy-associative-comp-pointed-map = refl-htpy

  coherence-associative-comp-pointed-map :
    coherence-point-unpointed-htpy-pointed-Π
      ( (h ∘∗ g) ∘∗ f)
      ( h ∘∗ (g ∘∗ f))
      ( htpy-associative-comp-pointed-map)
  coherence-associative-comp-pointed-map =
    inv coherence-point-inv-associative-comp-pointed-map

  associative-comp-pointed-map :
    (h ∘∗ g) ∘∗ f ~∗ h ∘∗ (g ∘∗ f)
  pr1 associative-comp-pointed-map =
    htpy-associative-comp-pointed-map
  pr2 associative-comp-pointed-map =
    coherence-associative-comp-pointed-map
```

### The left unit law for composition of pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  htpy-left-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-left-unit-law-comp-pointed-map = refl-htpy

  coherence-left-unit-law-comp-pointed-map :
    coherence-point-unpointed-htpy-pointed-Π
      ( id-pointed-map ∘∗ f)
      ( f)
      ( htpy-left-unit-law-comp-pointed-map)
  coherence-left-unit-law-comp-pointed-map =
    right-unit ∙ ap-id (preserves-point-pointed-map f)

  left-unit-law-comp-pointed-map : id-pointed-map ∘∗ f ~∗ f
  pr1 left-unit-law-comp-pointed-map = htpy-left-unit-law-comp-pointed-map
  pr2 left-unit-law-comp-pointed-map = coherence-left-unit-law-comp-pointed-map

  htpy-inv-left-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-inv-left-unit-law-comp-pointed-map = refl-htpy

  coherence-point-inv-left-unit-law-comp-pointed-map :
    coherence-point-unpointed-htpy-pointed-Π
      ( f)
      ( id-pointed-map ∘∗ f)
      ( htpy-inv-left-unit-law-comp-pointed-map)
  coherence-point-inv-left-unit-law-comp-pointed-map =
    inv coherence-left-unit-law-comp-pointed-map

  inv-left-unit-law-comp-pointed-map : f ~∗ id-pointed-map ∘∗ f
  pr1 inv-left-unit-law-comp-pointed-map =
    htpy-inv-left-unit-law-comp-pointed-map
  pr2 inv-left-unit-law-comp-pointed-map =
    coherence-point-inv-left-unit-law-comp-pointed-map
```

### The right unit law for composition of pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  htpy-right-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-right-unit-law-comp-pointed-map = refl-htpy

  coherence-right-unit-law-comp-pointed-map :
    coherence-point-unpointed-htpy-pointed-Π
      ( f ∘∗ id-pointed-map)
      ( f)
      ( htpy-right-unit-law-comp-pointed-map)
  coherence-right-unit-law-comp-pointed-map = refl

  right-unit-law-comp-pointed-map : f ∘∗ id-pointed-map ~∗ f
  pr1 right-unit-law-comp-pointed-map =
    htpy-right-unit-law-comp-pointed-map
  pr2 right-unit-law-comp-pointed-map =
    coherence-right-unit-law-comp-pointed-map
```

### Associativity of concatenation of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g h k : pointed-Π A B} (G : f ~∗ g) (H : g ~∗ h) (K : h ~∗ k)
  where

  htpy-associative-concat-pointed-htpy :
    htpy-pointed-htpy f k
      ( concat-pointed-htpy (concat-pointed-htpy G H) K) ~
    htpy-pointed-htpy f k
      ( concat-pointed-htpy G (concat-pointed-htpy H K))
  htpy-associative-concat-pointed-htpy =
    assoc-htpy
      ( htpy-pointed-htpy f g G)
      ( htpy-pointed-htpy g h H)
      ( htpy-pointed-htpy h k K)

  coherence-associative-concat-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy (concat-pointed-htpy G H) K)
      ( concat-pointed-htpy G (concat-pointed-htpy H K))
      ( htpy-associative-concat-pointed-htpy)
  coherence-associative-concat-pointed-htpy =
    associative-horizontal-pasting-coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( preserves-point-function-pointed-Π h)
      ( preserves-point-function-pointed-Π k)
      ( htpy-pointed-htpy f g G _)
      ( htpy-pointed-htpy g h H _)
      ( htpy-pointed-htpy h k K _)
      ( coherence-point-pointed-htpy f g G)
      ( coherence-point-pointed-htpy g h H)
      ( coherence-point-pointed-htpy h k K)

  associative-concat-pointed-htpy :
    pointed-2-htpy
      ( concat-pointed-htpy (concat-pointed-htpy G H) K)
      ( concat-pointed-htpy G (concat-pointed-htpy H K))
  pr1 associative-concat-pointed-htpy =
    htpy-associative-concat-pointed-htpy
  pr2 associative-concat-pointed-htpy =
    coherence-associative-concat-pointed-htpy
```
