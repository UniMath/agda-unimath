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
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

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
{{#concept "base point coherence" Disambiguation="pointed homotopy" Agda=preserves-base-point-pointed-htpy}},
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

commutes. Therefore we also introduce the type `pointed-htpy` of pointed homotopies, where the base point coherence takes this simpler form. The (nonuniform definition of pointed homotopies from `f` to `g` is therefore

```text
  Σ (H₀ : f₀ ~ g₀), f₁ ＝ (H₀ *) ∙ g₁
```

By transposing the commuting triangle of identifications in a pointed homotopy we directly obtain from each pointed homotopy a uniform pointed homotopy. This construction is an equivalence. By convention we will construct every uniform pointed homotopy this way.

We will see below that for pointed 2-homotopies, i.e., pointed homotopies between pointed homotopies, a significant simplification is possible by making sure that every identification faces in its uninverted direction. The only disadvantage of the nonuniform definition of pointed homotopies is that it does not easily iterate.

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

### The coherence of pointed homotopies

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

  coherence-point-unpointed-htpy-pointed-Π : UU l2
  coherence-point-unpointed-htpy-pointed-Π =
    coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( G (point-Pointed-Type A))

  compute-coherence-point-unpointed-htpy-pointed-Π :
    coherence-point-unpointed-htpy-pointed-Π ≃
    preserves-point-unpointed-htpy-pointed-Π
  compute-coherence-point-unpointed-htpy-pointed-Π =
    equiv-transpose-right-coherence-triangle-identifications _ _ _

  preserves-point-coherence-point-unpointed-htpy-pointed-Π :
    coherence-point-unpointed-htpy-pointed-Π →
    preserves-point-unpointed-htpy-pointed-Π
  preserves-point-coherence-point-unpointed-htpy-pointed-Π =
    transpose-right-coherence-triangle-identifications _ _ _

  coherence-point-preserves-point-unpointed-htpy-pointed-Π :
    preserves-point-unpointed-htpy-pointed-Π →
    coherence-point-unpointed-htpy-pointed-Π
  coherence-point-preserves-point-unpointed-htpy-pointed-Π =
    inv ∘ inv-right-transpose-eq-concat _ _ _
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

  infix 6 _~∗_

  _~∗_ : UU (l1 ⊔ l2)
  _~∗_ = uniform-pointed-htpy

  module _
    (H : uniform-pointed-htpy)
    where

    htpy-pointed-htpy :
      function-pointed-Π f ~ function-pointed-Π g
    htpy-pointed-htpy = pr1 H

    preserves-point-pointed-htpy :
      preserves-point-unpointed-htpy-pointed-Π f g htpy-pointed-htpy
    preserves-point-pointed-htpy = pr2 H

    coherence-point-pointed-htpy :
      coherence-point-unpointed-htpy-pointed-Π f g htpy-pointed-htpy
    coherence-point-pointed-htpy =
      coherence-point-preserves-point-unpointed-htpy-pointed-Π f g
        ( htpy-pointed-htpy)
        ( preserves-point-pointed-htpy)

  make-pointed-htpy :
    (G : unpointed-htpy-pointed-Π f g) →
    coherence-point-unpointed-htpy-pointed-Π f g G →
    uniform-pointed-htpy
  pr1 (make-pointed-htpy G p) = G
  pr2 (make-pointed-htpy G p) =
    preserves-point-coherence-point-unpointed-htpy-pointed-Π f g G p
```

### Pointed homotopies with inverse-free base point coherence

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B)
  where

  pointed-htpy' : UU (l1 ⊔ l2)
  pointed-htpy' =
    Σ ( function-pointed-Π f ~ function-pointed-Π g)
      ( coherence-point-unpointed-htpy-pointed-Π f g)

  module _
    (H : pointed-htpy')
    where

    htpy-pointed-htpy' : function-pointed-Π f ~ function-pointed-Π g
    htpy-pointed-htpy' = pr1 H

    coherence-point-pointed-htpy' :
      coherence-point-unpointed-htpy-pointed-Π f g htpy-pointed-htpy'
    coherence-point-pointed-htpy' = pr2 H

    preserves-point-pointed-htpy' :
      preserves-point-unpointed-htpy-pointed-Π f g htpy-pointed-htpy'
    preserves-point-pointed-htpy' =
      preserves-point-coherence-point-unpointed-htpy-pointed-Π f g
        ( htpy-pointed-htpy')
        ( coherence-point-pointed-htpy')

    pointed-htpy-pointed-htpy' : f ~∗ g
    pr1 pointed-htpy-pointed-htpy' = htpy-pointed-htpy'
    pr2 pointed-htpy-pointed-htpy' = preserves-point-pointed-htpy'

  compute-pointed-htpy : pointed-htpy' ≃ (f ~∗ g)
  compute-pointed-htpy =
    equiv-tot (compute-coherence-point-unpointed-htpy-pointed-Π f g)
```

### Higher pointed homotopies

Since homotopies are defined between pointed dependent functions, a pointed
2-homotopy between two pointed homotopies is simply a pointed homotopy between
them.

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

A pointed homotopy `H ~∗ K` then consists of an unpointed homotopy `α₀ : H₀ ~ K₀` and a base point coherence

```text
        α₀ *
  H₀ * ------> K₀ *
      \       ∧
    H̃₁ \     / inv K̃₁
        \   /
         ∨ /
       f₁ ∙ inv g₁
```

Equivalently, the base point coherence of an unpointed homotopy `α₀ : H₀ ~ K₀` is an identification witnessing that the triangle

```text
        H₁
  f₁ ------> (H₀ *) ∙ g₁
    \       /
  K₁ \     / right-whisker-concat (α₀ *) ∙ g₁
      \   /
       ∨ ∨
   (K₀ *) ∙ g₁
```

commutes.

```text
  K₁ ＝ H₁ ∙ right-whisker-concat (α₀ *) g₁
```

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (H K : pointed-htpy' f g)
  where

  unpointed-htpy-pointed-htpy' : UU (l1 ⊔ l2)
  unpointed-htpy-pointed-htpy' =
    htpy-pointed-htpy' f g H ~ htpy-pointed-htpy' f g K

  coherence-point-unpointed-htpy-pointed-htpy' :
    unpointed-htpy-pointed-htpy' → UU l2
  coherence-point-unpointed-htpy-pointed-htpy' α =
    coherence-triangle-identifications
      ( coherence-point-pointed-htpy' f g K)
      ( right-whisker-concat
        ( α (point-Pointed-Type A))
        ( preserves-point-function-pointed-Π g))
      ( coherence-point-pointed-htpy' f g H)

  pointed-2-htpy' : UU (l1 ⊔ l2)
  pointed-2-htpy' =
    Σ unpointed-htpy-pointed-htpy' coherence-point-unpointed-htpy-pointed-htpy'

  module _
    (α : pointed-2-htpy')
    where

    htpy-pointed-2-htpy' : unpointed-htpy-pointed-htpy'
    htpy-pointed-2-htpy' = pr1 α

    coherence-point-pointed-2-htpy' :
      coherence-point-unpointed-htpy-pointed-htpy' htpy-pointed-2-htpy'
    coherence-point-pointed-2-htpy' = pr2 α

    preserves-point-pointed-2-htpy' :
      preserves-point-unpointed-htpy-pointed-Π
        ( make-pointed-htpy f g
          ( htpy-pointed-htpy' f g H)
          ( coherence-point-pointed-htpy' f g H))
        ( make-pointed-htpy f g
          ( htpy-pointed-htpy' f g K)
          ( coherence-point-pointed-htpy' f g K))
        ( htpy-pointed-2-htpy')
    preserves-point-pointed-2-htpy' =
      transpose-right-coherence-triangle-identifications
        ( htpy-pointed-2-htpy' (point-Pointed-Type A))
        ( preserves-point-pointed-htpy' f g K)
        ( preserves-point-pointed-htpy' f g H)
        ( higher-transpose-right-coherence-triangle-identifications
          ( htpy-pointed-htpy' f g H (point-Pointed-Type A))
          ( preserves-point-function-pointed-Π g)
          ( preserves-point-function-pointed-Π f)
          ( htpy-pointed-2-htpy' (point-Pointed-Type A))
          ( coherence-point-pointed-htpy' f g H)
          ( coherence-point-pointed-htpy' f g K)
          ( coherence-point-pointed-2-htpy'))

    pointed-htpy-pointed-2-htpy' :
      pointed-htpy-pointed-htpy' f g H ~∗ pointed-htpy-pointed-htpy' f g K
    pr1 pointed-htpy-pointed-2-htpy' =
      htpy-pointed-2-htpy'
    pr2 pointed-htpy-pointed-2-htpy' =
      preserves-point-pointed-2-htpy'
```

## Properties

### Extensionality of pointed dependent function types

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f : pointed-Π A B)
  where

  refl-pointed-htpy : f ~∗ f
  pr1 refl-pointed-htpy = refl-htpy
  pr2 refl-pointed-htpy = inv (right-inv (preserves-point-function-pointed-Π f))

  extensionality-pointed-Π : (g : pointed-Π A B) → Id f g ≃ (f ~∗ g)
  extensionality-pointed-Π =
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

  eq-pointed-htpy :
    (g : pointed-Π A B) → f ~∗ g → Id f g
  eq-pointed-htpy g = map-inv-equiv (extensionality-pointed-Π g)
```

### Extensionality of pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B)
  where

  extensionality-pointed-map : (g : A →∗ B) → (f ＝ g) ≃ (f ~∗ g)
  extensionality-pointed-map = extensionality-pointed-Π f
```

### Concatenation of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g h : pointed-Π A B) (G : f ~∗ g) (H : g ~∗ h)
  where

  htpy-concat-pointed-htpy : unpointed-htpy-pointed-Π f h
  htpy-concat-pointed-htpy =
    htpy-pointed-htpy f g G ∙h htpy-pointed-htpy g h H

  coherence-concat-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π f h htpy-concat-pointed-htpy
  coherence-concat-pointed-htpy =
    ( coherence-point-pointed-htpy f g G) ∙
    ( ( ap
        ( concat (htpy-pointed-htpy f g G (pr2 A)) _)
        ( coherence-point-pointed-htpy g h H)) ∙
      ( inv
        ( assoc
          ( htpy-pointed-htpy f g G (point-Pointed-Type A))
          ( htpy-pointed-htpy g h H (point-Pointed-Type A))
          ( preserves-point-function-pointed-Π h))))

  concat-pointed-htpy : f ~∗ h
  concat-pointed-htpy =
    make-pointed-htpy f h htpy-concat-pointed-htpy coherence-concat-pointed-htpy
```

### Inverses of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  (f g : pointed-Π A B) (H : f ~∗ g)
  where

  htpy-inv-pointed-htpy : unpointed-htpy-pointed-Π g f
  htpy-inv-pointed-htpy = inv-htpy (htpy-pointed-htpy f g H)

  coherence-inv-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π g f htpy-inv-pointed-htpy
  coherence-inv-pointed-htpy =
    left-transpose-eq-concat
      ( htpy-pointed-htpy f g H (point-Pointed-Type A))
      ( preserves-point-function-pointed-Π g)
      ( preserves-point-function-pointed-Π f)
      ( inv (coherence-point-pointed-htpy f g H))

  inv-pointed-htpy : g ~∗ f
  inv-pointed-htpy =
    make-pointed-htpy g f htpy-inv-pointed-htpy coherence-inv-pointed-htpy
```

### Associativity of composition of pointed maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {C : Pointed-Type l3} {D : Pointed-Type l4}
  where

  htpy-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    unpointed-htpy-pointed-Π ((h ∘∗ g) ∘∗ f) (h ∘∗ (g ∘∗ f))
  htpy-associative-comp-pointed-map h g f = refl-htpy

  coherence-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    preserves-point-unpointed-htpy-pointed-Π
      ( (h ∘∗ g) ∘∗ f)
      ( h ∘∗ (g ∘∗ f))
      ( htpy-associative-comp-pointed-map h g f)
  coherence-associative-comp-pointed-map (h , refl) (g , refl) (f , refl) =
    refl

  associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    (h ∘∗ g) ∘∗ f ~∗ h ∘∗ (g ∘∗ f)
  pr1 (associative-comp-pointed-map h g f) =
    htpy-associative-comp-pointed-map h g f
  pr2 (associative-comp-pointed-map h g f) =
    coherence-associative-comp-pointed-map h g f

  htpy-inv-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    unpointed-htpy-pointed-Π (h ∘∗ (g ∘∗ f)) ((h ∘∗ g) ∘∗ f)
  htpy-inv-associative-comp-pointed-map h g f = refl-htpy

  coherence-inv-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    preserves-point-unpointed-htpy-pointed-Π
      ( h ∘∗ (g ∘∗ f))
      ( (h ∘∗ g) ∘∗ f)
      ( htpy-inv-associative-comp-pointed-map h g f)
  coherence-inv-associative-comp-pointed-map (h , refl) (g , refl) (f , refl) =
    refl

  inv-associative-comp-pointed-map :
    (h : C →∗ D) (g : B →∗ C) (f : A →∗ B) →
    h ∘∗ (g ∘∗ f) ~∗ (h ∘∗ g) ∘∗ f
  pr1 (inv-associative-comp-pointed-map h g f) =
    htpy-associative-comp-pointed-map h g f
  pr2 (inv-associative-comp-pointed-map h g f) =
    coherence-inv-associative-comp-pointed-map h g f
```

### The left unit law for composition of pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  htpy-left-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-left-unit-law-comp-pointed-map = refl-htpy

  coherence-left-unit-law-comp-pointed-map' :
    coherence-point-unpointed-htpy-pointed-Π
      ( id-pointed-map ∘∗ f)
      ( f)
      ( htpy-left-unit-law-comp-pointed-map)
  coherence-left-unit-law-comp-pointed-map' =
    right-unit ∙ ap-id (preserves-point-pointed-map f)

  left-unit-law-comp-pointed-map : id-pointed-map ∘∗ f ~∗ f
  left-unit-law-comp-pointed-map =
    make-pointed-htpy
      ( id-pointed-map ∘∗ f)
      ( f)
      ( htpy-left-unit-law-comp-pointed-map)
      ( coherence-left-unit-law-comp-pointed-map')

  htpy-inv-left-unit-law-comp-pointed-map :
    map-pointed-map f ~ map-pointed-map f
  htpy-inv-left-unit-law-comp-pointed-map = refl-htpy

  coherence-inv-left-unit-law-comp-pointed-map' :
    coherence-point-unpointed-htpy-pointed-Π
      ( f)
      ( id-pointed-map ∘∗ f)
      ( htpy-inv-left-unit-law-comp-pointed-map)
  coherence-inv-left-unit-law-comp-pointed-map' =
    inv (right-unit ∙ ap-id (preserves-point-pointed-map f))

  inv-left-unit-law-comp-pointed-map : f ~∗ id-pointed-map ∘∗ f
  inv-left-unit-law-comp-pointed-map =
    make-pointed-htpy
      ( f)
      ( id-pointed-map ∘∗ f)
      ( htpy-inv-left-unit-law-comp-pointed-map)
      ( coherence-inv-left-unit-law-comp-pointed-map')
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
    preserves-point-unpointed-htpy-pointed-Π
      ( f ∘∗ id-pointed-map)
      ( f)
      ( htpy-right-unit-law-comp-pointed-map)
  coherence-right-unit-law-comp-pointed-map =
    inv (right-inv (preserves-point-pointed-map f))

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
  (f g h k : pointed-Π A B) (G : f ~∗ g) (H : g ~∗ h) (K : h ~∗ k)
  where

  htpy-assoc-pointed-htpy :
    htpy-pointed-htpy f k
      ( concat-pointed-htpy f h k (concat-pointed-htpy f g h G H) K) ~
    htpy-pointed-htpy f k
      ( concat-pointed-htpy f g k G (concat-pointed-htpy g h k H K))
  htpy-assoc-pointed-htpy =
    assoc-htpy
      ( htpy-pointed-htpy f g G)
      ( htpy-pointed-htpy g h H)
      ( htpy-pointed-htpy h k K)

  coherence-assoc-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-htpy' f k
      {! concat-pointed-htpy' f h k (concat-pointed-htpy f g h G H) K!}
      {!!}
      {!!}
  coherence-assoc-pointed-htpy = {!!}


  assoc-pointed-htpy :
    concat-pointed-htpy f h k (concat-pointed-htpy f g h G H) K ~∗
    concat-pointed-htpy f g k G (concat-pointed-htpy g h k H K)
  pr1 assoc-pointed-htpy = htpy-assoc-pointed-htpy
  pr2 assoc-pointed-htpy = {!!}
```
