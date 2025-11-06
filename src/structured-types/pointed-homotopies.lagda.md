# Pointed homotopies

```agda
module structured-types.pointed-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
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

A {{#concept "pointed homotopy" Agda=_~∗_}} between
[pointed dependent functions](structured-types.pointed-dependent-functions.md)
`f := (f₀ , f₁)` and `g := (g₀ , g₁)` of type `pointed-Π A B` consists of an
unpointed [homotopy](foundation-core.homotopies.md) `H₀ : f₀ ~ g₀` and an
[identification](foundation-core.identity-types.md) `H₁ : f₁ ＝ (H₀ *) ∙ g₁`
witnessing that the triangle of identifications

```text
        H₀ *
  f₀ * ------> g₀ *
      \       /
    f₁ \     / g₁
        \   /
         ∨ ∨
          *
```

[commutes](foundation.commuting-triangles-of-identifications.md). This
identification is called the
{{#concept "base point coherence" Disambiguation="pointed homotopy" Agda=coherence-point-unpointed-htpy-pointed-Π}}
of the pointed homotopy `H := (H₀ , H₁)`.

An equivalent way of defining pointed homotopies occurs when we consider the
type family `x ↦ f₀ x ＝ g₀ x` over the base type `A`. This is a
[pointed type family](structured-types.pointed-families-of-types.md), where the
base point is the identification

```text
  f₁ ∙ inv g₁ : f₀ * ＝ g₀ *.
```

A pointed homotopy `f ~∗ g` is therefore equivalently defined as a pointed
dependent function of the pointed type family `x ↦ f₀ x ＝ g₀ x`. Such a pointed
dependent function consists of an unpointed homotopy `H₀ : f₀ ~ g₀` between the
underlying dependent functions and an identification witnessing that the
triangle of identifications

```text
        H₀ *
  f₀ * ------> g₀ *
      \       ∧
    f₁ \     / inv g₁
        \   /
         ∨ /
          *
```

[commutes](foundation.commuting-triangles-of-identifications.md). Notice that
the identification on the right in this triangle goes up, in the inverse
direction of the identification `g₁`.

Note that in this second definition of pointed homotopies we defined pointed
homotopies between pointed dependent functions to be certain pointed dependent
functions. This implies that the second definition is a uniform definition that
can easily be iterated in order to consider pointed higher homotopies. For this
reason, we call the second definition of pointed homotopies
[uniform pointed homotopies](structured-types.uniform-pointed-homotopies.md).

Note that the difference between our main definition of pointed homotopies and
the uniform definition of pointed homotopies is the direction of the
identification on the right in the commuting triangle

```text
        H₀ *
  f₀ * ------> g₀ *
      \       /
    f₁ \     / g₁
        \   /
         ∨ ∨
          *.
```

In the definition of uniform pointed homotopies it goes in the reverse
direction. This makes it slightly more complicated to construct an
identification witnessing that the triangle commutes in the case of uniform
pointed homotopies. Furthermore, this complication becomes more significant and
bothersome when we are trying to construct a
[pointed `2`-homotopy](structured-types.pointed-2-homotopies.md). For this
reason, our first definition where pointed homotopies are defined to consist of
unpointed homotopies and a base point coherence, is taken to be our main
definition of pointed homotopy. The only disadvantage of the nonuniform
definition of pointed homotopies is that it does not easily iterate.

We will write `f ~∗ g` for the type of (nonuniform) pointed homotopies, and we
will write `H ~²∗ K` for the nonuniform definition of pointed `2`-homotopies.

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

The base point coherence of pointed homotopies asserts that its underlying
homotopy preserves the base point, in the sense that the triangle of
identifications

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
  (f g : pointed-Π A B)
  where

  coherence-point-unpointed-htpy-pointed-Π' :
    function-pointed-Π f (point-Pointed-Type A) ＝
    function-pointed-Π g (point-Pointed-Type A) →
    UU l2
  coherence-point-unpointed-htpy-pointed-Π' G =
    coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( G)

  coherence-point-unpointed-htpy-pointed-Π :
    unpointed-htpy-pointed-Π f g → UU l2
  coherence-point-unpointed-htpy-pointed-Π G =
    coherence-point-unpointed-htpy-pointed-Π'
      ( G (point-Pointed-Type A))
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
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H : f ~∗ g)
  where

  htpy-pointed-htpy : function-pointed-Π f ~ function-pointed-Π g
  htpy-pointed-htpy = pr1 H

  coherence-point-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π f g htpy-pointed-htpy
  coherence-point-pointed-htpy = pr2 H
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

### Concatenation of pointed homotopies

Consider three pointed dependent functions `f := (f₀ , f₁)`, `g := (g₀ , g₁)`,
and `h := (h₀ , h₁)`, and pointed homotopies `G := (G₀ , G₁)` and
`H := (H₀ , H₁)` between them as indicated in the diagram

```text
      G        H
  f -----> g -----> h
```

The concatenation `(G ∙h H)` of `G` and `H` has underlying unpointed homotopy

```text
  (G ∙h H)₀ := G₀ ∙h H₀.
```

The base point coherence `(G ∙h H)₁` of `(G ∙h H)` is obtained by horizontally
pasting the commuting triangles of identifications

```text
      G₀ *      H₀ *
  f₀ * --> g₀ * ---> h₀ *
      \      |      /
       \     | g₁  /
     f₁ \    |    / h₁
         \   |   /
          \  |  /
           ∨ ∨ ∨
             *.
```

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g h : pointed-Π A B} (G : f ~∗ g) (H : g ~∗ h)
  where

  htpy-concat-pointed-htpy : unpointed-htpy-pointed-Π f h
  htpy-concat-pointed-htpy = htpy-pointed-htpy G ∙h htpy-pointed-htpy H

  coherence-point-concat-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π f h htpy-concat-pointed-htpy
  coherence-point-concat-pointed-htpy =
    horizontal-pasting-coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( preserves-point-function-pointed-Π h)
      ( htpy-pointed-htpy G (point-Pointed-Type A))
      ( htpy-pointed-htpy H (point-Pointed-Type A))
      ( coherence-point-pointed-htpy G)
      ( coherence-point-pointed-htpy H)

  concat-pointed-htpy : f ~∗ h
  pr1 concat-pointed-htpy = htpy-concat-pointed-htpy
  pr2 concat-pointed-htpy = coherence-point-concat-pointed-htpy

  infixl 15 _∙h∗_
  _∙h∗_ : f ~∗ h
  _∙h∗_ = concat-pointed-htpy
```

### Inverses of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H : f ~∗ g)
  where

  htpy-inv-pointed-htpy : unpointed-htpy-pointed-Π g f
  htpy-inv-pointed-htpy = inv-htpy (htpy-pointed-htpy H)

  coherence-point-inv-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-Π g f htpy-inv-pointed-htpy
  coherence-point-inv-pointed-htpy =
    transpose-top-coherence-triangle-identifications
      ( preserves-point-function-pointed-Π g)
      ( preserves-point-function-pointed-Π f)
      ( htpy-pointed-htpy H (point-Pointed-Type A))
      ( refl)
      ( coherence-point-pointed-htpy H)

  inv-pointed-htpy : g ~∗ f
  pr1 inv-pointed-htpy = htpy-inv-pointed-htpy
  pr2 inv-pointed-htpy = coherence-point-inv-pointed-htpy
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
    id ∘ map-pointed-map f ~ map-pointed-map f
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
    map-pointed-map f ~ id ∘ map-pointed-map f
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
    map-pointed-map f ∘ id ~ map-pointed-map f
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

### Concatenation of pointed homotopies is a binary equivalence

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g h : pointed-Π A B}
  where

  abstract
    is-equiv-concat-pointed-htpy :
      (G : f ~∗ g) → is-equiv (λ (H : g ~∗ h) → concat-pointed-htpy G H)
    is-equiv-concat-pointed-htpy G =
      is-equiv-map-Σ _
        ( is-equiv-concat-htpy (htpy-pointed-htpy G) _)
        ( λ H →
          is-equiv-horizontal-pasting-coherence-triangle-identifications
            ( preserves-point-function-pointed-Π f)
            ( preserves-point-function-pointed-Π g)
            ( preserves-point-function-pointed-Π h)
            ( htpy-pointed-htpy G _)
            ( H _)
            ( coherence-point-pointed-htpy G))

  equiv-concat-pointed-htpy : f ~∗ g → (g ~∗ h) ≃ (f ~∗ h)
  pr1 (equiv-concat-pointed-htpy G) = concat-pointed-htpy G
  pr2 (equiv-concat-pointed-htpy G) = is-equiv-concat-pointed-htpy G

  abstract
    is-equiv-concat-pointed-htpy' :
      (H : g ~∗ h) → is-equiv (λ (G : f ~∗ g) → concat-pointed-htpy G H)
    is-equiv-concat-pointed-htpy' H =
      is-equiv-map-Σ _
        ( is-equiv-concat-htpy' _ (htpy-pointed-htpy H))
        ( λ G →
          is-equiv-horizontal-pasting-coherence-triangle-identifications'
            ( preserves-point-function-pointed-Π f)
            ( preserves-point-function-pointed-Π g)
            ( preserves-point-function-pointed-Π h)
            ( G _)
            ( htpy-pointed-htpy H _)
            ( coherence-point-pointed-htpy H))

  equiv-concat-pointed-htpy' : g ~∗ h → (f ~∗ g) ≃ (f ~∗ h)
  pr1 (equiv-concat-pointed-htpy' H) G = concat-pointed-htpy G H
  pr2 (equiv-concat-pointed-htpy' H) = is-equiv-concat-pointed-htpy' H

  is-binary-equiv-concat-pointed-htpy :
    is-binary-equiv (λ (G : f ~∗ g) (H : g ~∗ h) → concat-pointed-htpy G H)
  pr1 is-binary-equiv-concat-pointed-htpy = is-equiv-concat-pointed-htpy'
  pr2 is-binary-equiv-concat-pointed-htpy = is-equiv-concat-pointed-htpy
```

## Reasoning with pointed homotopies

Pointed homotopies can be constructed by equational reasoning in the following
way:

```text
pointed-homotopy-reasoning
  f ~∗ g by htpy-1
    ~∗ h by htpy-2
    ~∗ i by htpy-3
```

The pointed homotopy obtained in this way is `htpy-1 ∙h∗ (htpy-2 ∙h∗ htpy-3)`,
i.e., it is associated fully to the right.

```agda
infixl 1 pointed-homotopy-reasoning_
infixl 0 step-pointed-homotopy-reasoning

pointed-homotopy-reasoning_ :
  {l1 l2 : Level} {X : Pointed-Type l1} {Y : Pointed-Fam l2 X}
  (f : pointed-Π X Y) → f ~∗ f
pointed-homotopy-reasoning f = refl-pointed-htpy f

step-pointed-homotopy-reasoning :
  {l1 l2 : Level} {X : Pointed-Type l1} {Y : Pointed-Fam l2 X}
  {f g : pointed-Π X Y} → f ~∗ g →
  (h : pointed-Π X Y) → g ~∗ h → f ~∗ h
step-pointed-homotopy-reasoning p h q = p ∙h∗ q

syntax step-pointed-homotopy-reasoning p h q = p ~∗ h by q
```

## See also

- [Pointed 2-homotopies](structured-types.pointed-2-homotopies.md)
- [Uniform pointed homotopies](structured-types.uniform-pointed-homotopies.md)
