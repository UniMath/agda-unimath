# Extensions of dependent maps

```agda
module orthogonal-factorization-systems.extensions-dependent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.torsorial-type-families
```

</details>

## Idea

An
{{#concept "extension" Disambiguation="of a dependent map along a map, types" Agda=extension-dependent-type}}
of a dependent map `f : (x : A) → P (i x)` along a map `i : A → B` is a map
`g : (y : B) → P y` such that `g` restricts along `i` to `f`.

```text
      A
      |  \
    i |    \ f
      |      \
      ∨   g   ∨
  b ∈ B -----> P b
```

## Definition

### Extensions of dependent maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-extension-dependent-type :
    {P : B → UU l3} →
    ((x : A) → P (i x)) → ((y : B) → P y) → UU (l1 ⊔ l3)
  is-extension-dependent-type f g = (f ~ g ∘ i)

  extension-dependent-type :
    (P : B → UU l3) →
    ((x : A) → P (i x)) → UU (l1 ⊔ l2 ⊔ l3)
  extension-dependent-type P f =
    Σ ((y : B) → P y) (is-extension-dependent-type f)

  total-extension-dependent-type : (P : B → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension-dependent-type P =
    Σ ((x : A) → P (i x)) (extension-dependent-type P)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {i : A → B}
  {P : B → UU l3} {f : (x : A) → P (i x)}
  where

  map-extension-dependent-type : extension-dependent-type i P f → (y : B) → P y
  map-extension-dependent-type = pr1

  is-extension-map-extension-dependent-type :
    (E : extension-dependent-type i P f) →
    is-extension-dependent-type i f (map-extension-dependent-type E)
  is-extension-map-extension-dependent-type = pr2
```

### Extensions of dependent maps with homotopies going the other way

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-extension-dependent-type' :
    {P : B → UU l3} →
    ((x : A) → P (i x)) → ((y : B) → P y) → UU (l1 ⊔ l3)
  is-extension-dependent-type' f g = (g ∘ i ~ f)

  extension-dependent-type' :
    (P : B → UU l3) →
    ((x : A) → P (i x)) → UU (l1 ⊔ l2 ⊔ l3)
  extension-dependent-type' P f =
    Σ ((y : B) → P y) (is-extension-dependent-type' f)

  total-extension-dependent-type' : (P : B → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension-dependent-type' P =
    Σ ((x : A) → P (i x)) (extension-dependent-type' P)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {i : A → B}
  {P : B → UU l3} {f : (x : A) → P (i x)}
  where

  map-extension-dependent-type' :
    extension-dependent-type' i P f → (y : B) → P y
  map-extension-dependent-type' = pr1

  is-extension-map-extension-dependent-type' :
    (E : extension-dependent-type' i P f) →
    is-extension-dependent-type' i f (map-extension-dependent-type' E)
  is-extension-map-extension-dependent-type' = pr2
```

## Operations

### Vertical composition of extensions of dependent maps

```text
  A
  |  \
  i    f
  |      \
  ∨       ∨
  B - g -> P
  |       ∧
  j      /
  |    h
  ∨  /
  C
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {P : C → UU l4}
  {i : A → B} {j : B → C}
  {f : (x : A) → P (j (i x))} {g : (x : B) → P (j x)} {h : (x : C) → P x}
  where

  is-extension-dependent-type-comp-vertical :
    is-extension-dependent-type j g h →
    is-extension-dependent-type i f g →
    is-extension-dependent-type (j ∘ i) f h
  is-extension-dependent-type-comp-vertical H G x = G x ∙ H (i x)
```

### Horizontal composition of extensions of dependent maps

```text
           A
        /  |  \
      f    g    h
    /      |      \
   ∨       ∨       ∨
  B - i -> C - j -> P
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {P : C → UU l4}
  {f : A → B} {g : A → C} {h : (x : A) → P (g x)}
  {i : B → C} {j : (z : C) → P z}
  where

  is-extension-dependent-type-comp-horizontal :
    (I : is-extension-dependent-type f g i) →
    is-extension-dependent-type g h j →
    is-extension-dependent-type f (λ x → tr P (I x) (h x)) (j ∘ i)
  is-extension-dependent-type-comp-horizontal I J x =
    ap (tr P (I x)) (J x) ∙ apd j (I x)
```

### Left whiskering of extensions of dependent maps

```text
  A
  |  \
  i    f
  |      \
  ∨       ∨
  B - g -> C - h -> P
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {P : C → UU l4}
  {i : A → B} {f : A → C} {g : B → C}
  where

  is-extension-dependent-type-left-whisker :
    (h : (x : C) → P x) (F : is-extension-dependent-type i f g) →
    is-extension-dependent-type i (λ x → tr P (F x) (h (f x))) (h ∘ g)
  is-extension-dependent-type-left-whisker h F = apd h ∘ F
```

### Right whiskering of extensions of dependent maps

```text
  X - h -> A
           |  \
           i    f
           |      \
           ∨       ∨
           B - g -> P
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : B → UU l3} {X : UU l4}
  {i : A → B} {f : (x : A) → P (i x)} {g : (y : B) → P y}
  where

  is-extension-dependent-type-right-whisker :
    is-extension-dependent-type i f g →
    (h : X → A) →
    is-extension-dependent-type (i ∘ h) (f ∘ h) g
  is-extension-dependent-type-right-whisker F h = F ∘ h
```

## Properties

### The total type of extensions is equivalent to `(y : B) → P y`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  inv-compute-total-extension-dependent-type :
    {P : B → UU l3} → total-extension-dependent-type i P ≃ ((y : B) → P y)
  inv-compute-total-extension-dependent-type =
    ( right-unit-law-Σ-is-contr (λ f → is-torsorial-htpy' (f ∘ i))) ∘e
    ( equiv-left-swap-Σ)

  compute-total-extension-dependent-type :
    {P : B → UU l3} → ((y : B) → P y) ≃ total-extension-dependent-type i P
  compute-total-extension-dependent-type =
    inv-equiv (inv-compute-total-extension-dependent-type)
```

### The truncation level of the type of extensions is bounded by the truncation level of the codomain

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-trunc-is-extension-dependent-type :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-trunc (succ-𝕋 k) (P (i x))) →
    (g : (x : B) → P x) → is-trunc k (is-extension-dependent-type i f g)
  is-trunc-is-extension-dependent-type f is-trunc-P g =
    is-trunc-Π k (λ x → is-trunc-P x (f x) (g (i x)))

  is-trunc-extension-dependent-type :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : B) → is-trunc k (P x)) → is-trunc k (extension-dependent-type i P f)
  is-trunc-extension-dependent-type f is-trunc-P =
    is-trunc-Σ
      ( is-trunc-Π k is-trunc-P)
      ( is-trunc-is-extension-dependent-type f
        ( is-trunc-succ-is-trunc k ∘ (is-trunc-P ∘ i)))

  is-trunc-total-extension-dependent-type :
    {P : B → UU l3} →
    ((x : B) → is-trunc k (P x)) →
    is-trunc k (total-extension-dependent-type i P)
  is-trunc-total-extension-dependent-type {P} is-trunc-P =
    is-trunc-equiv' k
      ( (y : B) → P y)
      ( compute-total-extension-dependent-type i)
      ( is-trunc-Π k is-trunc-P)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-contr-is-extension-dependent-type :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-prop (P (i x))) →
    (g : (x : B) → P x) → is-contr (is-extension-dependent-type i f g)
  is-contr-is-extension-dependent-type f is-prop-P g =
    is-contr-Π (λ x → is-prop-P x (f x) (g (i x)))

  is-prop-is-extension-dependent-type :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-set (P (i x))) →
    (g : (x : B) → P x) → is-prop (is-extension-dependent-type i f g)
  is-prop-is-extension-dependent-type f is-set-P g =
    is-prop-Π (λ x → is-set-P x (f x) (g (i x)))
```

## Examples

### Every dependent map is an extension of itself along the identity

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2} (f : (x : A) → P x)
  where

  is-extension-dependent-type-self : is-extension-dependent-type id f f
  is-extension-dependent-type-self = refl-htpy

  extension-self : extension-dependent-type id P f
  extension-self = (f , is-extension-dependent-type-self)
```

## See also

- [`orthogonal-factorization-systems.lifts-maps`](orthogonal-factorization-systems.lifts-maps.md)
  for the dual notion.
