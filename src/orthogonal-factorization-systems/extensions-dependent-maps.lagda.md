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
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

An
{{#concept "extension" Disambiguation="of a dependent map along a map, types" Agda=extension-dependent-map}}
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

  is-extension-of-dependent-map :
    {P : B → UU l3} →
    ((x : A) → P (i x)) → ((y : B) → P y) → UU (l1 ⊔ l3)
  is-extension-of-dependent-map f g = (f ~ g ∘ i)

  extension-dependent-map :
    (P : B → UU l3) →
    ((x : A) → P (i x)) → UU (l1 ⊔ l2 ⊔ l3)
  extension-dependent-map P f =
    Σ ((y : B) → P y) (is-extension-of-dependent-map f)

  total-extension-dependent-map : (P : B → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension-dependent-map P =
    Σ ((x : A) → P (i x)) (extension-dependent-map P)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {i : A → B}
  {P : B → UU l3} {f : (x : A) → P (i x)}
  where

  map-extension-dependent-map : extension-dependent-map i P f → (y : B) → P y
  map-extension-dependent-map = pr1

  is-extension-map-extension-dependent-map :
    (E : extension-dependent-map i P f) →
    is-extension-of-dependent-map i f (map-extension-dependent-map E)
  is-extension-map-extension-dependent-map = pr2
```

### Extensions of dependent maps with homotopies going the other way

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-extension-of-dependent-map' :
    {P : B → UU l3} →
    ((x : A) → P (i x)) → ((y : B) → P y) → UU (l1 ⊔ l3)
  is-extension-of-dependent-map' f g = (g ∘ i ~ f)

  extension-dependent-map' :
    (P : B → UU l3) →
    ((x : A) → P (i x)) → UU (l1 ⊔ l2 ⊔ l3)
  extension-dependent-map' P f =
    Σ ((y : B) → P y) (is-extension-of-dependent-map' f)

  total-extension-dependent-map' : (P : B → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension-dependent-map' P =
    Σ ((x : A) → P (i x)) (extension-dependent-map' P)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {i : A → B}
  {P : B → UU l3} {f : (x : A) → P (i x)}
  where

  map-extension-dependent-map' :
    extension-dependent-map' i P f → (y : B) → P y
  map-extension-dependent-map' = pr1

  is-extension-map-extension-dependent-map' :
    (E : extension-dependent-map' i P f) →
    is-extension-of-dependent-map' i f (map-extension-dependent-map' E)
  is-extension-map-extension-dependent-map' = pr2
```

## Operations

### Vertical composition of extensions of dependent maps

```text
    A
    |  \
  i |    \ f
    |      \
    ∨   g    ∨
    B ------> P
    |        ∧
  j |      /
    |    / h
    ∨  /
    C
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {P : C → UU l4}
  {i : A → B} {j : B → C}
  {f : (x : A) → P (j (i x))} {g : (x : B) → P (j x)} {h : (x : C) → P x}
  where

  is-extension-of-dependent-map-comp-vertical :
    is-extension-of-dependent-map j g h →
    is-extension-of-dependent-map i f g →
    is-extension-of-dependent-map (j ∘ i) f h
  is-extension-of-dependent-map-comp-vertical H G x = G x ∙ H (i x)
```

### Horizontal composition of extensions of dependent maps

```text
            A
         /  |  \
     f /  g |    \ h
     /      |      \
   ∨   i    ∨    j   ∨
  B ------> C ------> P
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {P : C → UU l4}
  {f : A → B} {g : A → C} {h : (x : A) → P (g x)}
  {i : B → C} {j : (z : C) → P z}
  where

  is-extension-of-dependent-map-comp-horizontal :
    (I : is-extension-of-dependent-map f g i) →
    is-extension-of-dependent-map g h j →
    is-extension-of-dependent-map f (λ x → tr P (I x) (h x)) (j ∘ i)
  is-extension-of-dependent-map-comp-horizontal I J x =
    ap (tr P (I x)) (J x) ∙ apd j (I x)
```

### Left whiskering of extensions of dependent maps

```text
    A
    |  \
  i |    \ f
    |      \
    ∨    g   ∨     h
    B ------> C ------> P
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {P : C → UU l4}
  {i : A → B} {f : A → C} {g : B → C}
  where

  is-extension-of-dependent-map-left-whisker :
    (h : (x : C) → P x) (F : is-extension-of-dependent-map i f g) →
    is-extension-of-dependent-map i (λ x → tr P (F x) (h (f x))) (h ∘ g)
  is-extension-of-dependent-map-left-whisker h F = apd h ∘ F
```

### Right whiskering of extensions of dependent maps

```text
       h
  X ------> A
            |  \
          i |    \ f
            |      \
            ∨    g   ∨
            B ------> P
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : B → UU l3} {X : UU l4}
  {i : A → B} {f : (x : A) → P (i x)} {g : (y : B) → P y}
  where

  is-extension-of-dependent-map-right-whisker :
    is-extension-of-dependent-map i f g →
    (h : X → A) →
    is-extension-of-dependent-map (i ∘ h) (f ∘ h) g
  is-extension-of-dependent-map-right-whisker F h = F ∘ h
```

## Properties

### The total type of extensions is equivalent to `(y : B) → P y`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  inv-compute-total-extension-dependent-map :
    {P : B → UU l3} → total-extension-dependent-map i P ≃ ((y : B) → P y)
  inv-compute-total-extension-dependent-map =
    ( right-unit-law-Σ-is-contr (λ f → is-torsorial-htpy' (f ∘ i))) ∘e
    ( equiv-left-swap-Σ)

  compute-total-extension-dependent-map :
    {P : B → UU l3} → ((y : B) → P y) ≃ total-extension-dependent-map i P
  compute-total-extension-dependent-map =
    inv-equiv (inv-compute-total-extension-dependent-map)
```

### The truncation level of the type of extensions is bounded by the truncation level of the codomain

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-trunc-is-extension-of-dependent-map :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-trunc (succ-𝕋 k) (P (i x))) →
    (g : (x : B) → P x) → is-trunc k (is-extension-of-dependent-map i f g)
  is-trunc-is-extension-of-dependent-map f is-trunc-P g =
    is-trunc-Π k (λ x → is-trunc-P x (f x) (g (i x)))

  is-trunc-extension-dependent-map :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : B) → is-trunc k (P x)) → is-trunc k (extension-dependent-map i P f)
  is-trunc-extension-dependent-map f is-trunc-P =
    is-trunc-Σ
      ( is-trunc-Π k is-trunc-P)
      ( is-trunc-is-extension-of-dependent-map f
        ( is-trunc-succ-is-trunc k ∘ (is-trunc-P ∘ i)))

  is-trunc-total-extension-dependent-map :
    {P : B → UU l3} →
    ((x : B) → is-trunc k (P x)) →
    is-trunc k (total-extension-dependent-map i P)
  is-trunc-total-extension-dependent-map {P} is-trunc-P =
    is-trunc-equiv' k
      ( (y : B) → P y)
      ( compute-total-extension-dependent-map i)
      ( is-trunc-Π k is-trunc-P)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-contr-is-extension-of-dependent-map :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-prop (P (i x))) →
    (g : (x : B) → P x) → is-contr (is-extension-of-dependent-map i f g)
  is-contr-is-extension-of-dependent-map f is-prop-P g =
    is-contr-Π (λ x → is-prop-P x (f x) (g (i x)))

  is-prop-is-extension-of-dependent-map :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-set (P (i x))) →
    (g : (x : B) → P x) → is-prop (is-extension-of-dependent-map i f g)
  is-prop-is-extension-of-dependent-map f is-set-P g =
    is-prop-Π (λ x → is-set-P x (f x) (g (i x)))
```

## Examples

### Every dependent map is an extension of itself along the identity

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2} (f : (x : A) → P x)
  where

  is-extension-of-dependent-map-self : is-extension-of-dependent-map id f f
  is-extension-of-dependent-map-self = refl-htpy

  self-extension-dependent-map : extension-dependent-map id P f
  self-extension-dependent-map = (f , is-extension-of-dependent-map-self)
```

## See also

- [`orthogonal-factorization-systems.lifts-maps`](orthogonal-factorization-systems.lifts-maps.md)
  for the dual notion.
