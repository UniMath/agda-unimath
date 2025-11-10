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
    B -----> P b
```

## Definition

### Extensions of dependent maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-extension :
    {P : B → UU l3} →
    ((x : A) → P (i x)) → ((y : B) → P y) → UU (l1 ⊔ l3)
  is-extension f g = (f ~ g ∘ i)

  extension-dependent-type :
    (P : B → UU l3) →
    ((x : A) → P (i x)) → UU (l1 ⊔ l2 ⊔ l3)
  extension-dependent-type P f = Σ ((y : B) → P y) (is-extension f)

  total-extension-dependent-type : (P : B → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension-dependent-type P =
    Σ ((x : A) → P (i x)) (extension-dependent-type P)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {i : A → B}
  {P : B → UU l3} {f : (x : A) → P (i x)}
  where

  map-extension : extension-dependent-type i P f → (y : B) → P y
  map-extension = pr1

  is-extension-map-extension :
    (E : extension-dependent-type i P f) → is-extension i f (map-extension E)
  is-extension-map-extension = pr2
```

### Extensions of dependent maps with homotopies going the other way

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-extension' :
    {P : B → UU l3} →
    ((x : A) → P (i x)) → ((y : B) → P y) → UU (l1 ⊔ l3)
  is-extension' f g = (g ∘ i ~ f)

  extension-dependent-type' :
    (P : B → UU l3) →
    ((x : A) → P (i x)) → UU (l1 ⊔ l2 ⊔ l3)
  extension-dependent-type' P f = Σ ((y : B) → P y) (is-extension' f)

  total-extension-dependent-type' : (P : B → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension-dependent-type' P =
    Σ ((x : A) → P (i x)) (extension-dependent-type' P)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {i : A → B}
  {P : B → UU l3} {f : (x : A) → P (i x)}
  where

  map-extension' : extension-dependent-type' i P f → (y : B) → P y
  map-extension' = pr1

  is-extension-map-extension' :
    (E : extension-dependent-type' i P f) → is-extension' i f (map-extension' E)
  is-extension-map-extension' = pr2
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

  is-extension-comp-vertical :
    is-extension j g h → is-extension i f g → is-extension (j ∘ i) f h
  is-extension-comp-vertical H G x = G x ∙ H (i x)
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
    (I : is-extension f g i) →
    is-extension g h j → is-extension f (λ x → tr P (I x) (h x)) (j ∘ i)
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

  is-extension-left-whisker :
    (h : (x : C) → P x) (F : is-extension i f g) →
    (is-extension i (λ x → tr P (F x) (h (f x))) (h ∘ g))
  is-extension-left-whisker h F = apd h ∘ F
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

  is-extension-right-whisker :
    (F : is-extension i f g) (h : X → A) → is-extension (i ∘ h) (f ∘ h) g
  is-extension-right-whisker F h = F ∘ h
```

## Properties

### Characterizing equality of extensions of dependent maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3}
  (f : (x : A) → P (i x))
  where

  coherence-htpy-extension :
    (e e' : extension-dependent-type i P f) →
    map-extension e ~ map-extension e' → UU (l1 ⊔ l3)
  coherence-htpy-extension e e' K =
    (is-extension-map-extension e ∙h (K ·r i)) ~ is-extension-map-extension e'

  htpy-extension : (e e' : extension-dependent-type i P f) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-extension e e' =
    Σ ( map-extension e ~ map-extension e')
      ( coherence-htpy-extension e e')

  refl-htpy-extension :
    (e : extension-dependent-type i P f) → htpy-extension e e
  pr1 (refl-htpy-extension e) = refl-htpy
  pr2 (refl-htpy-extension e) = right-unit-htpy

  htpy-eq-extension :
    (e e' : extension-dependent-type i P f) → e ＝ e' → htpy-extension e e'
  htpy-eq-extension e .e refl = refl-htpy-extension e

  is-torsorial-htpy-extension :
    (e : extension-dependent-type i P f) → is-torsorial (htpy-extension e)
  is-torsorial-htpy-extension e =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-extension e))
      ( map-extension e , refl-htpy)
      ( is-torsorial-htpy (is-extension-map-extension e ∙h refl-htpy))

  is-equiv-htpy-eq-extension :
    (e e' : extension-dependent-type i P f) → is-equiv (htpy-eq-extension e e')
  is-equiv-htpy-eq-extension e =
    fundamental-theorem-id
      ( is-torsorial-htpy-extension e)
      ( htpy-eq-extension e)

  extensionality-extension :
    (e e' : extension-dependent-type i P f) → (e ＝ e') ≃ (htpy-extension e e')
  pr1 (extensionality-extension e e') = htpy-eq-extension e e'
  pr2 (extensionality-extension e e') = is-equiv-htpy-eq-extension e e'

  eq-htpy-extension :
    (e e' : extension-dependent-type i P f)
    (H : map-extension e ~ map-extension e') →
    coherence-htpy-extension e e' H → e ＝ e'
  eq-htpy-extension e e' H K =
    map-inv-equiv (extensionality-extension e e') (H , K)
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3}
  (f : (x : A) → P (i x))
  where

  coherence-htpy-extension-dependent-type' :
    (e e' : extension-dependent-type' i P f) →
    map-extension' e ~ map-extension' e' → UU (l1 ⊔ l3)
  coherence-htpy-extension-dependent-type' e e' K =
    is-extension-map-extension' e ~ (K ·r i) ∙h is-extension-map-extension' e'

  htpy-extension-dependent-type' :
    (e e' : extension-dependent-type' i P f) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-extension-dependent-type' e e' =
    Σ ( map-extension' e ~ map-extension' e')
      ( coherence-htpy-extension-dependent-type' e e')

  refl-htpy-extension-dependent-type' :
    (e : extension-dependent-type' i P f) → htpy-extension-dependent-type' e e
  pr1 (refl-htpy-extension-dependent-type' e) = refl-htpy
  pr2 (refl-htpy-extension-dependent-type' e) = refl-htpy

  htpy-eq-extension-dependent-type' :
    (e e' : extension-dependent-type' i P f) →
    e ＝ e' → htpy-extension-dependent-type' e e'
  htpy-eq-extension-dependent-type' e .e refl =
    refl-htpy-extension-dependent-type' e

  is-torsorial-htpy-extension-dependent-type' :
    (e : extension-dependent-type' i P f) →
    is-torsorial (htpy-extension-dependent-type' e)
  is-torsorial-htpy-extension-dependent-type' e =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-extension' e))
      ( map-extension' e , refl-htpy)
      ( is-torsorial-htpy (is-extension-map-extension' e))

  is-equiv-htpy-eq-extension-dependent-type' :
    (e e' : extension-dependent-type' i P f) →
    is-equiv (htpy-eq-extension-dependent-type' e e')
  is-equiv-htpy-eq-extension-dependent-type' e =
    fundamental-theorem-id
      ( is-torsorial-htpy-extension-dependent-type' e)
      ( htpy-eq-extension-dependent-type' e)

  extensionality-extension-dependent-type' :
    (e e' : extension-dependent-type' i P f) →
    (e ＝ e') ≃ (htpy-extension-dependent-type' e e')
  pr1 (extensionality-extension-dependent-type' e e') =
    htpy-eq-extension-dependent-type' e e'
  pr2 (extensionality-extension-dependent-type' e e') =
    is-equiv-htpy-eq-extension-dependent-type' e e'

  eq-htpy-extension-dependent-type' :
    (e e' : extension-dependent-type' i P f) →
    htpy-extension-dependent-type' e e' → e ＝ e'
  eq-htpy-extension-dependent-type' e e' =
    map-inv-equiv (extensionality-extension-dependent-type' e e')
```

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
    (g : (x : B) → P x) → is-trunc k (is-extension i f g)
  is-trunc-is-extension-dependent-type f is-trunc-P g =
    is-trunc-Π k λ x → is-trunc-P x (f x) (g (i x))

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

  is-contr-is-extension :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-prop (P (i x))) →
    (g : (x : B) → P x) → is-contr (is-extension i f g)
  is-contr-is-extension f is-prop-P g =
    is-contr-Π λ x → is-prop-P x (f x) (g (i x))

  is-prop-is-extension :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-set (P (i x))) →
    (g : (x : B) → P x) → is-prop (is-extension i f g)
  is-prop-is-extension f is-set-P g =
    is-prop-Π (λ x → is-set-P x (f x) (g (i x)))
```

## Examples

### Every dependent map is an extension of itself along the identity

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2} (f : (x : A) → P x)
  where

  is-extension-self : is-extension id f f
  is-extension-self = refl-htpy

  extension-self : extension-dependent-type id P f
  extension-self = (f , is-extension-self)
```

## See also

- [`orthogonal-factorization-systems.lifts-maps`](orthogonal-factorization-systems.lifts-maps.md)
  for the dual notion.
