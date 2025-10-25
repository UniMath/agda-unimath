# Extensions of maps

```agda
module orthogonal-factorization-systems.extensions-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.precomposition-functions
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.monomorphisms
open import foundation.postcomposition-functions
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.precomposition-dependent-functions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

An **extension** of a map `f : (x : A) → P x` along a map `i : A → B` is a map
`g : (y : B) → Q y` such that `Q` restricts along `i` to `P` and `g` restricts
along `i` to `f`.

```text
  A
  |  \
  i    f
  |      \
  ∨       ∨
  B - g -> P
```

## Definition

### Extensions of dependent functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-extension :
    {P : B → UU l3} →
    ((x : A) → P (i x)) → ((y : B) → P y) → UU (l1 ⊔ l3)
  is-extension f g = f ~ (g ∘ i)

  extension-dependent-type :
    (P : B → UU l3) →
    ((x : A) → P (i x)) → UU (l1 ⊔ l2 ⊔ l3)
  extension-dependent-type P f = Σ ((y : B) → P y) (is-extension f)

  extension :
    {X : UU l3} → (A → X) → UU (l1 ⊔ l2 ⊔ l3)
  extension {X} = extension-dependent-type (λ _ → X)

  total-extension-dependent-type : (P : B → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension-dependent-type P =
    Σ ((x : A) → P (i x)) (extension-dependent-type P)

  total-extension : (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-extension X = total-extension-dependent-type (λ _ → X)

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

## Operations

### Vertical composition of extensions of maps

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

### Horizontal composition of extensions of maps

```text
           A
        /  |  \
      f    g    h
    /      |      \
   ∨       ∨       ∨
  B - i -> C - j -> P
```

#### Horizontal composition of extensions of dependent functions

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

#### Horizontal composition of extensions of ordinary maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  {f : A → B} {g : A → C} {h : A → X}
  {i : B → C} {j : C → X}
  where

  is-extension-comp-horizontal :
    (I : is-extension f g i) → is-extension g h j → is-extension f h (j ∘ i)
  is-extension-comp-horizontal I J x = (J x) ∙ ap j (I x)
```

### Left whiskering of extensions of maps

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

### Right whiskering of extensions of maps

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

### Characterizing identifications of extensions of maps

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

### Computing extension types as a dependent product

Extension types are equivalent to fibers of precomposition maps, which in turn
have a Π-type characterization. Given `i : A → B` and `g : B → C`, then

```text
  extension i g ≃ ((y : B) → Σ (c : C), (x : X) → (i x ＝ y) → (c ＝ g y)).
```

We give 4 different formulations of this equivalence for both the nondependent
and dependent extension type.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {C : UU l3} (g : A → C)
  where


  equiv-fiber-Π-curry-precomp-extension :
    extension i g ≃ ((b : B) → Σ C (λ u → (a : A) → i a ＝ b → g a ＝ u))
  equiv-fiber-Π-curry-precomp-extension =
    ( compute-fiber-Π-curry-precomp i g) ∘e
    ( inv-equiv (compute-extension-fiber-precomp i g))

  equiv-fiber-Π-curry-precomp-extension' :
    extension i g ≃ ((b : B) → Σ C (λ u → (a : A) → b ＝ i a → u ＝ g a))
  equiv-fiber-Π-curry-precomp-extension' =
    ( compute-fiber-Π-curry-precomp' i g) ∘e
    ( inv-equiv (compute-extension-fiber-precomp i g))

  equiv-fiber-Π-precomp-extension :
    extension i g ≃ fiber-Π-precomp i g
  equiv-fiber-Π-precomp-extension =
    ( compute-fiber-Π-precomp i g) ∘e
    ( inv-equiv (compute-extension-fiber-precomp i g))

  equiv-fiber-Π-precomp-extension' :
    extension i g ≃ fiber-Π-precomp' i g
  equiv-fiber-Π-precomp-extension' =
    ( compute-fiber-Π-precomp' i g) ∘e
    ( inv-equiv (compute-extension-fiber-precomp i g))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  {P : B → UU l3} (g : (x : A) → P (i x))
  where

  equiv-fiber-Π-curry-precomp-Π-extension-dependent-type :
    extension-dependent-type i P g ≃ fiber-Π-curry-precomp-Π i P g
  equiv-fiber-Π-curry-precomp-Π-extension-dependent-type =
    ( compute-fiber-Π-curry-precomp-Π i P g) ∘e
    ( inv-equiv (compute-extension-fiber-precomp-Π i P g))

  equiv-fiber-Π-curry-precomp-Π-extension-dependent-type' :
    extension-dependent-type i P g ≃ fiber-Π-curry-precomp-Π' i P g
  equiv-fiber-Π-curry-precomp-Π-extension-dependent-type' =
    ( compute-fiber-Π-curry-precomp-Π' i P g) ∘e
    ( inv-equiv (compute-extension-fiber-precomp-Π i P g))

  equiv-fiber-Π-precomp-Π-extension-dependent-type :
    extension-dependent-type i P g ≃ fiber-Π-precomp-Π i P g
  equiv-fiber-Π-precomp-Π-extension-dependent-type =
    ( compute-fiber-Π-precomp-Π i P g) ∘e
    ( inv-equiv (compute-extension-fiber-precomp-Π i P g))

  equiv-fiber-Π-precomp-Π-extension-dependent-type' :
    extension-dependent-type i P g ≃ fiber-Π-precomp-Π' i P g
  equiv-fiber-Π-precomp-Π-extension-dependent-type' =
    ( compute-fiber-Π-precomp-Π' i P g) ∘e
    ( inv-equiv (compute-extension-fiber-precomp-Π i P g))
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

  inv-compute-total-extension :
    {X : UU l3} → total-extension i X ≃ (B → X)
  inv-compute-total-extension = inv-compute-total-extension-dependent-type

  compute-total-extension :
    {X : UU l3} → (B → X) ≃ total-extension i X
  compute-total-extension = compute-total-extension-dependent-type
```

### The truncation level of the type of extensions is bounded by the truncation level of the codomains

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-trunc-is-extension-dependent-type :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-trunc (succ-𝕋 k) (P (i x))) →
    (g : (x : B) → P x) → is-trunc k (is-extension i f g)
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

  is-contr-is-extension :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-prop (P (i x))) →
    (g : (x : B) → P x) → is-contr (is-extension i f g)
  is-contr-is-extension f is-prop-P g =
    is-contr-Π (λ x → is-prop-P x (f x) (g (i x)))

  is-prop-is-extension :
    {P : B → UU l3} (f : (x : A) → P (i x)) →
    ((x : A) → is-set (P (i x))) →
    (g : (x : B) → P x) → is-prop (is-extension i f g)
  is-prop-is-extension f is-set-P g =
    is-prop-Π (λ x → is-set-P x (f x) (g (i x)))
```

## Examples

### Every map is an extension of itself along the identity

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2} (f : (x : A) → P x)
  where

  is-extension-self : is-extension id f f
  is-extension-self = refl-htpy

  extension-self : extension-dependent-type id P f
  extension-self = (f , is-extension-self)
```

### The identity is an extension of every map along themselves

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-extension-along-self : is-extension f f id
  is-extension-along-self = refl-htpy

  extension-along-self : extension f f
  extension-along-self = (id , is-extension-along-self)
```

## See also

- [`orthogonal-factorization-systems.lifts-maps`](orthogonal-factorization-systems.lifts-maps.md)
  for the dual notion.
