# Small types

```agda
module foundation-core.small-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coherently-invertible-maps
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A type is said to be **small** with respect to a universe `UU l` if it is
[equivalent](foundation-core.equivalences.md) to a type in `UU l`.

## Definitions

### Small types

```agda
is-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-small l A = Σ (UU l) (λ X → A ≃ X)

module _
  {l l1 : Level} {A : UU l1} (H : is-small l A)
  where

  type-is-small : UU l
  type-is-small = pr1 H

  equiv-is-small : A ≃ type-is-small
  equiv-is-small = pr2 H

  inv-equiv-is-small : type-is-small ≃ A
  inv-equiv-is-small = inv-equiv equiv-is-small

  map-equiv-is-small : A → type-is-small
  map-equiv-is-small = map-equiv equiv-is-small

  map-inv-equiv-is-small : type-is-small → A
  map-inv-equiv-is-small = map-inv-equiv equiv-is-small

  is-section-map-inv-equiv-is-small :
    is-section map-equiv-is-small map-inv-equiv-is-small
  is-section-map-inv-equiv-is-small =
    is-section-map-inv-equiv equiv-is-small

  is-retraction-map-inv-equiv-is-small :
    is-retraction map-equiv-is-small map-inv-equiv-is-small
  is-retraction-map-inv-equiv-is-small =
    is-retraction-map-inv-equiv equiv-is-small

  is-equiv-map-inv-equiv-is-small : is-equiv map-inv-equiv-is-small
  is-equiv-map-inv-equiv-is-small = is-equiv-map-inv-equiv equiv-is-small

  coherence-map-inv-equiv-is-small :
    coherence-is-coherently-invertible
      ( map-equiv-is-small)
      ( map-inv-equiv-is-small)
      ( is-section-map-inv-equiv-is-small)
      ( is-retraction-map-inv-equiv-is-small)
  coherence-map-inv-equiv-is-small =
    coherence-map-inv-equiv equiv-is-small
```

### The subuniverse of `UU l1`-small types in `UU l2`

```agda
Small-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Small-Type l1 l2 = Σ (UU l2) (is-small l1)

module _
  {l1 l2 : Level} (A : Small-Type l1 l2)
  where

  type-Small-Type : UU l2
  type-Small-Type = pr1 A

  is-small-type-Small-Type : is-small l1 type-Small-Type
  is-small-type-Small-Type = pr2 A

  small-type-Small-Type : UU l1
  small-type-Small-Type = type-is-small is-small-type-Small-Type

  equiv-is-small-type-Small-Type :
    type-Small-Type ≃ small-type-Small-Type
  equiv-is-small-type-Small-Type =
    equiv-is-small is-small-type-Small-Type
```

## Properties

### Being small is a property

```agda
module _
  (l : Level) {l1 : Level} (A : UU l1)
  where

  is-proof-irrelevant-is-small : is-proof-irrelevant (is-small l A)
  is-proof-irrelevant-is-small (X , e) =
    is-contr-equiv'
      ( Σ (UU l) (λ Y → X ≃ Y))
      ( equiv-tot (equiv-precomp-equiv e))
      ( is-torsorial-equiv X)

  is-prop-is-small : is-prop (is-small l A)
  is-prop-is-small = is-prop-is-proof-irrelevant is-proof-irrelevant-is-small

  is-small-Prop : Prop (lsuc l ⊔ l1)
  is-small-Prop = (is-small l A , is-prop-is-small)
```

### Any type in `UU l1` is `l1`-small

```agda
is-small' : {l1 : Level} {A : UU l1} → is-small l1 A
is-small' {A = A} = (A , id-equiv)
```

### Every type of universe level `l1` is `(l1 ⊔ l2)`-small

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-small-lmax : is-small (l1 ⊔ l2) X
  is-small-lmax = (raise l2 X , compute-raise l2 X)

  is-contr-is-small-lmax :
    is-contr (is-small (l1 ⊔ l2) X)
  pr1 is-contr-is-small-lmax = is-small-lmax
  pr2 is-contr-is-small-lmax x = eq-is-prop (is-prop-is-small (l1 ⊔ l2) X)
```

### Every type of universe level `l` is `(lsuc l)`-small

```agda
is-small-lsuc : {l : Level} (X : UU l) → is-small (lsuc l) X
is-small-lsuc {l} = is-small-lmax (lsuc l)
```

### Small types are closed under equivalences

```agda
is-small-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU l2) →
  A ≃ B → is-small l3 B → is-small l3 A
is-small-equiv B e (X , h) = (X , h ∘e e)

is-small-equiv' :
  {l1 l2 l3 : Level} (A : UU l1) {B : UU l2} →
  A ≃ B → is-small l3 A → is-small l3 B
is-small-equiv' A e = is-small-equiv A (inv-equiv e)

equiv-is-small-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-small l3 A ≃ is-small l3 B
equiv-is-small-equiv e =
  equiv-tot (equiv-precomp-equiv (inv-equiv e))
```

### The universe of `UU l1`-small types in `UU l2` is equivalent to the universe of `UU l2`-small types in `UU l1`

```agda
equiv-Small-Type :
  (l1 l2 : Level) → Small-Type l1 l2 ≃ Small-Type l2 l1
equiv-Small-Type l1 l2 =
  ( equiv-tot (λ X → equiv-tot (λ Y → equiv-inv-equiv))) ∘e
  ( equiv-left-swap-Σ)
```

### Being small is closed under mere equivalences

```agda
is-small-mere-equiv :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
  is-small l B → is-small l A
is-small-mere-equiv l e H =
  apply-universal-property-trunc-Prop e
    ( is-small-Prop l _)
    ( λ e' → is-small-equiv _ e' H)
```

### The equality type of the smallness predicate is equivalent to the fiber of `equiv-eq`

This computation uses the function extensionality axiom.

```agda
compute-eq-is-small :
  {l1 l2 : Level} {X : UU l1} (α β : is-small l2 X) →
  (α ＝ β) ≃ fiber equiv-eq (equiv-is-small β ∘e inv-equiv-is-small α)
compute-eq-is-small {X = X} (Y , α) (Y' , α') =
  equivalence-reasoning
  ( (Y , α) ＝ (Y' , α'))
  ≃ Σ (Y ＝ Y') (λ x → dependent-identification (λ Y → X ≃ Y) x α α')
    by equiv-pair-eq-Σ (Y , α) (Y' , α')
  ≃ Σ (Y ＝ Y') (λ x → equiv-eq x ∘e α ＝ α')
    by equiv-tot (λ p → equiv-concat (tr-equiv-type-right p α) α')
  ≃ Σ (Y ＝ Y') (λ x → equiv-eq x ＝ α' ∘e inv-equiv α)
    by equiv-tot (λ p → equiv-right-transpose-equiv-comp α (equiv-eq p) α')
```

### Any contractible type is small

```agda
is-small-is-contr :
  (l : Level) {l1 : Level} {A : UU l1} → is-contr A → is-small l A
is-small-is-contr l H = (raise-unit l , equiv-is-contr H is-contr-raise-unit)
```

### The unit type is small with respect to any universe

```agda
is-small-unit : {l : Level} → is-small l unit
is-small-unit = is-small-is-contr _ is-contr-unit
```

### Small types are closed under dependent pair types

```agda
is-small-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-small l4 (B x)) → is-small (l3 ⊔ l4) (Σ A B)
pr1 (is-small-Σ {B = B} (X , e) H) =
  Σ X (λ x → pr1 (H (map-inv-equiv e x)))
pr2 (is-small-Σ {B = B} (X , e) H) =
  equiv-Σ
    ( λ x → pr1 (H (map-inv-equiv e x)))
    ( e)
    ( λ a →
      ( equiv-tr
        ( λ t → pr1 (H t))
        ( inv (is-retraction-map-inv-equiv e a))) ∘e
      ( pr2 (H a)))

Σ-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Small-Type l1 l2) →
  (B : type-Small-Type A → Small-Type l3 l4) → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Σ-Small-Type A B) = Σ (type-Small-Type A) (λ a → type-Small-Type (B a))
pr2 (Σ-Small-Type {l1} {l2} {l3} {l4} A B) =
  is-small-Σ (is-small-type-Small-Type A) (λ a → is-small-type-Small-Type (B a))
```

### Small types are closed under cartesian products

```agda
is-small-product :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A × B)
is-small-product H K = is-small-Σ H (λ a → K)

product-Small-Type :
  {l1 l2 l3 l4 : Level} →
  Small-Type l1 l2 → Small-Type l3 l4 → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (product-Small-Type A B) = type-Small-Type A × type-Small-Type B
pr2 (product-Small-Type A B) =
  is-small-product (is-small-type-Small-Type A) (is-small-type-Small-Type B)
```

### Any product of small types indexed by a small type is small

```agda
is-small-Π :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-small l4 (B x)) →
  is-small (l3 ⊔ l4) ((x : A) → B x)
pr1 (is-small-Π {B = B} (X , e) H) =
  (x : X) → pr1 (H (map-inv-equiv e x))
pr2 (is-small-Π {B = B} (X , e) H) =
  equiv-Π
    ( λ (x : X) → pr1 (H (map-inv-equiv e x)))
    ( e)
    ( λ a →
      ( equiv-tr
      ( λ t → pr1 (H t))
        ( inv (is-retraction-map-inv-equiv e a))) ∘e
      ( pr2 (H a)))

Π-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Small-Type l1 l2) →
  (type-Small-Type A → Small-Type l3 l4) → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Π-Small-Type A B) = (a : type-Small-Type A) → type-Small-Type (B a)
pr2 (Π-Small-Type A B) =
  is-small-Π (is-small-type-Small-Type A) (λ a → is-small-type-Small-Type (B a))
```

### Small types are closed under function types

```agda
is-small-function-type :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A → B)
is-small-function-type H K = is-small-Π H (λ a → K)
```

### Small types are closed under coproduct types

```agda
is-small-coproduct :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A + B)
pr1 (is-small-coproduct H K) = type-is-small H + type-is-small K
pr2 (is-small-coproduct H K) =
  equiv-coproduct (equiv-is-small H) (equiv-is-small K)

coproduct-Small-Type :
  {l1 l2 l3 l4 : Level} →
  Small-Type l1 l2 → Small-Type l3 l4 → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (coproduct-Small-Type A B) = type-Small-Type A + type-Small-Type B
pr2 (coproduct-Small-Type A B) =
  is-small-coproduct (is-small-type-Small-Type A) (is-small-type-Small-Type B)
```

### The type of logical equivalences between small types is small

```agda
is-small-logical-equivalence :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A ↔ B)
is-small-logical-equivalence H K =
  is-small-product (is-small-function-type H K) (is-small-function-type K H)
```

## See also

- [Small maps](foundation.small-maps.md)
- The `is-essentially-in-subuniverse` predicate in
  [`foundation.subuniverses`](foundation.subuniverses.md)
