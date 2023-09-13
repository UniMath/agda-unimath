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
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A type is said to be small with respect to a universe `UU l` if it is equivalent
to a type in `UU l`.

## Definitions

### Small types

```agda
is-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-small l A = Σ (UU l) (λ X → A ≃ X)

type-is-small :
  {l l1 : Level} {A : UU l1} → is-small l A → UU l
type-is-small = pr1

equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → A ≃ type-is-small H
equiv-is-small = pr2

inv-equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → type-is-small H ≃ A
inv-equiv-is-small H = inv-equiv (equiv-is-small H)

map-equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → A → type-is-small H
map-equiv-is-small H = map-equiv (equiv-is-small H)

map-inv-equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → type-is-small H → A
map-inv-equiv-is-small H = map-inv-equiv (equiv-is-small H)
```

### The universe of `UU l1`-small types in a universe `UU l2`

```agda
Small-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Small-Type l1 l2 = Σ (UU l2) (is-small l1)

module _
  {l1 l2 : Level} (X : Small-Type l1 l2)
  where

  type-Small-Type : UU l2
  type-Small-Type = pr1 X

  is-small-type-Small-Type : is-small l1 type-Small-Type
  is-small-type-Small-Type = pr2 X

  small-type-Small-Type : UU l1
  small-type-Small-Type = type-is-small is-small-type-Small-Type

  equiv-is-small-type-Small-Type : type-Small-Type ≃ small-type-Small-Type
  equiv-is-small-type-Small-Type = equiv-is-small is-small-type-Small-Type
```

## Properties

### Being small is a property

```agda
is-prop-is-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-small l A)
is-prop-is-small l A =
  is-prop-is-proof-irrelevant
    ( λ Xe →
      is-contr-equiv'
        ( Σ (UU l) (λ Y → (pr1 Xe) ≃ Y))
        ( equiv-tot ((λ Y → equiv-precomp-equiv (pr2 Xe) Y)))
        ( is-contr-total-equiv (pr1 Xe)))

is-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → Prop (lsuc l ⊔ l1)
pr1 (is-small-Prop l A) = is-small l A
pr2 (is-small-Prop l A) = is-prop-is-small l A
```

### Any type in `UU l1` is `l1`-small

```agda
is-small' : {l1 : Level} {A : UU l1} → is-small l1 A
pr1 (is-small' {A = A}) = A
pr2 is-small' = id-equiv
```

### Every type of universe level `l1` is `l1 ⊔ l2`-small

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-small-lmax : is-small (l1 ⊔ l2) X
  pr1 is-small-lmax = raise l2 X
  pr2 is-small-lmax = compute-raise l2 X

  is-contr-is-small-lmax :
    is-contr (is-small (l1 ⊔ l2) X)
  pr1 is-contr-is-small-lmax = is-small-lmax
  pr2 is-contr-is-small-lmax x = eq-is-prop (is-prop-is-small (l1 ⊔ l2) X)
```

### Every type of universe level `l` is `UU (lsuc l)`-small

```agda
is-small-lsuc : {l : Level} (X : UU l) → is-small (lsuc l) X
is-small-lsuc {l} X = is-small-lmax (lsuc l) X
```

### Small types are closed under equivalences

```agda
is-small-equiv :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU l2) →
  A ≃ B → is-small l3 B → is-small l3 A
pr1 (is-small-equiv B e (pair X h)) = X
pr2 (is-small-equiv B e (pair X h)) = h ∘e e

is-small-equiv' :
  {l1 l2 l3 : Level} (A : UU l1) {B : UU l2} →
  A ≃ B → is-small l3 A → is-small l3 B
is-small-equiv' A e = is-small-equiv A (inv-equiv e)
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

### Any contractible type is small

```agda
is-small-is-contr :
  (l : Level) {l1 : Level} {A : UU l1} → is-contr A → is-small l A
pr1 (is-small-is-contr l H) = raise-unit l
pr2 (is-small-is-contr l H) = equiv-is-contr H is-contr-raise-unit
```

### Small types are closed under dependent pair types

```agda
is-small-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-small l4 (B x)) → is-small (l3 ⊔ l4) (Σ A B)
pr1 (is-small-Σ {B = B} (pair X e) H) =
  Σ X (λ x → pr1 (H (map-inv-equiv e x)))
pr2 (is-small-Σ {B = B} (pair X e) H) =
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
is-small-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A × B)
is-small-prod H K = is-small-Σ H (λ a → K)

prod-Small-Type :
  {l1 l2 l3 l4 : Level} →
  Small-Type l1 l2 → Small-Type l3 l4 → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (prod-Small-Type A B) = type-Small-Type A × type-Small-Type B
pr2 (prod-Small-Type A B) =
  is-small-prod (is-small-type-Small-Type A) (is-small-type-Small-Type B)
```

### Any product of small types indexed by a small type is small

```agda
is-small-Π :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-small l4 (B x)) →
  is-small (l3 ⊔ l4) ((x : A) → B x)
pr1 (is-small-Π {B = B} (pair X e) H) =
  (x : X) → pr1 (H (map-inv-equiv e x))
pr2 (is-small-Π {B = B} (pair X e) H) =
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
is-small-coprod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A + B)
pr1 (is-small-coprod H K) = type-is-small H + type-is-small K
pr2 (is-small-coprod H K) = equiv-coprod (equiv-is-small H) (equiv-is-small K)

coprod-Small-Type :
  {l1 l2 l3 l4 : Level} →
  Small-Type l1 l2 → Small-Type l3 l4 → Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (coprod-Small-Type A B) = type-Small-Type A + type-Small-Type B
pr2 (coprod-Small-Type A B) =
  is-small-coprod (is-small-type-Small-Type A) (is-small-type-Small-Type B)
```

### The type of logical equivalences between small types is small

```agda
is-small-logical-equivalence :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} →
  is-small l3 A → is-small l4 B → is-small (l3 ⊔ l4) (A ↔ B)
is-small-logical-equivalence H K =
  is-small-prod (is-small-function-type H K) (is-small-function-type K H)
```
