# Sets

```agda
module foundation.sets where

open import foundation-core.sets public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-truncated-types
open import foundation.logical-equivalences
open import foundation.subuniverses
open import foundation.truncated-types
open import foundation.univalent-type-families
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.precomposition-functions
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncation-levels
```

</details>

## Properties

### The type of all sets in a universe is a 1-type

```agda
is-1-type-Set : {l : Level} → is-1-type (Set l)
is-1-type-Set = is-trunc-Truncated-Type zero-𝕋

Set-1-Type : (l : Level) → 1-Type (lsuc l)
pr1 (Set-1-Type l) = Set l
pr2 (Set-1-Type l) = is-1-type-Set
```

### Any contractible type is a set

```agda
abstract
  is-set-is-contr :
    {l : Level} {A : UU l} → is-contr A → is-set A
  is-set-is-contr = is-trunc-is-contr zero-𝕋
```

### Sets are closed under dependent pair types

```agda
abstract
  is-set-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
  is-set-Σ = is-trunc-Σ {k = zero-𝕋}

Σ-Set :
  {l1 l2 : Level} (A : Set l1) (B : pr1 A → Set l2) → Set (l1 ⊔ l2)
pr1 (Σ-Set A B) = Σ (type-Set A) (λ x → (type-Set (B x)))
pr2 (Σ-Set A B) = is-set-Σ (is-set-type-Set A) (λ x → is-set-type-Set (B x))
```

### Sets are closed under cartesian product types

```agda
abstract
  is-set-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A × B)
  is-set-product = is-trunc-product zero-𝕋

product-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
product-Set A B = Σ-Set A (λ x → B)
```

### Being a set is a property

```agda
abstract
  is-prop-is-set :
    {l : Level} (A : UU l) → is-prop (is-set A)
  is-prop-is-set = is-prop-is-trunc zero-𝕋

is-set-Prop : {l : Level} → UU l → Prop l
pr1 (is-set-Prop A) = is-set A
pr2 (is-set-Prop A) = is-prop-is-set A
```

### The inclusion of sets into the universe is an embedding

```agda
emb-type-Set : (l : Level) → Set l ↪ UU l
emb-type-Set l = emb-type-Truncated-Type l zero-𝕋
```

### Products of families of sets are sets

```agda
abstract
  is-set-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-set (B x)) → is-set ((x : A) → (B x))
  is-set-Π = is-trunc-Π zero-𝕋

type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → Set l2) → UU (l1 ⊔ l2)
type-Π-Set' A B = (x : A) → type-Set (B x)

is-set-type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → Set l2) → is-set (type-Π-Set' A B)
is-set-type-Π-Set' A B =
  is-set-Π (λ x → is-set-type-Set (B x))

Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → Set l2) → Set (l1 ⊔ l2)
pr1 (Π-Set' A B) = type-Π-Set' A B
pr2 (Π-Set' A B) = is-set-type-Π-Set' A B

function-Set :
  {l1 l2 : Level} (A : UU l1) (B : Set l2) → Set (l1 ⊔ l2)
function-Set A B = Π-Set' A (λ x → B)

type-Π-Set :
  {l1 l2 : Level} (A : Set l1) (B : type-Set A → Set l2) → UU (l1 ⊔ l2)
type-Π-Set A B = type-Π-Set' (type-Set A) B

is-set-type-Π-Set :
  {l1 l2 : Level} (A : Set l1) (B : type-Set A → Set l2) →
  is-set (type-Π-Set A B)
is-set-type-Π-Set A B =
  is-set-type-Π-Set' (type-Set A) B

Π-Set :
  {l1 l2 : Level} (A : Set l1) →
  (type-Set A → Set l2) → Set (l1 ⊔ l2)
pr1 (Π-Set A B) = type-Π-Set A B
pr2 (Π-Set A B) = is-set-type-Π-Set A B
```

### The type of functions into a set is a set

```agda
abstract
  is-set-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set B → is-set (A → B)
  is-set-function-type = is-trunc-function-type zero-𝕋

hom-Set :
  {l1 l2 : Level} → Set l1 → Set l2 → UU (l1 ⊔ l2)
hom-Set A B = type-Set A → type-Set B

is-set-hom-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) →
  is-set (hom-Set A B)
is-set-hom-Set A B = is-set-function-type (is-set-type-Set B)

hom-set-Set :
  {l1 l2 : Level} → Set l1 → Set l2 → Set (l1 ⊔ l2)
pr1 (hom-set-Set A B) = hom-Set A B
pr2 (hom-set-Set A B) = is-set-hom-Set A B

precomp-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : Set l3) →
  (B → type-Set C) → (A → type-Set C)
precomp-Set f C = precomp f (type-Set C)
```

### The type of equivalences between sets is a set

```agda
abstract
  is-set-equiv-is-set :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A ≃ B)
  is-set-equiv-is-set = is-trunc-equiv-is-trunc zero-𝕋

module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where

  equiv-Set : UU (l1 ⊔ l2)
  equiv-Set = type-Set A ≃ type-Set B

  equiv-set-Set : Set (l1 ⊔ l2)
  pr1 equiv-set-Set = equiv-Set
  pr2 equiv-set-Set =
    is-set-equiv-is-set (is-set-type-Set A) (is-set-type-Set B)
```

### Extensionality of sets

```agda
module _
  {l : Level} (X : Set l)
  where

  equiv-eq-Set : (Y : Set l) → X ＝ Y → equiv-Set X Y
  equiv-eq-Set = equiv-eq-subuniverse is-set-Prop X

  abstract
    is-torsorial-equiv-Set : is-torsorial (λ (Y : Set l) → equiv-Set X Y)
    is-torsorial-equiv-Set =
      is-torsorial-equiv-subuniverse is-set-Prop X

  abstract
    is-equiv-equiv-eq-Set : (Y : Set l) → is-equiv (equiv-eq-Set Y)
    is-equiv-equiv-eq-Set = is-equiv-equiv-eq-subuniverse is-set-Prop X

  eq-equiv-Set : (Y : Set l) → equiv-Set X Y → X ＝ Y
  eq-equiv-Set Y = eq-equiv-subuniverse is-set-Prop

  extensionality-Set : (Y : Set l) → (X ＝ Y) ≃ equiv-Set X Y
  pr1 (extensionality-Set Y) = equiv-eq-Set Y
  pr2 (extensionality-Set Y) = is-equiv-equiv-eq-Set Y
```

### If a type embeds into a set, then it is a set

```agda
abstract
  is-set-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-set B → is-set A
  is-set-is-emb = is-trunc-is-emb neg-one-𝕋

abstract
  is-set-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ B) → is-set B → is-set A
  is-set-emb = is-trunc-emb neg-one-𝕋
```

### Any function from a proposition into a set is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb-is-prop-is-set : is-prop A → is-set B → {f : A → B} → is-emb f
  is-emb-is-prop-is-set is-prop-A is-set-B {f} =
    is-emb-is-prop-map (λ b → is-prop-Σ is-prop-A (λ a → is-set-B (f a) b))
```

### Sets are `k+2`-truncated for any `k`

```agda
is-trunc-is-set :
  {l : Level} (k : 𝕋) {A : UU l} → is-set A → is-trunc (succ-𝕋 (succ-𝕋 k)) A
is-trunc-is-set neg-two-𝕋 is-set-A = is-set-A
is-trunc-is-set (succ-𝕋 k) is-set-A =
  is-trunc-succ-is-trunc (succ-𝕋 (succ-𝕋 k)) (is-trunc-is-set k is-set-A)

set-Truncated-Type :
  {l : Level} (k : 𝕋) → Set l → Truncated-Type l (succ-𝕋 (succ-𝕋 k))
pr1 (set-Truncated-Type k A) = type-Set A
pr2 (set-Truncated-Type k A) = is-trunc-is-set k (is-set-type-Set A)
```

### The type of equivalences is a set if the domain or codomain is a set

```agda
abstract
  is-set-equiv-is-set-codomain :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-set B → is-set (A ≃ B)
  is-set-equiv-is-set-codomain = is-trunc-equiv-is-trunc-codomain neg-one-𝕋

  is-set-equiv-is-set-domain :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-set A → is-set (A ≃ B)
  is-set-equiv-is-set-domain = is-trunc-equiv-is-trunc-domain neg-one-𝕋
```

### The canonical type family over `Set` is univalent

```agda
is-univalent-type-Set : {l : Level} → is-univalent (type-Set {l})
is-univalent-type-Set = is-univalent-inclusion-subuniverse is-set-Prop
```

### The subtype of of preimages of an element of a Set

```agda
preimage-Set :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) → (A → type-Set B) → type-Set B →
  subtype l2 A
preimage-Set B f b a = Id-Prop B (f a) b

is-in-preimage-Set :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) → (A → type-Set B) → type-Set B →
  A → UU l2
is-in-preimage-Set B f b a = type-Prop (preimage-Set B f b a)
```
