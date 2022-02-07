# Sets

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.sets where

open import foundation-core.sets public

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using (_≃_)
open import foundation-core.propositions using (is-prop; UU-Prop)
open import foundation-core.truncation-levels using (zero-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_)

open import foundation.contractible-types using
  ( is-contr; is-trunc-is-contr)
open import foundation.truncated-types using
  ( is-trunc-Σ; is-trunc-prod; is-prop-is-trunc; is-trunc-Π;
    is-trunc-function-type; is-trunc-equiv-is-trunc)
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
  {l1 l2 : Level} (A : UU-Set l1) (B : pr1 A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Σ-Set A B) = Σ (type-Set A) (λ x → (type-Set (B x)))
pr2 (Σ-Set A B) = is-set-Σ (is-set-type-Set A) (λ x → is-set-type-Set (B x))
```

### Sets are closed under cartesian product types

```agda
abstract
  is-set-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A × B)
  is-set-prod = is-trunc-prod zero-𝕋
  
prod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
prod-Set A B = Σ-Set A (λ x → B)
```

### Being a set is a property

```agda
abstract
  is-prop-is-set :
    {l : Level} (A : UU l) → is-prop (is-set A)
  is-prop-is-set = is-prop-is-trunc zero-𝕋

is-set-Prop : {l : Level} → UU l → UU-Prop l
pr1 (is-set-Prop A) = is-set A
pr2 (is-set-Prop A) = is-prop-is-set A
```

### Products of families of sets are sets

```agda
abstract
  is-set-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-set (B x)) → is-set ((x : A) → (B x))
  is-set-Π = is-trunc-Π zero-𝕋

type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set' A B = (x : A) → type-Set (B x)

is-set-type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → is-set (type-Π-Set' A B)
is-set-type-Π-Set' A B =
  is-set-Π (λ x → is-set-type-Set (B x))

Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Π-Set' A B) = type-Π-Set' A B
pr2 (Π-Set' A B) = is-set-type-Π-Set' A B

type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set A B = type-Π-Set' (type-Set A) B

is-set-type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) →
  is-set (type-Π-Set A B)
is-set-type-Π-Set A B =
  is-set-type-Π-Set' (type-Set A) B

Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) →
  (type-Set A → UU-Set l2) → UU-Set (l1 ⊔ l2)
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

type-hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU (l1 ⊔ l2)
type-hom-Set A B = type-Set A → type-Set B

is-set-type-hom-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
  is-set (type-hom-Set A B)
is-set-type-hom-Set A B = is-set-function-type (is-set-type-Set B)

hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU-Set (l1 ⊔ l2)
pr1 (hom-Set A B) = type-hom-Set A B
pr2 (hom-Set A B) = is-set-type-hom-Set A B
```

### The type of equivalences between sets is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-set-equiv-is-set : is-set A → is-set B → is-set (A ≃ B)
  is-set-equiv-is-set = is-trunc-equiv-is-trunc zero-𝕋

module _
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2)
  where
  
  type-equiv-Set : UU (l1 ⊔ l2)
  type-equiv-Set = type-Set A ≃ type-Set B

  equiv-Set : UU-Set (l1 ⊔ l2)
  pr1 equiv-Set = type-equiv-Set
  pr2 equiv-Set = is-set-equiv-is-set (is-set-type-Set A) (is-set-type-Set B)

aut-Set :
  {l : Level} (X : UU-Set l) → UU-Set l
aut-Set X = equiv-Set X X
```
