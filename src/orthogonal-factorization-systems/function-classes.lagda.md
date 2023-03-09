# Function classes

<details><summary>Imports</summary>
```agda
module orthogonal-factorization-systems.function-classes where
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels
```
</details>

## Idea

A function class is a subtype of the type of all functions.

## Definition

```agda
function-class : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
function-class l1 l2 l3 = {A : UU l1} {B : UU l2} → (A → B) → Prop l3
```

### Function classes containing identities and equivalences

```agda
has-identity-maps-function-class :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
has-identity-maps-function-class {l1} {l2} c = (A : UU l1) → type-Prop (c (id {A = A}))

identity-maps-function-class :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
identity-maps-function-class l1 l2 = Σ (function-class l1 l1 l2) (has-identity-maps-function-class)

has-equivalences-function-class :
  {l1 l2 l3 : Level} → function-class l1 l2 l3 → UU (lsuc l1 ⊔ lsuc l2 ⊔ l3)
has-equivalences-function-class {l1} {l2} c =
  (A : UU l1) (B : UU l2) (f : A → B) → is-equiv f → type-Prop (c f)

equivalences-function-class :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
equivalences-function-class l1 l2 l3 =
  Σ (function-class l1 l2 l3) (has-equivalences-function-class)
```

We say a function class is **composition closed** if it is closed under taking
composites.

```agda
is-composition-closed-function-class :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
is-composition-closed-function-class {l1} {l2} c =
  (A B C : UU l1) (f : A → B) (g : B → C) →
  type-Prop (c f) → type-Prop (c g) →
  type-Prop (c (g ∘ f))

composition-closed-function-class :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
composition-closed-function-class l1 l2 =
  Σ (function-class l1 l1 l2) (is-composition-closed-function-class)
```

A function class that has identities and is composition closed
is morally a ∞-subprecategory of the ∞-precategory of small types.

```agda
is-function-precat :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
is-function-precat c =
  has-identity-maps-function-class c × is-composition-closed-function-class c

function-precat : {l1 l2 : Level} → UU (lsuc l1 ⊔ lsuc l2)
function-precat {l1} {l2} = Σ (function-class l1 l1 l2) (is-function-precat)
```

## Properties

### Having identities is a property

```agda
has-identity-maps-function-class-Prop :
  {l1 l2 : Level} → function-class l1 l1 l2 → Prop (lsuc l1 ⊔ l2)
has-identity-maps-function-class-Prop {l1} {l2} c =
  Π-Prop (UU l1) λ A → c (id {A = A})

is-prop-has-identity-maps-function-class :
  {l1 l2 : Level} (c : function-class l1 l1 l2) →
  is-prop (has-identity-maps-function-class c)
is-prop-has-identity-maps-function-class =
  is-prop-type-Prop ∘ has-identity-maps-function-class-Prop
```

### Having equivalences is a property

```agda
has-equivalences-function-class-Prop :
  {l1 l2 l3 : Level} → function-class l1 l2 l3 → Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3)
has-equivalences-function-class-Prop {l1} {l2} {l3} c =
  Π-Prop (UU l1) λ A → Π-Prop (UU l2) λ B → Π-Prop (A → B)
    ( λ f → function-Prop (is-equiv f) (c f))

is-prop-has-equivalences-function-class :
  {l1 l2 l3 : Level} (c : function-class l1 l2 l3) →
  is-prop (has-equivalences-function-class c)
is-prop-has-equivalences-function-class =
  is-prop-type-Prop ∘ has-equivalences-function-class-Prop
```

### Composition closedness is a property

```agda
is-prop-is-composition-closed-function-class :
  {l1 l2 : Level} (c : function-class l1 l1 l2) →
  is-prop (is-composition-closed-function-class c)
is-prop-is-composition-closed-function-class c =
  is-prop-Π λ A → is-prop-Π λ B → is-prop-Π λ C →
    is-prop-Π λ f → is-prop-Π λ g →
      is-prop-function-type (is-prop-function-type
        ( is-prop-type-Prop (c (g ∘ f))))

is-composition-closed-function-class-Prop :
  {l1 l2 : Level} → function-class l1 l1 l2 → Prop (lsuc l1 ⊔ l2)
pr1 (is-composition-closed-function-class-Prop c) =
  is-composition-closed-function-class c
pr2 (is-composition-closed-function-class-Prop c) =
  is-prop-is-composition-closed-function-class c
```

```agda
is-function-precat-Prop :
  {l1 l2 : Level} → function-class l1 l1 l2 → Prop (lsuc l1 ⊔ l2)
is-function-precat-Prop c =
  prod-Prop
    ( has-identity-maps-function-class-Prop c)
    ( is-composition-closed-function-class-Prop c)

is-prop-is-function-precat :
  {l1 l2 : Level} (c : function-class l1 l1 l2) → is-prop (is-function-precat c)
is-prop-is-function-precat = is-prop-type-Prop ∘ is-function-precat-Prop
```
