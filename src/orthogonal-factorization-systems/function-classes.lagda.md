# Function classes

```agda
module orthogonal-factorization-systems.function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.pullback-squares
open import foundation.universe-levels
```

</details>

## Idea

A **function class** is a [subtype](foundation.subtypes.md) of the type of all
functions in a given universe.

## Definition

```agda
function-class : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
function-class l1 l2 l3 = {A : UU l1} {B : UU l2} → (A → B) → Prop l3
```

### Function classes containing identities or equivalences

```agda
has-identity-maps-function-class :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
has-identity-maps-function-class {l1} {l2} c =
  (A : UU l1) → type-Prop (c (id {A = A}))

identity-maps-function-class :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
identity-maps-function-class l1 l2 =
  Σ (function-class l1 l1 l2) (has-identity-maps-function-class)

has-equivalences-function-class :
  {l1 l2 l3 : Level} → function-class l1 l2 l3 → UU (lsuc l1 ⊔ lsuc l2 ⊔ l3)
has-equivalences-function-class {l1} {l2} c =
  (A : UU l1) (B : UU l2) (f : A → B) → is-equiv f → type-Prop (c f)

equivalences-function-class :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
equivalences-function-class l1 l2 l3 =
  Σ (function-class l1 l2 l3) (has-equivalences-function-class)
```

### Composition closed function classes

We say a function class is **composition closed** if it is closed under taking
composites.

```agda
is-closed-under-composition-function-class :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
is-closed-under-composition-function-class {l1} {l2} c =
  (A B C : UU l1) (f : A → B) (g : B → C) →
  type-Prop (c f) → type-Prop (c g) →
  type-Prop (c (g ∘ f))

composition-closed-function-class :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
composition-closed-function-class l1 l2 =
  Σ (function-class l1 l1 l2) (is-closed-under-composition-function-class)
```

## Pullback-stable function classes

A function class is said to be **pullback-stable** if given a function in it,
then its pullback along any map is also in the function class.

```agda
is-pullback-stable-function-class :
  {l1 l2 l3 : Level} (l : Level) → function-class l1 l2 l3 →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l)
is-pullback-stable-function-class {l1} {l2} l F =
  (A : UU l1) (B C : UU l2) (f : A → C) (g : B → C)
  (c : Σ (UU l1) (pullback-cone l f g)) →
  type-Prop (F f) → type-Prop (F (horizontal-map-pullback-cone f g (pr2 c)))

pullback-stable-function-class :
  (l1 l2 l3 l4 : Level) → UU (lsuc (l1 ⊔ l2 ⊔ l3 ⊔ l4))
pullback-stable-function-class l1 l2 l3 l4 =
  Σ (function-class l1 l2 l3) (is-pullback-stable-function-class l4)
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
is-prop-is-closed-under-composition-function-class :
  {l1 l2 : Level} (c : function-class l1 l1 l2) →
  is-prop (is-closed-under-composition-function-class c)
is-prop-is-closed-under-composition-function-class c =
  is-prop-Π λ A → is-prop-Π λ B → is-prop-Π λ C →
    is-prop-Π λ f → is-prop-Π λ g →
      is-prop-function-type (is-prop-function-type
        ( is-prop-type-Prop (c (g ∘ f))))

is-closed-under-composition-function-class-Prop :
  {l1 l2 : Level} → function-class l1 l1 l2 → Prop (lsuc l1 ⊔ l2)
pr1 (is-closed-under-composition-function-class-Prop c) =
  is-closed-under-composition-function-class c
pr2 (is-closed-under-composition-function-class-Prop c) =
  is-prop-is-closed-under-composition-function-class c
```

### Being pullback-stable is a property

```agda
is-prop-is-pullback-stable-function-class :
  {l1 l2 l3 : Level} (l : Level) (F : function-class l1 l2 l3) →
  is-prop (is-pullback-stable-function-class l F)
is-prop-is-pullback-stable-function-class l F =
  is-prop-Π λ A → is-prop-Π λ B → is-prop-Π λ C → is-prop-Π
  λ f → is-prop-Π λ g → is-prop-Π λ c →
  is-prop-function-type
    ( is-prop-type-Prop (F (horizontal-map-pullback-cone f g (pr2 c))))

is-pullback-stable-function-class-Prop :
  {l1 l2 l3 : Level} (l : Level) (F : function-class l1 l2 l3) →
  Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ lsuc l)
pr1 (is-pullback-stable-function-class-Prop l F) =
  is-pullback-stable-function-class l F
pr2 (is-pullback-stable-function-class-Prop l F) =
  is-prop-is-pullback-stable-function-class l F
```
