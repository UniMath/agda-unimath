# Function classes

```agda
module orthogonal-factorization-systems.function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.pullback-squares
open import foundation.transport
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

A **function class** is a [subtype](foundation.subtypes.md) of the type of all
functions in a given universe.

## Definitions

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

### Having equivalences is equivalent to having identity maps

This is a consequence of [univalence](foundation.univalence.md).

```agda
module _
  {l1 l2 : Level} (F : function-class l1 l1 l2)
  where

  has-identity-maps-has-equivalences-function-class :
    has-equivalences-function-class F → has-identity-maps-function-class F
  has-identity-maps-has-equivalences-function-class has-equivs-F A =
    has-equivs-F A A id is-equiv-id

  htpy-has-identity-maps-function-class :
    has-identity-maps-function-class F →
    {X Y : UU l1} → (p : X ＝ Y) → type-Prop (F (map-eq p))
  htpy-has-identity-maps-function-class has-ids-F {X} refl = has-ids-F X

  has-equivalence-has-identity-maps-function-class :
    has-identity-maps-function-class F →
    {X Y : UU l1} (e : X ≃ Y) → type-Prop (F (map-equiv e))
  has-equivalence-has-identity-maps-function-class has-ids-F {X} {Y} e =
    tr
      ( type-Prop ∘ F)
      ( ap pr1 (is-section-eq-equiv e))
      ( htpy-has-identity-maps-function-class has-ids-F (eq-equiv X Y e))

  has-equivalences-has-identity-maps-function-class :
    has-identity-maps-function-class F → has-equivalences-function-class F
  has-equivalences-has-identity-maps-function-class has-ids-F A B f is-equiv-f =
    has-equivalence-has-identity-maps-function-class has-ids-F (f , is-equiv-f)

  is-equiv-has-identity-maps-has-equivalences-function-class :
    is-equiv has-identity-maps-has-equivalences-function-class
  is-equiv-has-identity-maps-has-equivalences-function-class =
    is-equiv-is-prop
      ( is-prop-has-equivalences-function-class F)
      ( is-prop-has-identity-maps-function-class F)
      ( has-equivalences-has-identity-maps-function-class)

  equiv-has-identity-maps-has-equivalences-function-class :
    has-equivalences-function-class F ≃ has-identity-maps-function-class F
  pr1 equiv-has-identity-maps-has-equivalences-function-class =
    has-identity-maps-has-equivalences-function-class
  pr2 equiv-has-identity-maps-has-equivalences-function-class =
    is-equiv-has-identity-maps-has-equivalences-function-class

  is-equiv-has-equivalences-has-identity-maps-function-class :
    is-equiv has-equivalences-has-identity-maps-function-class
  is-equiv-has-equivalences-has-identity-maps-function-class =
    is-equiv-is-prop
      ( is-prop-has-identity-maps-function-class F)
      ( is-prop-has-equivalences-function-class F)
      ( has-identity-maps-has-equivalences-function-class)

  equiv-has-equivalences-has-identity-maps-function-class :
    has-identity-maps-function-class F ≃ has-equivalences-function-class F
  pr1 equiv-has-equivalences-has-identity-maps-function-class =
    has-equivalences-has-identity-maps-function-class
  pr2 equiv-has-equivalences-has-identity-maps-function-class =
    is-equiv-has-equivalences-has-identity-maps-function-class
```
