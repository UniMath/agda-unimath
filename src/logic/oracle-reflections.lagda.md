# Oracle reflections

```agda
module logic.oracle-reflections where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import orthogonal-factorization-systems.higher-modalities
open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

Given an _oracle_ `p`, i.e. a predicate `p : A → Prop`, and a type `X`, then the
{{#concept "oracle reflection" Agda=oracle-reflection}} of `X`, `𝒪ₚX`, is the
universal [proposition](foundation-core.propositions.md) equipped with
operations

1. `unit : X → 𝒪ₚX`
2. `ask : (a : A) → (p a → 𝒪ₚX) → 𝒪ₚX`.

Oracle reflections satisfy the _universal extension property_ that for any
family of propositions `Q : 𝒪ₚX → Prop`, to construct a section of `Q` it
suffices to construct it along the restrictions of `unit` and `ask`.

## Definitions

### Oracle algebras

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (X : UU l3)
  (𝒪ₚX@(𝒪ₚX' , H) : Prop l4)
  where

  oracle-algebra : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  oracle-algebra = (X → 𝒪ₚX') × ((a : A) → (type-Prop (p a) → 𝒪ₚX') → 𝒪ₚX')

  is-prop-oracle-algebra : is-prop oracle-algebra
  is-prop-oracle-algebra =
    is-prop-product
      ( is-prop-function-type H)
      ( is-prop-Π (λ _ → is-prop-function-type H))

  oracle-algebra-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  oracle-algebra-Prop = (oracle-algebra , is-prop-oracle-algebra)
```

### The dependent extension property of oracle reflections

This is a simplified form of the universal property that works because we're
mapping into propositions.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (l : Level)
  {A : UU l1} (p : A → Prop l2)
  (X : UU l3)
  (𝒪ₚX : Prop l4)
  (ηε@(unit , ask) : oracle-algebra p X 𝒪ₚX)
  where

  dependent-extension-property-oracle-reflection-Level :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  dependent-extension-property-oracle-reflection-Level =
    (Q : type-Prop 𝒪ₚX → Prop l) →
    ((x : X) → type-Prop (Q (unit x))) →
    ( (a : A) (f : type-Prop (p a) → type-Prop 𝒪ₚX) →
      ((u : type-Prop (p a)) → type-Prop (Q (f u))) →
      type-Prop (Q (ask a f))) →
    (y : type-Prop 𝒪ₚX) → type-Prop (Q y)

  is-prop-dependent-extension-property-oracle-reflection-Level :
    is-prop dependent-extension-property-oracle-reflection-Level
  is-prop-dependent-extension-property-oracle-reflection-Level =
    is-prop-Π
      ( λ Q →
        is-prop-Π
          ( λ _ →
            is-prop-Π
              ( λ _ →
                is-prop-Π (λ y → is-prop-type-Prop (Q y)))))

  dependent-extension-property-prop-oracle-reflection-Level :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  dependent-extension-property-prop-oracle-reflection-Level =
    ( dependent-extension-property-oracle-reflection-Level ,
      is-prop-dependent-extension-property-oracle-reflection-Level)
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (X : UU l3)
  (𝒪ₚX : Prop l4)
  (ηε : oracle-algebra p X 𝒪ₚX)
  where

  dependent-extension-property-oracle-reflection : UUω
  dependent-extension-property-oracle-reflection =
    {l : Level} →
    dependent-extension-property-oracle-reflection-Level l p X 𝒪ₚX ηε
```

### The extension property of oracle reflections

```agda
module _
  {l1 l2 l3 l4 : Level}
  (l : Level)
  {A : UU l1} (p : A → Prop l2)
  (let p' = type-Prop ∘ p)
  (X : UU l3)
  (𝒪ₚX : Prop l4)
  (ηε@(unit , ask) : oracle-algebra p X 𝒪ₚX)
  where

  extension-property-oracle-reflection-Level :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  extension-property-oracle-reflection-Level =
    (Q : Prop l) →
    (X → type-Prop Q) →
    ((a : A) (f : p' a → type-Prop 𝒪ₚX) → (p' a → type-Prop Q) → type-Prop Q) →
    type-Prop 𝒪ₚX → type-Prop Q

  is-prop-extension-property-oracle-reflection-Level :
    is-prop extension-property-oracle-reflection-Level
  is-prop-extension-property-oracle-reflection-Level =
    is-prop-Π
      ( λ Q →
        is-prop-Π
          ( λ _ →
            is-prop-Π
              ( λ _ →
                is-prop-function-type (is-prop-type-Prop Q))))

  extension-property-prop-oracle-reflection-Level :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  extension-property-prop-oracle-reflection-Level =
    ( extension-property-oracle-reflection-Level ,
      is-prop-extension-property-oracle-reflection-Level)
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (X : UU l3)
  (𝒪ₚX : Prop l4)
  (ηε : oracle-algebra p X 𝒪ₚX)
  where

  extension-property-oracle-reflection : UUω
  extension-property-oracle-reflection =
    {l : Level} → extension-property-oracle-reflection-Level l p X 𝒪ₚX ηε
```

### The predicate on a proposition of being an oracle reflection

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (X : UU l3)
  where

  is-oracle-reflection :
    (l : Level) (𝒪ₚX : Prop l4) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  is-oracle-reflection l 𝒪ₚX =
    Σ ( oracle-algebra p X 𝒪ₚX)
      ( dependent-extension-property-oracle-reflection-Level l p X 𝒪ₚX)

  is-prop-is-oracle-reflection :
    {l : Level} (𝒪ₚX : Prop l4) →
    is-prop (is-oracle-reflection l 𝒪ₚX)
  is-prop-is-oracle-reflection {l} 𝒪ₚX =
    is-prop-Σ
      ( is-prop-oracle-algebra p X 𝒪ₚX)
      ( is-prop-dependent-extension-property-oracle-reflection-Level l p X 𝒪ₚX)

  is-oracle-reflection-Prop :
    (l : Level) (𝒪ₚX : Prop l4) →
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  is-oracle-reflection-Prop l 𝒪ₚX =
    ( is-oracle-reflection l 𝒪ₚX ,
      is-prop-is-oracle-reflection 𝒪ₚX)
```

### The type of oracle reflections of a type

```agda
module _
  {l1 l2 l3 : Level}
  (l4 l5 : Level)
  {A : UU l1} (p : A → Prop l2)
  (X : UU l3)
  where

  oracle-reflection : UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5)
  oracle-reflection =
    Σ (Prop l4) (is-oracle-reflection p X l5)
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (p : A → Prop l2)
  {X : UU l3} (𝒪ₚX : oracle-reflection l4 l5 p X)
  where

  prop-oracle-reflection :
    Prop l4
  prop-oracle-reflection = pr1 𝒪ₚX

  oracle-algebra-oracle-reflection :
    oracle-algebra p X (prop-oracle-reflection)
  oracle-algebra-oracle-reflection = pr1 (pr2 𝒪ₚX)

  type-oracle-reflection : UU l4
  type-oracle-reflection =
    type-Prop prop-oracle-reflection

  is-prop-type-oracle-reflection :
    is-prop type-oracle-reflection
  is-prop-type-oracle-reflection =
    is-prop-type-Prop prop-oracle-reflection

  unit-oracle-reflection :
    X → type-oracle-reflection
  unit-oracle-reflection =
    pr1 oracle-algebra-oracle-reflection

  ask-oracle-reflection :
    (a : A) →
    (type-Prop (p a) → type-oracle-reflection) →
    type-oracle-reflection
  ask-oracle-reflection =
    pr2 oracle-algebra-oracle-reflection

  ind-oracle-reflection :
    dependent-extension-property-oracle-reflection-Level l5 p X
      ( prop-oracle-reflection)
      ( oracle-algebra-oracle-reflection)
  ind-oracle-reflection =
    pr2 (pr2 𝒪ₚX)

  rec-oracle-reflection :
    extension-property-oracle-reflection-Level l5 p X
      ( prop-oracle-reflection)
      ( oracle-algebra-oracle-reflection)
  rec-oracle-reflection Q =
    ind-oracle-reflection (λ _ → Q)
```

### The functorial action of oracle reflections

```agda
module _
  {l1 l2 l3 l4 l6 l7 : Level}
  {A : UU l1} (p : A → Prop l2)
  {X : UU l3}
  where

  map-oracle-reflection :
    (l5 : Level) →
    (R : oracle-reflection l4 (l5 ⊔ l6) p X)
    (R' : oracle-reflection l6 l7 p X) →
    type-oracle-reflection p R → type-oracle-reflection p R'
  map-oracle-reflection l5 R R' =
    map-inv-raise ∘
    ind-oracle-reflection p R
      ( λ _ → raise-Prop l5 (prop-oracle-reflection p R'))
      ( map-raise ∘ unit-oracle-reflection p R')
      ( λ a _ f* →
        map-raise (ask-oracle-reflection p R' a (map-inv-raise ∘ f*)))
```

## Properties

### Oracle reflections are unique

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (p : A → Prop l2)
  (X : UU l3)
  where

  eq-prop-oracle-reflection :
    {l5 : Level} →
    (R R' : oracle-reflection l4 (l4 ⊔ l5) p X) →
    prop-oracle-reflection p R ＝ prop-oracle-reflection p R'
  eq-prop-oracle-reflection {l5} R R' =
    eq-iff
      ( map-oracle-reflection p l5 R R')
      ( map-oracle-reflection p l5 R' R)

  is-prop-oracle-reflection :
    (l5 : Level) → is-prop (oracle-reflection l4 (l4 ⊔ l5) p X)
  is-prop-oracle-reflection l5 =
    is-prop-all-elements-equal
      ( λ R R' →
        eq-pair-Σ
          ( eq-prop-oracle-reflection {l5} R R')
          ( eq-is-prop
            ( is-prop-is-oracle-reflection p X (prop-oracle-reflection p R'))))

  oracle-reflection-Prop :
    (l5 : Level) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5)
  oracle-reflection-Prop l5 =
    ( oracle-reflection l4 (l4 ⊔ l5) p X , is-prop-oracle-reflection l5)
```

### Lowering universe levels for the extension property of oracle reflections

```agda
module _
  {l1 l2 l3 l4 : Level} (l5 l6 : Level)
  {A : UU l1} (p : A → Prop l2)
  {X : UU l3}
  (R : oracle-reflection l4 (l5 ⊔ l6) p X)
  where

  ind-lower-oracle-reflection :
    dependent-extension-property-oracle-reflection-Level l5 p X
      ( prop-oracle-reflection p R)
      ( oracle-algebra-oracle-reflection p R)
  ind-lower-oracle-reflection Q unit ask =
    map-inv-raise ∘
    ind-oracle-reflection p R
      ( raise-Prop l6 ∘ Q)
      ( map-raise ∘ unit)
      ( λ a f f* → map-raise (ask a f (map-inv-raise ∘ f*)))

  rec-lower-oracle-reflection :
    extension-property-oracle-reflection-Level l5 p X
      ( prop-oracle-reflection p R)
      ( oracle-algebra-oracle-reflection p R)
  rec-lower-oracle-reflection Q =
    ind-lower-oracle-reflection (λ _ → Q)
```
