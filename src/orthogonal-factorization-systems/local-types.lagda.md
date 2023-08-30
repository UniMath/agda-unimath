# Local types

```agda
module orthogonal-factorization-systems.local-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universe-levels
```

</details>

## Idea

A type family `A` over `X` is said to be **local at** `f : Y → X`, or
**`f`-local**, if the [precomposition map](foundation-core.function-types.md)

```text
  _∘ f : ((x : X) → A x) → ((y : Y) → A (f y))
```

is an [equivalence](foundation-core.equivalences.md).

Likewise, a _type_ `A` is said to be **`f`-local** if the precomposition map
`_∘ f : (X → A) → (Y → A)` is an equivalence.

We reserve the name `is-local` for local types, and specify `is-local-Π` when
the type may vary over the base.

## Definition

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-Π : {l : Level} → (X → UU l) → UU (l1 ⊔ l2 ⊔ l)
  is-local-Π A = is-equiv (precomp-Π f A)

  is-local : {l : Level} → UU l → UU (l1 ⊔ l2 ⊔ l)
  is-local A = is-local-Π (λ _ → A)
```

## Properties

### Being local is a property

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-property-is-local-Π :
    {l : Level} (A : X → UU l) → is-prop (is-local-Π f A)
  is-property-is-local-Π A = is-property-is-equiv (precomp-Π f A)

  is-local-Π-Prop :
    {l : Level} → (X → UU l) → Prop (l1 ⊔ l2 ⊔ l)
  pr1 (is-local-Π-Prop A) = is-local-Π f A
  pr2 (is-local-Π-Prop A) = is-property-is-local-Π A

  is-property-is-local :
    {l : Level} (A : UU l) → is-prop (is-local f A)
  is-property-is-local A = is-property-is-local-Π (λ _ → A)

  is-local-Prop :
    {l : Level} → UU l → Prop (l1 ⊔ l2 ⊔ l)
  is-local-Prop A = is-local-Π-Prop (λ _ → A)
```

### Being local distributes over Π-types

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  map-distributive-Π-is-local-Π :
    {l3 l4 : Level} {A : UU l3} (B : A → X → UU l4) →
    ((a : A) → is-local-Π f (B a)) →
    is-local-Π f (λ x → (a : A) → B a x)
  map-distributive-Π-is-local-Π B f-loc =
    is-equiv-map-equiv
      ( equiv-swap-Π ∘e
        ( equiv-map-Π (λ a → precomp-Π f (B a) , (f-loc a)) ∘e
          equiv-swap-Π))
```

### Locality of dependent pair types

```agda
module _
  {l1 l2 l3 l4 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  {A : UU l3} {B : A → UU l4}
  (is-local-A : is-local f A)
  (is-local-B : ((x : A) → is-local f (B x)))
  where

  -- map-is-local-Σ : (Y → Σ A B) → X → Σ A B
  -- pr1 (map-is-local-Σ g x) = map-inv-is-equiv is-local-A (pr1 ∘ g) x
  -- pr2 (map-is-local-Σ g x) =
  --   map-inv-is-equiv (is-local-B (pr1 (map-is-local-Σ g x))) (λ y → {! pr2 (g ?)  !}) {!   !}

  -- is-local-Σ :
  --   is-local f A → ((x : A) → is-local f (B x)) → is-local f (Σ A B)
  -- is-local-Σ is-local-A is-local-B =
  --   is-equiv-htpy
  --     {!   !}
  --     {!   !}
  --     ( is-equiv-map-equiv-Π (λ _ → Σ A B) {!   !} {!   !})
```

### If every type is `f`-local, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-equiv-is-local :
    ((l : Level) (A : UU l) → is-local f A) → is-equiv f
  is-equiv-is-local = is-equiv-is-equiv-precomp f
```

### If the domain and codomain of `f` is `f`-local, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  retraction-section-precomp-domain : section (precomp f Y) → retraction f
  pr1 (retraction-section-precomp-domain section-precomp-Y) =
    pr1 section-precomp-Y id
  pr2 (retraction-section-precomp-domain section-precomp-Y) =
    htpy-eq (pr2 section-precomp-Y id)

  section-is-local-domains' : section (precomp f Y) → is-local f X → section f
  pr1 (section-is-local-domains' section-precomp-Y is-local-X) =
    pr1 section-precomp-Y id
  pr2 (section-is-local-domains' section-precomp-Y is-local-X) =
    htpy-eq
      ( ap
        ( pr1)
        { ( f ∘ pr1 (section-is-local-domains' section-precomp-Y is-local-X)) ,
          ( ap (postcomp Y f) (pr2 section-precomp-Y id))}
        { id , refl}
        ( eq-is-contr (is-contr-map-is-equiv is-local-X f)))

  is-equiv-is-local-domains' : section (precomp f Y) → is-local f X → is-equiv f
  pr1 (is-equiv-is-local-domains' section-precomp-Y is-local-X) =
    section-is-local-domains' section-precomp-Y is-local-X
  pr2 (is-equiv-is-local-domains' section-precomp-Y is-local-X) =
    retraction-section-precomp-domain section-precomp-Y

  is-equiv-is-local-domains : is-local f Y → is-local f X → is-equiv f
  is-equiv-is-local-domains is-local-Y =
    is-equiv-is-local-domains' (pr1 is-local-Y)
```

### Propositions are `f`-local if `_∘ f` has a converse

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-Π-is-prop :
    {l : Level} (A : X → UU l) →
    ((x : X) → is-prop (A x)) →
    (((y : Y) → A (f y)) → ((x : X) → A x)) →
    is-local-Π f A
  is-local-Π-is-prop A is-prop-A =
    is-equiv-is-prop
      (is-prop-Π is-prop-A)
      (is-prop-Π (is-prop-A ∘ f))

  is-local-is-prop :
    {l : Level} (A : UU l) →
    is-prop A → ((Y → A) → (X → A)) → is-local f A
  is-local-is-prop A is-prop-A =
    is-local-Π-is-prop (λ _ → A) (λ _ → is-prop-A)
```

## Examples

### All type families are local at equivalences

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-Π-is-equiv :
    is-equiv f → {l : Level} (A : X → UU l) → is-local-Π f A
  is-local-Π-is-equiv is-equiv-f = is-equiv-precomp-Π-is-equiv f is-equiv-f

  is-local-is-equiv :
    is-equiv f → {l : Level} (A : UU l) → is-local f A
  is-local-is-equiv is-equiv-f = is-equiv-precomp-is-equiv f is-equiv-f
```

### Families of contractible types are local at any map

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-Π-is-contr :
    {l : Level} (A : X → UU l) →
    ((x : X) → is-contr (A x)) → is-local-Π f A
  is-local-Π-is-contr A is-contr-A =
    is-equiv-is-contr
      ( precomp-Π f A)
      ( is-contr-Π is-contr-A)
      ( is-contr-Π (is-contr-A ∘ f))

  is-local-is-contr :
    {l : Level} (A : UU l) → is-contr A → is-local f A
  is-local-is-contr A is-contr-A =
    is-local-Π-is-contr (λ _ → A) (λ _ → is-contr-A)
```

### A type that is local at the unique map `empty → unit` is contractible

```agda
is-contr-is-local :
  {l : Level} (A : UU l) → is-local (λ (_ : empty) → star) A → is-contr A
is-contr-is-local A is-local-A =
  is-contr-is-equiv
    ( empty → A)
    ( λ a _ → a)
    ( is-equiv-comp
      ( λ a' _ → a' star)
      ( λ a _ →
        map-inv-is-equiv (is-equiv-map-left-unit-law-Π (λ _ → A)) a star)
      ( is-equiv-map-inv-is-equiv (is-equiv-map-left-unit-law-Π (λ _ → A)))
      ( is-local-A))
    ( universal-property-empty' A)
```

## See also

- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
