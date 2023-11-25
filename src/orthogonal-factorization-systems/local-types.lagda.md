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
open import foundation.dependent-universal-property-equivalences
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.sections
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-empty-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels
```

</details>

## Idea

A dependent type `A` over `X` is said to be **local at** `f : Y → X`, or
**`f`-local**, if the [precomposition map](foundation-core.function-types.md)

```text
  _∘ f : ((x : X) → A x) → ((y : Y) → A (f y))
```

is an [equivalence](foundation-core.equivalences.md).

We reserve the name `is-local` for when `A` does not vary over `X`, and specify
with `is-local-dependent-type` when it does.

## Definition

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type : {l : Level} → (X → UU l) → UU (l1 ⊔ l2 ⊔ l)
  is-local-dependent-type A = is-equiv (precomp-Π f A)

  is-local : {l : Level} → UU l → UU (l1 ⊔ l2 ⊔ l)
  is-local A = is-local-dependent-type (λ _ → A)
```

## Properties

### Being local is a property

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-property-is-local-dependent-type :
    {l : Level} (A : X → UU l) → is-prop (is-local-dependent-type f A)
  is-property-is-local-dependent-type A = is-property-is-equiv (precomp-Π f A)

  is-local-dependent-type-Prop :
    {l : Level} → (X → UU l) → Prop (l1 ⊔ l2 ⊔ l)
  pr1 (is-local-dependent-type-Prop A) = is-local-dependent-type f A
  pr2 (is-local-dependent-type-Prop A) = is-property-is-local-dependent-type A

  is-property-is-local :
    {l : Level} (A : UU l) → is-prop (is-local f A)
  is-property-is-local A = is-property-is-local-dependent-type (λ _ → A)

  is-local-Prop :
    {l : Level} → UU l → Prop (l1 ⊔ l2 ⊔ l)
  is-local-Prop A = is-local-dependent-type-Prop (λ _ → A)
```

### Being local distributes over Π-types

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  map-distributive-Π-is-local-dependent-type :
    {l3 l4 : Level} {A : UU l3} (B : A → X → UU l4) →
    ((a : A) → is-local-dependent-type f (B a)) →
    is-local-dependent-type f (λ x → (a : A) → B a x)
  map-distributive-Π-is-local-dependent-type B f-loc =
    is-equiv-map-equiv
      ( ( equiv-swap-Π) ∘e
        ( ( equiv-Π-equiv-family (λ a → precomp-Π f (B a) , (f-loc a))) ∘e
          ( equiv-swap-Π)))

  map-distributive-Π-is-local :
    {l3 l4 : Level} {A : UU l3} (B : A → UU l4) →
    ((a : A) → is-local f (B a)) →
    is-local f ((a : A) → B a)
  map-distributive-Π-is-local B =
    map-distributive-Π-is-local-dependent-type (λ a _ → B a)
```

### If every type is `f`-local, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-equiv-is-local :
    ({l : Level} (A : UU l) → is-local f A) → is-equiv f
  is-equiv-is-local = is-equiv-is-equiv-precomp f
```

### If the domain and codomain of `f` is `f`-local, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

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
    retraction-section-precomp-domain f section-precomp-Y

  is-equiv-is-local-domains : is-local f Y → is-local f X → is-equiv f
  is-equiv-is-local-domains is-local-Y =
    is-equiv-is-local-domains' (pr1 is-local-Y)
```

### Propositions are `f`-local if `_∘ f` has a converse

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type-is-prop :
    {l : Level} (A : X → UU l) →
    ((x : X) → is-prop (A x)) →
    (((y : Y) → A (f y)) → ((x : X) → A x)) →
    is-local-dependent-type f A
  is-local-dependent-type-is-prop A is-prop-A =
    is-equiv-is-prop
      (is-prop-Π is-prop-A)
      (is-prop-Π (is-prop-A ∘ f))

  is-local-is-prop :
    {l : Level} (A : UU l) →
    is-prop A → ((Y → A) → (X → A)) → is-local f A
  is-local-is-prop A is-prop-A =
    is-local-dependent-type-is-prop (λ _ → A) (λ _ → is-prop-A)
```

## Examples

### All type families are local at equivalences

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type-is-equiv :
    is-equiv f → {l : Level} (A : X → UU l) → is-local-dependent-type f A
  is-local-dependent-type-is-equiv is-equiv-f =
    is-equiv-precomp-Π-is-equiv is-equiv-f

  is-local-is-equiv :
    is-equiv f → {l : Level} (A : UU l) → is-local f A
  is-local-is-equiv is-equiv-f = is-equiv-precomp-is-equiv f is-equiv-f
```

### Families of contractible types are local at any map

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type-is-contr :
    {l : Level} (A : X → UU l) →
    ((x : X) → is-contr (A x)) → is-local-dependent-type f A
  is-local-dependent-type-is-contr A is-contr-A =
    is-equiv-is-contr
      ( precomp-Π f A)
      ( is-contr-Π is-contr-A)
      ( is-contr-Π (is-contr-A ∘ f))

  is-local-is-contr :
    {l : Level} (A : UU l) → is-contr A → is-local f A
  is-local-is-contr A is-contr-A =
    is-local-dependent-type-is-contr (λ _ → A) (λ _ → is-contr-A)
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

- [Local maps](orthogonal-factorization-systems.local-maps.md)
- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
