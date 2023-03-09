# Local types

```agda
module orthogonal-factorization-systems.local-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-empty-type

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.empty-types
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.universe-levels
```

</details>

## Idea

A type family `A` over `X` is said to be _local at_ `f : Y → X`,
or _`f`-local_, if the precomposition map
`_∘ f : ((x : X) → A x) → ((y : Y) → A (f y))`
is an equivalence.

Likewise a type `A` is said to be `f`-local if the precomposition map
`_∘ f : (X → A) → (Y → A)`
is an equivalence.

## Definition

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-family : {l : Level} → (X → UU l) → UU (l1 ⊔ l2 ⊔ l)
  is-local-family A = is-equiv (precomp-Π f A)

  is-local-type : {l : Level} → UU l → UU (l1 ⊔ l2 ⊔ l)
  is-local-type A = is-local-family (λ _ → A)
```

## Properties

### Being local is a property

```agda
  is-property-is-local-family : {l : Level} (A : X → UU l) → is-prop (is-local-family A)
  is-property-is-local-family A = is-property-is-equiv (precomp-Π f A)

  is-local-family-Prop : {l : Level} → (X → UU l) → Prop (l1 ⊔ l2 ⊔ l)
  pr1 (is-local-family-Prop A) = is-local-family A
  pr2 (is-local-family-Prop A) = is-property-is-local-family A

  is-property-is-local-type : {l : Level} (A : UU l) → is-prop (is-local-type A)
  is-property-is-local-type A = is-property-is-equiv (precomp f A)

  is-local-type-Prop : {l : Level} → UU l → Prop (l1 ⊔ l2 ⊔ l)
  pr1 (is-local-type-Prop A) = is-local-type A
  pr2 (is-local-type-Prop A) = is-property-is-local-type A
```

### Locality distributes over Π-types

```agda
  map-distributive-Π-is-local-family :
    {l3 l4 : Level} {A : UU l3} (B : A → X → UU l4) →
    ((a : A) → is-local-family (B a)) → is-local-family (λ x → (a : A) → B a x)
  map-distributive-Π-is-local-family B f-loc =
    is-equiv-map-equiv
      ( equiv-swap-Π ∘e
        ( equiv-map-Π (λ a → precomp-Π f (B a) , (f-loc a)) ∘e
          equiv-swap-Π))
```

### If every type is `f`-local, then `f` is an equivalence

```agda
  is-equiv-is-local-type : ((l : Level) (A : UU l) → is-local-type A) → is-equiv f
  is-equiv-is-local-type = is-equiv-is-equiv-precomp f
```

### If the domain and codomain of ´f´ is ´f´-local then ´f´ is an equivalence

```agda
  retraction-sec-precomp-domain : sec (precomp f Y) → retr f
  pr1 (retraction-sec-precomp-domain sec-precomp-Y) = pr1 sec-precomp-Y id
  pr2 (retraction-sec-precomp-domain sec-precomp-Y) = htpy-eq (pr2 sec-precomp-Y id)
  section-is-local-domains' : sec (precomp f Y) → is-local-type X → sec f
  pr1 (section-is-local-domains' sec-precomp-Y is-local-X) = pr1 sec-precomp-Y id
  pr2 (section-is-local-domains' sec-precomp-Y is-local-X) =
    htpy-eq
      ( ap
        ( pr1)
        { pair
          ( f ∘ pr1 (section-is-local-domains' sec-precomp-Y is-local-X))
          ( ap (postcomp Y f) (pr2 sec-precomp-Y id))}
        { pair id refl}
        ( eq-is-contr (is-contr-map-is-equiv is-local-X f)))
  is-equiv-is-local-domains' : sec (precomp f Y) → is-local-type X → is-equiv f
  pr1 (is-equiv-is-local-domains' sec-precomp-Y is-local-X) =
    section-is-local-domains' sec-precomp-Y is-local-X
  pr2 (is-equiv-is-local-domains' sec-precomp-Y is-local-X) =
    retraction-sec-precomp-domain sec-precomp-Y
  is-equiv-is-local-domains : is-local-type Y → is-local-type X → is-equiv f
  is-equiv-is-local-domains is-local-Y = is-equiv-is-local-domains' (pr1 is-local-Y)
```

## Examples

### All type families are local at equivalences

```agda
  is-local-family-is-equiv :
    is-equiv f → {l : Level} (A : X → UU l) → is-local-family A
  is-local-family-is-equiv is-equiv-f = is-equiv-precomp-Π-is-equiv f is-equiv-f

  is-local-type-is-equiv :
    is-equiv f → {l : Level} (A : UU l) → is-local-type A
  is-local-type-is-equiv is-equiv-f = is-equiv-precomp-is-equiv f is-equiv-f
```

### Families of contractible types are local at any map

```agda
  is-local-family-is-contr :
    {l : Level} (A : X → UU l) →
    ((x : X) → is-contr (A x)) → is-local-family A
  is-local-family-is-contr A is-contr-A =
    is-equiv-is-contr
      ( precomp-Π f A)
      ( is-contr-Π is-contr-A)
      ( is-contr-Π (is-contr-A ∘ f))

  is-local-type-is-contr :
    {l : Level} (A : UU l) → is-contr A → is-local-type A
  is-local-type-is-contr A is-contr-A =
    is-local-family-is-contr (λ _ → A) (λ _ → is-contr-A)
```

### A type that is local at the unique map `empty → unit` is contractible.

```agda
is-contr-is-local-type :
  {l : Level} (A : UU l) → is-local-type (λ (_ : empty) → star) A → is-contr A
is-contr-is-local-type A is-local-type-A =
  is-contr-is-equiv
    ( empty → A)
    ( λ a _ → a)
    ( is-equiv-comp _ _
      ( is-equiv-map-inv-is-equiv (is-equiv-map-left-unit-law-Π λ _ → A))
      ( is-local-type-A))
    ( universal-property-empty' A)
```
