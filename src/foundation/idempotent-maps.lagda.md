# Idempotent maps

```agda
module foundation.idempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.universe-levels
```

</details>

## Idea

An **idempotent map** is a map `f : A → A` such that `f ∘ f ~ f`.

## Definition

```agda
is-idempotent : {l : Level} {A : UU l} → (A → A) → UU l
is-idempotent f = (f ∘ f) ~ f
```

## Properties

### Being idempotent over a set is a property

```agda
is-prop-is-idempotent-is-set :
  {l : Level} {A : UU l} → is-set A → (f : A → A) → is-prop (is-idempotent f)
is-prop-is-idempotent-is-set is-set-A f =
  is-prop-Π λ x → is-set-A (f (f x)) (f x)
```

## References

- Mike Shulman, _Splitting Idempotents_,
  <https://homotopytypetheory.org/2014/12/08/splitting-idempotents/>
