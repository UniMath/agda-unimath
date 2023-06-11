# Preidempotent maps

```agda
module foundation.preidempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

A **preidempotent map** is a map `f : A → A` equipped with a homotopy
`f ∘ f ~ f`.

## Definition

```agda
is-preidempotent : {l : Level} {A : UU l} → (A → A) → UU l
is-preidempotent f = (f ∘ f) ~ f

preidempotent-map : {l : Level} (A : UU l) → UU l
preidempotent-map A = Σ (A → A) is-preidempotent
```

## Properties

### Being preidempotent over a set is a property

```agda
is-prop-is-preidempotent-is-set :
  {l : Level} {A : UU l} → is-set A → (f : A → A) → is-prop (is-preidempotent f)
is-prop-is-preidempotent-is-set is-set-A f =
  is-prop-Π λ x → is-set-A (f (f x)) (f x)
```

## References

- Mike Shulman, _Idempotents in intensional type theory_, Logical Methods in
  Computer Science, Volume 12, Issue 3, 2017
  ([arXiv:1507.03634](https://arxiv.org/abs/1507.03634),
  [DOI:10.48550](https://doi.org/10.48550/arXiv.1507.03634))
- Mike Shulman, _Splitting Idempotents_,
  <https://homotopytypetheory.org/2014/12/08/splitting-idempotents/>
