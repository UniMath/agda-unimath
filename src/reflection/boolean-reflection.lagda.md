# Boolean reflection

```agda
module reflection.boolean-reflection where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.decidable-types
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.identity-types
```

</details>

## Idea

The idea of boolean reflection is to use the equality checker of the proof
assistant in order to offload proof obligations to the computer. This works in
two steps. First, we construct the booleanization, which is a map
`is-decidable A → bool`, that sends elements of the form `inl a` to `true` and
elements of the form `inr na` to `false`. Then we construct the boolean
reflection function, which takes a decision `d : is-decidable A` and an
identification `Id (booleanization d) true` to an element of `A`. This allows us
to construct an element of `A` if it has elements, by
`boolean-reflection d refl`. Indeed, if `A` was nonempty, then the decision
`d : is-decidable A` must have been of the form `inl a` for some element `a`,
and that `refl` is indeed an identification `Id (booleanization d) true`.

## Definition

```agda
booleanization : {l : Level} {A : UU l} → is-decidable A → bool
booleanization (inl a) = true
booleanization (inr f) = false

inv-boolean-reflection :
  {l : Level} {A : UU l} (d : is-decidable A) → A → booleanization d ＝ true
inv-boolean-reflection (inl a) x = refl
inv-boolean-reflection (inr f) x = ex-falso (f x)

boolean-reflection :
  {l : Level} {A : UU l} (d : is-decidable A) → booleanization d ＝ true → A
boolean-reflection (inl a) p = a
boolean-reflection (inr f) p = ex-falso (Eq-eq-bool p)
```
