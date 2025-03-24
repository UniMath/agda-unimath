# The universal reflexive globular type

```agda
{-# OPTIONS --guardedness #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module globular-types.universal-reflexive-globular-type
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.reflexive-globular-types funext univalence truncations
```

</details>

## Idea

The {{#concept "universal reflexive globular type"}} `𝒢 l` at
[universe level](foundation.universe-levels.md) is a translation from category
theory into type theory of the Hofmann–Streicher universe {{#cite Awodey22}} of
presheaves on the reflexive globular category `Γʳ`

```text
      s₀       s₁       s₂
    ----->   ----->   ----->
  0 <-r₀-- 1 <-r₁-- 2 <-r₂-- ⋯,
    ----->   ----->   ----->
      t₀       t₁       t₂
```

in which the _reflexive globular identities_

```text
  rs = id
  rt = id
  ss = ts
  tt = st
```

hold.

The Hofmann–Streicher universe of presheaves on a category `𝒞` is the presheaf
obtained by applying the functoriality of the right adjoint `ν : Cat → Psh 𝒞` of
the _category of elements functor_ `∫_𝒞 : Psh 𝒞 → Cat` to the universal discrete
fibration `π : Pointed-Type → Type`. More specifically, the Hofmann–Streicher
universe `(𝒰_𝒞 , El_𝒞)` is given by

```text
     𝒰_𝒞 I := Presheaf 𝒞/I
  El_𝒞 I A := A *,
```

where `*` is the terminal object of `𝒞/I`, i.e., the identity morphism on `I`.

We compute a few instances of the slice category `Γʳ/I`:

- The category Γʳ/0 is the category

  ```text
        s₀        s₁          s₂
      ----->    ----->      ----->
    1 <-r₀-- r₀ <-r₁-- r₀r₁ <-r₂-- ⋯.
      ----->    ----->      ----->
        t₀        t₁          t₂
  ```

  In other words, we have an isomorphism of categories `Γʳ/0 ≅ Γʳ`.

- The category Γʳ/1 is the category

  ```text
                                        ⋮
                                       r₁r₂
                                       ∧|∧
                                       |||
                                       |∨|
                                        r₁
                                       ∧|∧
             s₁          s₀            |||            s₀          s₁
           <-----      <-----      s₀  |∨|  t₀      ----->      ----->
  ⋯ s₀r₀r₁ --r₁-> s₀r₀ --r₀-> s₀ -----> 1 <----- t₀ <-r₀-- t₀r₀ <-r₁-- t₀r₀r₁ ⋯.
           <-----      <-----                       ----->      ----->
             t₁          t₀                           t₀          t₁
  ```

## Definitions

```agda
module _
  (l1 l2 : Level)
  where

  0-cell-universal-Reflexive-Globular-Type : UU (lsuc l1 ⊔ lsuc l2)
  0-cell-universal-Reflexive-Globular-Type =
    Reflexive-Globular-Type l1 l2
```

## See also

- [The universal directed graph](graph-theory.universal-directed-graph.md)
- [The universal globular type](globular-types.universal-globular-type.md)
- [The universal reflexive graph](graph-theory.universal-reflexive-graph.md)

## External links

- [Globular sets](https://ncatlab.org/nlab/show/globular+set) at the $n$Lab.

## References

{{#bibliography}}
