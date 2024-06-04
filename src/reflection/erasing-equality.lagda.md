# Erasing equality

```agda
module reflection.erasing-equality where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

Agda's builtin primitive `primEraseEquality` is a special construct on
[identifications](foundation-core.identity-types.md) that for every
identification `x ＝ y` gives another identification `x ＝ y` with the following
reduction behaviour:

- If the two end points of `p : x ＝ y` normalize to the same term,
  `primEraseEquality p` reduces to `refl`.

For example, `primEraseEquality` applied to the loop of the
[circle](synthetic-homotopy-theory.circle.md) will compute to `refl`, while
`primEraseEquality` applied to the nontrivial identification in the
[interval](synthetic-homotopy-theory.interval-type.md) will not reduce.

This primitive is useful for [rewrite rules](reflection.rewriting.md), as it
ensures that the identification used in defining the rewrite rule also computes
to `refl`. Concretely, if the identification `β` defines a rewrite rule, and `β`
is defined via `primEraseEqaulity`, then we have the strict equality `β ≐ refl`.

## Primitives

```agda
primitive
  primEraseEquality : {l : Level} {A : UU l} {x y : A} → x ＝ y → x ＝ y
```

## External links

- [Built-ins#Equality](https://agda.readthedocs.io/en/latest/language/built-ins.html#equality)
  at Agda's documentation pages
