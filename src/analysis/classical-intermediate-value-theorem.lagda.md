# The classical intermediate value theorem

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.classical-intermediate-value-theorem where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

The
{{#concept "classical intermediate value theorem" WDID=Q245098 WD="intermediate value theorem"}}
states that for a
[pointwise continuous function](real-numbers.pointwise-continuous-functions-real-numbers.md)
`f` from the [real numbers](real-numbers.dedekind-real-numbers.md) to
themselves, real numbers `a` and `b` with `a`
[less than or equal to](real-numbers.inequality-real-numbers.md) `b` such that
`f a` is [negative](real-numbers.negative-real-numbers.md) and `f b` is
[positive](real-numbers.positive-real-numbers.md), there exists a `c` with
`a ≤ c ≤ b` such that `f c` is zero.

$n$Lab states that this theorem is known to be invalid in constructive contexts.

This contrasts with the
[constructive intermediate value theorem](analysis.intermediate-value-theorem.md),
which states merely that for any
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
there exists a `c` with `a ≤ c ≤ b` with `|f c| ≤ ε`.

## Proof

This has yet to be proved.

## External links

- [Intermediate value theorem](https://ncatlab.org/nlab/show/intermediate+value+theorem)
  on $n$Lab
- [Intermediate value theorem](https://en.wikipedia.org/wiki/Intermediate_value_theorem)
  on Wikipedia
