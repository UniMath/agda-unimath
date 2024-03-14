# Crisp types

## Idea

A {{#concept "crisp type"}} is a type whose formation is done in a purely _crisp
context_. In Agda, we can assume a variable type `A` is crisp by writing
`@♭ A : UU`. Crisp types stand in contrast to {{#concept "cohesive types"}}
which are types that may be formed in arbitrary contexts.

**Note:** The notion of being a crisp type is quite different to that of being
[crisply flat discrete](modal-type-theory.flat-discrete-crisp-types.md).
Essentially, a crisply flat discrete type is a type whose _elements_ may be
assumed to be crisp. \[Remark 6.13, Shu15\]

## See also

- [The flat modality](modal-type-theory.flat-modality.md)

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))

## External links

- [Flat Modality](https://agda.readthedocs.io/en/latest/language/flat.html) on
  the Agda documentation pages.
- [spatial type theory](https://ncatlab.org/nlab/show/spatial+type+theory) at
  $n$Lab
