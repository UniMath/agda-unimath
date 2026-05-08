# Library design principles

Understanding the design principles, structure, and philosophy behind the
agda-unimath library is essential for effectively navigating and contributing to
it. This document aims to provide a clear and concise introduction.

## Statement of purpose

Before stating the design principles of the agda-unimath library, it is
necessary to specify its purpose. This statement of the purpose provides the
boundary conditions by which we determine the design philosophy and structure of
the library. In other words, the remainder of the design philosophy is informed
by the stated purpose of this library.

1. To formalize an extensive curriculum of mathematical topics from a univalent
   point of view, in a human-enjoyable format. We hope to bring together a large
   community of enthusiasts of formalization and univalent mathematics.
2. To build a platform that facilitates research projects and student projects
   regarding formalization of univalent mathematics in Martin-Löf's dependent
   type theory extended with the univalence axiom and higher inductive types. A
   full description of the postulates in this library can be found
   [here](POSTULATES.md).
3. To break open new domains of application for the univalence axiom. For
   example, we have developed univalent theories of
   [combinatorics](univalent-combinatorics.md), [trees](trees.md),
   [species](species.md), ... TO DO: DESCRIBE A FULLER LIST
4. To develop a theory of library management that meets these stated goalds. For
   example, through our work we demonstrate the feasibility of a concept-central
   approach to library management and theorem-proving.

## Library structure

1. The source code of the formalization can be found in the folder `src`.
2. The library is organized by mathematical subject, with one folder per
   subject. For each folder, there is also an Agda file of the same name, which
   lists the files in that folder by importing them publicly.
3. The agda-unimath library aims to be an informative resource for formalized
   mathematics. We therefore formalize in literate Agda using markdown, treating
   files as pages of a mathematics wiki.
4. Each file is focused on a single topic, typically introducing one new concept
   and establishing its basic properties, or proving a central theorem and
   deriving immediate corollaries thereof.

## Design philosophy of agda-unimath

When a person is searching for something in a library of formalized mathematics,
they likely have a clear idea of the concept they are looking for. However, it
is unlikely that they know all the other concepts on which the desired concept
depends. Even if the concept they are seeking is an instance of something more
general, we cannot assume that they are aware of this. We certainly don't expect
users to have any knowledge of how their concept has been formalized in order to
find it in agda-unimath. In fact, users might have limited knowledge about the
concept they're searching for, knowing only its name, and they may be seeking
more information about it. In such cases, the ideal scenario is for them to
easily locate their concept in a hyperlinked index, similar to the index found
at the back of a book. This way, they can find the concept, click on it, and
access the information they were looking for.

Concepts are given prominence in the agda-unimath library because users know how
to search for them. An index of the formalized concepts in agda-unimath is
created by listing the files in the library, with the file names serving as the
indexing terms. To assist users in quickly finding the topics they are
interested in, each file in our library focuses narrowly on a single concept, a
named theorem, or a specific topic. The file names succinctly and naturally
describe the concept, theorem, or topic.

This organizational choice for the library allows us to structure our files in a
manner similar to pages on a wiki. The file's title represents the topic at
hand, and in an informal section, we can describe the main idea in words.
Subsequently, we provide the main definition, the basic infrastructure
surrounding it, and derive properties or consequences that hold with the same
generality as the main definition of the file.

For instance, the file about sets initially defines what a set is, and then
proceeds to demonstrate that sets are closed under equivalences, dependent pair
types, dependent product types, and so on. However, it does not prove that the
type of natural numbers is a set because users would more likely expect such
information to be presented on the page specifically dedicated to natural
numbers.

Let's consider a thought experiment. Suppose we have an unorganized library of
mathematics and organize everything by topic as described above. Mathematics is
already a well-organized subject, so this is our preferred way to organize most
of the library. However, towards the bottom of the library, we encounter a
cluster of interdependent files, and Agda will report errors due to these cyclic
dependencies. The reason is that our desire to organize the library by topic
does not account for the initial bootstrapping process at the foundational level
of the library.

To resolve these cyclic dependencies, we created two folders for the foundation
of the agda-unimath library: the `foundation-core` folder containing the basic
setup, and the `foundation` folder containing all the components belonging to
the library's foundation. The `foundation-core` folder contains files that are
paired with files of the same name in the `foundation` folder. The corresponding
file in the `foundation` folder publicly imports the file from the
`foundation-core` folder. Users working in areas outside of the foundation can
directly import files from the `foundation` folder without worrying about
potential file splits.

Outside of the `foundation` folder, the library adheres to the design principle
of "one-concept-per-file." However, if you discover that something you were
looking for is located in a different place than expected (which can happen!),
please let us know, and we will consider it for future improvements.
